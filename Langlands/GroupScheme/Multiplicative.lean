import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.TorsionBaseChange
import Langlands.AbelianScheme.Tate.Twist
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.Limits

/-! # The multiplicative group scheme and its roots-of-unity kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u

namespace Gm

/-! ### Laurent polynomials and units -/

/-- The integral Laurent polynomial ring `ℤ[t, t⁻¹]`, with coefficients lifted to universe `u`. -/
abbrev laurentRing : CommRingCat.{u} := CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ))

/-- The coordinate `t` as a unit of `ℤ[t, t⁻¹]`. -/
def coordUnit : (LaurentPolynomial (ULift.{u} ℤ))ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp [LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add]; simp [LaurentPolynomial.T_zero]

lemma coordUnit_zpow_val (m : ℤ) :
    ((coordUnit.{u} ^ m : (LaurentPolynomial (ULift.{u} ℤ))ˣ) :
      LaurentPolynomial (ULift.{u} ℤ)) = LaurentPolynomial.T m := by
  induction m using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ m ih =>
    rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]
    rfl
  | pred m ih =>
    rw [zpow_sub_one, Units.val_mul, ih, LaurentPolynomial.T_sub]
    rfl

/-- Ring maps out of `ℤ[t, t⁻¹]` are exactly units: a map corresponds to the image of `t`. -/
def laurentHomEquiv (A : Type u) [CommRing A] :
    (LaurentPolynomial (ULift.{u} ℤ) →+* A) ≃ Aˣ where
  toFun φ := Units.map φ.toMonoidHom coordUnit
  invFun a := LaurentPolynomial.eval₂ ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) a
  left_inv φ := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C r) = φ (LaurentPolynomial.C r)
      rw [LaurentPolynomial.eval₂_C]
      have h : ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) =
          φ.comp LaurentPolynomial.C := by
        apply RingHom.ext
        intro s
        have hs : s = ((s.down : ℤ) : ULift.{u} ℤ) := by ext; simp
        rw [hs, map_intCast, map_intCast]
      exact RingHom.congr_fun h r
    · intro m
      change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T m) = φ (LaurentPolynomial.T m)
      rw [LaurentPolynomial.eval₂_T, ← coordUnit_zpow_val, ← map_zpow]
      rfl
  right_inv a := by
    apply Units.ext
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = (a : A)
    rw [LaurentPolynomial.eval₂_T, zpow_one]

@[simp]
lemma laurentHomEquiv_val (A : Type u) [CommRing A] (φ : LaurentPolynomial (ULift.{u} ℤ) →+* A) :
    (laurentHomEquiv A φ : A) = φ (LaurentPolynomial.T 1) := rfl

lemma laurentHomEquiv_comp {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (φ : LaurentPolynomial (ULift.{u} ℤ) →+* A) :
    laurentHomEquiv B (f.comp φ) = Units.map f.toMonoidHom (laurentHomEquiv A φ) := rfl

/-! ### Morphisms to `Spec ℤ[t, t⁻¹]` -/

/-- Morphisms into an affine scheme `Spec R` are ring maps `R ⟶ Γ(X, ⊤)`. -/
def specHomEquiv (X : Scheme.{u}) (R : CommRingCat.{u}) : (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) where
  toFun f := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  invFun φ := X.toSpecΓ ≫ Spec.map φ
  left_inv f := by
    simp only [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  right_inv φ := by
    simp [Scheme.ΓSpecIso_naturality]

lemma specHomEquiv_comp {X Y : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec R) :
    specHomEquiv X R (g ≫ f) = specHomEquiv Y R f ≫ g.appTop := rfl

/-- Morphisms `X ⟶ Spec ℤ[t, t⁻¹]` are global units of `X`, via the image of `t`. -/
def unitsHomEquiv (X : Scheme.{u}) : (X ⟶ Spec laurentRing.{u}) ≃ (Γ(X, ⊤))ˣ :=
  (specHomEquiv X laurentRing).trans
    (ConcreteCategory.homEquiv.trans (laurentHomEquiv _))

@[simp]
lemma unitsHomEquiv_val (X : Scheme.{u}) (f : X ⟶ Spec laurentRing.{u}) :
    (unitsHomEquiv X f : Γ(X, ⊤)) =
      f.appTop ((Scheme.ΓSpecIso laurentRing).inv (LaurentPolynomial.T 1)) := rfl

lemma unitsHomEquiv_comp {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec laurentRing.{u}) :
    unitsHomEquiv X (g ≫ f) = Units.map g.appTop.hom.toMonoidHom (unitsHomEquiv Y f) := rfl

/-! ### The representing scheme over an arbitrary base -/

/-- The unique morphism from `S` to `Spec ℤ`. -/
def toSpecZ (S : Scheme.{u}) : S ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.from S

/-- `Spec ℤ[t, t⁻¹]` as a scheme over `Spec ℤ`. -/
def overSpecZ : Over (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))

/-- The base change `Spec ℤ[t, t⁻¹] ×_{Spec ℤ} S` of `Spec ℤ[t, t⁻¹]` to `S`. -/
def scheme (S : Scheme.{u}) : Over S :=
  (Over.pullback (toSpecZ S)).obj overSpecZ

/-- `S`-morphisms into the base change are morphisms of schemes into `Spec ℤ[t, t⁻¹]`. -/
def schemeHomEquiv {S : Scheme.{u}} (T : Over S) :
    (T ⟶ scheme S) ≃ (T.left ⟶ Spec laurentRing.{u}) where
  toFun x := x.left ≫ pullback.fst _ _
  invFun f := Over.homMk (pullback.lift f T.hom (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simp only [pullback.lift_snd, Over.homMk_left]
      exact (Over.w x).symm
  right_inv f := pullback.lift_fst _ _ _

/-- `S`-morphisms into the base change of `Spec ℤ[t, t⁻¹]` are global units of the source. -/
def homEquiv {S : Scheme.{u}} (T : Over S) : (T ⟶ scheme S) ≃ (Γ(T.left, ⊤))ˣ :=
  (schemeHomEquiv T).trans (unitsHomEquiv T.left)

lemma homEquiv_apply {S : Scheme.{u}} (T : Over S) (x : T ⟶ scheme S) :
    homEquiv T x = unitsHomEquiv T.left (x.left ≫ pullback.fst _ _) := rfl

lemma homEquiv_comp {S : Scheme.{u}} {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ scheme S) :
    homEquiv T' (a ≫ x) = Units.map a.left.appTop.hom.toMonoidHom (homEquiv T x) := by
  rw [homEquiv_apply, homEquiv_apply, ← unitsHomEquiv_comp, Over.comp_left, Category.assoc]

/-! ### The units presheaf -/

/-- The presheaf of global units `T ↦ Γ(T, 𝒪_T)ˣ` on schemes over `S`. -/
@[simps]
def unitsFunctor (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (Γ(T.unop.left, ⊤))ˣ
  map a := CommGrpCat.ofHom (Units.map a.unop.left.appTop.hom.toMonoidHom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The units presheaf is represented by the base change of `Spec ℤ[t, t⁻¹]`. -/
def representableBy (S : Scheme.{u}) :
    (unitsFunctor S ⋙ forget CommGrpCat).RepresentableBy (scheme S) where
  homEquiv := homEquiv _
  homEquiv_comp a x := homEquiv_comp a x

end Gm

/-- The multiplicative group scheme `𝔾_{m,S}`: the base change of `Spec ℤ[t, t⁻¹]` to `S`,
with the group law representing multiplication of global units. -/
def Gm (S : Scheme.{u}) : CommGroupScheme S :=
  letI := CommGrpObj.ofRepresentableBy (Gm.scheme S) (Gm.unitsFunctor S) (Gm.representableBy S)
  { X := Gm.scheme S }

namespace Gm

variable (S : Scheme.{u})

/-- The group-valued points of `𝔾_{m,S}` are the units presheaf. -/
def pointsIso : GroupScheme.points (Gm S).toGrp ≅ unitsFunctor S ⋙ forget₂ CommGrpCat GrpCat :=
  yonedaGrpObjIsoOfRepresentableBy (Gm.scheme S) (unitsFunctor S ⋙ forget₂ CommGrpCat GrpCat)
    (representableBy S)

/-- The `T`-points of `𝔾_{m,S}` are the global units of `T`, as groups. -/
def pointsEquiv (T : Over S) : (T ⟶ (Gm S).X) ≃* (Γ(T.left, ⊤))ˣ :=
  ((pointsIso S).app (op T)).groupIsoToMulEquiv

lemma pointsEquiv_apply (T : Over S) (x : T ⟶ (Gm S).X) :
    pointsEquiv S T x = homEquiv T x := rfl

/-- The unit attached to a point is the pullback of the coordinate `t`. -/
lemma pointsEquiv_val (T : Over S) (x : T ⟶ (Gm S).X) :
    (pointsEquiv S T x : Γ(T.left, ⊤)) =
      (x.left ≫ pullback.fst _ _).appTop
        ((Scheme.ΓSpecIso laurentRing).inv (LaurentPolynomial.T 1)) := rfl

/-- The group law of `𝔾_{m,S}` is multiplication of units. -/
@[simp]
lemma pointsEquiv_mul (T : Over S) (x y : T ⟶ (Gm S).X) :
    pointsEquiv S T (x * y) = pointsEquiv S T x * pointsEquiv S T y :=
  map_mul _ _ _

/-- The points identification is natural in the test scheme. -/
lemma pointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (Gm S).X) :
    pointsEquiv S T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (pointsEquiv S T x) :=
  homEquiv_comp a x

/-- The multiplication morphism of `𝔾_{m,S}` multiplies the two coordinates. -/
lemma pointsEquiv_μ :
    pointsEquiv S ((Gm S).X ⊗ (Gm S).X) μ[(Gm S).X] =
      pointsEquiv S _ (CartesianMonoidalCategory.fst (Gm S).X (Gm S).X) *
        pointsEquiv S _ (CartesianMonoidalCategory.snd (Gm S).X (Gm S).X) := by
  rw [← pointsEquiv_mul, CategoryTheory.Hom.mul_def, CartesianMonoidalCategory.lift_fst_snd,
    Category.id_comp]

end Gm

/-! ### Group-scheme morphisms from natural maps of points -/

section Yoneda

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- A natural family of homomorphisms between groups of points, as a morphism of presheaves. -/
def pointsNatTrans (φ : ∀ T : Over S, (T ⟶ G.X) →* (T ⟶ H.X))
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), φ T' (a ≫ x) = a ≫ φ T x) :
    yonedaGrp.obj G ⟶ yonedaGrp.obj H where
  app T := GrpCat.ofHom (φ T.unop)
  naturality _ _ a := by
    ext x
    exact hφ a.unop x

/-- The group-scheme homomorphism inducing a natural family of homomorphisms of points. -/
def homOfPoints (φ : ∀ T : Over S, (T ⟶ G.X) →* (T ⟶ H.X))
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), φ T' (a ≫ x) = a ≫ φ T x) :
    G ⟶ H :=
  yonedaGrpFullyFaithful.preimage (pointsNatTrans φ hφ)

@[simp]
lemma comp_homOfPoints (φ : ∀ T : Over S, (T ⟶ G.X) →* (T ⟶ H.X))
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), φ T' (a ≫ x) = a ≫ φ T x)
    (T : Over S) (x : T ⟶ G.X) :
    x ≫ (homOfPoints φ hφ).hom.hom = φ T x :=
  congrArg (fun α => (α.app (op T)).hom x)
    (yonedaGrpFullyFaithful.map_preimage (pointsNatTrans φ hφ))

/-- Homomorphisms of group schemes agree when they agree on all points. -/
lemma hom_ext_points {f g : G ⟶ H}
    (h : ∀ (T : Over S) (x : T ⟶ G.X), x ≫ f.hom.hom = x ≫ g.hom.hom) : f = g := by
  apply Grp.hom_ext
  simpa using h G.X (𝟙 G.X)

lemma isoOfPoints_symm_naturality (e : ∀ T : Over S, (T ⟶ G.X) ≃* (T ⟶ H.X))
    (he : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), e T' (a ≫ x) = a ≫ e T x)
    {T T' : Over S} (a : T' ⟶ T) (y : T ⟶ H.X) :
    (e T').symm (a ≫ y) = a ≫ (e T).symm y := by
  apply (e T').injective
  simp [he]

/-- A natural family of multiplicative equivalences of points comes from an isomorphism. -/
def isoOfPoints (e : ∀ T : Over S, (T ⟶ G.X) ≃* (T ⟶ H.X))
    (he : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), e T' (a ≫ x) = a ≫ e T x) :
    G ≅ H where
  hom := homOfPoints (fun T => (e T).toMonoidHom) he
  inv := homOfPoints (fun T => (e T).symm.toMonoidHom) (isoOfPoints_symm_naturality e he)
  hom_inv_id := hom_ext_points (fun T x => by
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_homOfPoints, comp_homOfPoints]
    simp)
  inv_hom_id := hom_ext_points (fun T x => by
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_homOfPoints, comp_homOfPoints]
    simp)

@[simp]
lemma comp_isoOfPoints_hom (e : ∀ T : Over S, (T ⟶ G.X) ≃* (T ⟶ H.X))
    (he : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), e T' (a ≫ x) = a ≫ e T x)
    (T : Over S) (x : T ⟶ G.X) :
    x ≫ (isoOfPoints e he).hom.hom.hom = e T x :=
  comp_homOfPoints _ he T x

@[simp]
lemma comp_isoOfPoints_inv (e : ∀ T : Over S, (T ⟶ G.X) ≃* (T ⟶ H.X))
    (he : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X), e T' (a ≫ x) = a ≫ e T x)
    (T : Over S) (y : T ⟶ H.X) :
    y ≫ (isoOfPoints e he).inv.hom.hom = (e T).symm y :=
  comp_homOfPoints _ (isoOfPoints_symm_naturality e he) T y

end Yoneda

/-! ### Roots of unity -/

/-- The group scheme `μ_{n,S}` of `n`-th roots of unity: the kernel of the `n`-th power
endomorphism of `𝔾_{m,S}`. -/
abbrev mu (S : Scheme.{u}) (n : ℕ) : CommGroupScheme S where
  toGrp := torsion (Gm S).toGrp n

namespace mu

variable (S : Scheme.{u}) (n : ℕ)

lemma toGrp_eq : (mu S n).toGrp = torsion (Gm S).toGrp n := rfl

/-- The inclusion `μ_{n,S} ⟶ 𝔾_{m,S}`, as a homomorphism of commutative group schemes. -/
def incl : mu S n ⟶ Gm S := Additive.ofMul (torsionι (Gm S).toGrp n)

lemma groupHom_incl : CommGroupScheme.groupHom (incl S n) = torsionι (Gm S).toGrp n := rfl

/-- The `n`-torsion points of `𝔾_{m,S}` are the `n`-th roots of unity. -/
def torsionPointsUnitsEquiv (T : Over S) :
    torsionPoints (Gm S).toGrp n T ≃* rootsOfUnity n Γ(T.left, ⊤) where
  toFun x := ⟨Gm.pointsEquiv S T x.val, by
    rw [mem_rootsOfUnity, ← map_pow, ← zpow_natCast,
      (mem_torsionPoints _ _ _ _).mp x.property, map_one]⟩
  invFun ζ := ⟨(Gm.pointsEquiv S T).symm ζ, by
    rw [mem_torsionPoints, zpow_natCast, ← map_pow, (mem_rootsOfUnity n _).mp ζ.property,
      map_one]⟩
  left_inv x := Subtype.ext ((Gm.pointsEquiv S T).symm_apply_apply x.val)
  right_inv ζ := Subtype.ext ((Gm.pointsEquiv S T).apply_symm_apply ζ.val)
  map_mul' x y := Subtype.ext (map_mul (Gm.pointsEquiv S T) x.val y.val)

/-- The `T`-points of `μ_{n,S}` are the `n`-th roots of unity in `Γ(T, 𝒪_T)`. -/
def pointsEquiv (T : Over S) : (T ⟶ (mu S n).X) ≃* rootsOfUnity n Γ(T.left, ⊤) :=
  (GroupScheme.torsionPointsEquiv (Gm S).toGrp n T).trans (torsionPointsUnitsEquiv S n T)

/-- Under the points identifications, the inclusion `μ_n ⟶ 𝔾_m` is the inclusion of roots of
unity into units. -/
@[simp]
lemma pointsEquiv_val (T : Over S) (x : T ⟶ (mu S n).X) :
    (pointsEquiv S n T x : (Γ(T.left, ⊤))ˣ) =
      Gm.pointsEquiv S T (x ≫ (torsionι (Gm S).toGrp n).hom.hom) := rfl

lemma pointsEquiv_symm_comp_ι (T : Over S) (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    (pointsEquiv S n T).symm ζ ≫ (torsionι (Gm S).toGrp n).hom.hom =
      (Gm.pointsEquiv S T).symm ζ := by
  apply (Gm.pointsEquiv S T).injective
  rw [← pointsEquiv_val, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The points identification is natural in the test scheme. -/
lemma pointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (mu S n).X) :
    pointsEquiv S n T' (a ≫ x) =
      restrictRootsOfUnity a.left.appTop.hom n (pointsEquiv S n T x) := by
  apply Subtype.ext
  change Gm.pointsEquiv S T' ((a ≫ x) ≫ _) = Units.map _ (Gm.pointsEquiv S T (x ≫ _))
  rw [Category.assoc, Gm.pointsEquiv_naturality]
  rfl

end mu

/-! ### Affine test schemes -/

namespace Gm

variable {S : Scheme.{u}}

/-- The `S`-morphism `Spec R' ⟶ Spec R` induced by a ring homomorphism `φ : R ⟶ R'`. -/
abbrev affineMap {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : Spec R ⟶ S) :
    Over.mk (Spec.map φ ≫ f) ⟶ Over.mk f :=
  Over.homMk (Spec.map φ) rfl

/-- The points of `𝔾_{m,S}` over an affine test scheme `Spec R ⟶ S` are the units of `R`. -/
def affinePointsEquiv {R : CommRingCat.{u}} (f : Spec R ⟶ S) :
    (Over.mk f ⟶ (Gm S).X) ≃* Rˣ :=
  (pointsEquiv S (Over.mk f)).trans
    (Units.mapEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv)

lemma affinePointsEquiv_val {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (x : Over.mk f ⟶ (Gm S).X) :
    (affinePointsEquiv f x : R) =
      (Scheme.ΓSpecIso R).hom (pointsEquiv S (Over.mk f) x).val := rfl

/-- The affine points identification is compatible with ring homomorphisms. -/
lemma affinePointsEquiv_naturality {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : Spec R ⟶ S)
    (x : Over.mk f ⟶ (Gm S).X) :
    affinePointsEquiv (Spec.map φ ≫ f) (affineMap φ f ≫ x) =
      Units.map φ.hom.toMonoidHom (affinePointsEquiv f x) := by
  apply Units.ext
  rw [affinePointsEquiv_val, pointsEquiv_naturality]
  change ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso R').hom) _ =
    φ ((Scheme.ΓSpecIso R).hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

end Gm

namespace mu

variable {S : Scheme.{u}} (n : ℕ)

/-- The points of `μ_{n,S}` over an affine test scheme `Spec R ⟶ S` are the `n`-th roots of
unity in `R`. -/
def affinePointsEquiv {R : CommRingCat.{u}} (f : Spec R ⟶ S) :
    (Over.mk f ⟶ (mu S n).X) ≃* rootsOfUnity n R :=
  (pointsEquiv S n (Over.mk f)).trans
    (MulEquiv.restrictRootsOfUnity (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv n)

/-- Over an affine test scheme, the inclusion `μ_n ⟶ 𝔾_m` is the inclusion of roots of unity
into units. -/
lemma affinePointsEquiv_val {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (x : Over.mk f ⟶ (mu S n).X) :
    (affinePointsEquiv n f x : Rˣ) =
      Gm.affinePointsEquiv f (x ≫ (torsionι (Gm S).toGrp n).hom.hom) := rfl

/-- The affine roots-of-unity identification is compatible with ring homomorphisms. -/
lemma affinePointsEquiv_naturality {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : Spec R ⟶ S)
    (x : Over.mk f ⟶ (mu S n).X) :
    affinePointsEquiv n (Spec.map φ ≫ f) (Gm.affineMap φ f ≫ x) =
      restrictRootsOfUnity φ.hom n (affinePointsEquiv n f x) := by
  apply Subtype.ext
  rw [affinePointsEquiv_val, Category.assoc, Gm.affinePointsEquiv_naturality]
  rfl

/-- The `T`-points of `μ_{n,S}`, written additively, are the Tate-twist level
`TateTwist.Level Γ(T, 𝒪_T) n`. -/
def pointsLevelEquiv (T : Over S) :
    Additive (T ⟶ (mu S n).X) ≃+ TateTwist.Level Γ(T.left, ⊤) n :=
  (pointsEquiv S n T).toAdditive

lemma toUnit_pointsLevelEquiv (T : Over S) (x : Additive (T ⟶ (mu S n).X)) :
    TateTwist.toUnit Γ(T.left, ⊤) n (pointsLevelEquiv n T x) =
      Additive.ofMul (Gm.pointsEquiv S T (x.toMul ≫ (torsionι (Gm S).toGrp n).hom.hom)) := rfl

/-- The points of `μ_{n,S}` over an affine test scheme `Spec R ⟶ S`, written additively, are
the Tate-twist level `TateTwist.Level R n`. -/
def levelEquiv {R : CommRingCat.{u}} (f : Spec R ⟶ S) :
    Additive (Over.mk f ⟶ (mu S n).X) ≃+ TateTwist.Level R n :=
  (affinePointsEquiv n f).toAdditive

lemma toUnit_levelEquiv {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (x : Additive (Over.mk f ⟶ (mu S n).X)) :
    TateTwist.toUnit R n (levelEquiv n f x) =
      Additive.ofMul (Gm.affinePointsEquiv f (x.toMul ≫ (torsionι (Gm S).toGrp n).hom.hom)) :=
  rfl

end mu

/-! ### Transition maps between roots of unity -/

/-- For `n ∣ m`, the homomorphism `ζ ↦ ζ ^ (m / n)` from `m`-th to `n`-th roots of unity; it is
the multiplicative form of `TateTwist.transition`. -/
def rootsTransition (A : Type u) [CommRing A] {n m : ℕ} (h : n ∣ m) :
    rootsOfUnity m A →* rootsOfUnity n A :=
  MonoidHom.toAdditive.symm (TateTwist.transition A h)

@[simp]
lemma rootsTransition_val (A : Type u) [CommRing A] {n m : ℕ} (h : n ∣ m)
    (ζ : rootsOfUnity m A) :
    (rootsTransition A h ζ : Aˣ) = (ζ : Aˣ) ^ (m / n) := rfl

lemma toAdditive_rootsTransition (A : Type u) [CommRing A] {n m : ℕ} (h : n ∣ m) :
    MonoidHom.toAdditive (rootsTransition A h) = TateTwist.transition A h := rfl

lemma rootsTransition_restrict {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    {n m : ℕ} (h : n ∣ m) (ζ : rootsOfUnity m A) :
    rootsTransition B h (restrictRootsOfUnity g m ζ) =
      restrictRootsOfUnity g n (rootsTransition A h ζ) := by
  apply Subtype.ext
  change Units.map (g : A →* B) (ζ : Aˣ) ^ (m / n) = Units.map (g : A →* B) ((ζ : Aˣ) ^ (m / n))
  rw [map_pow]

namespace mu

variable (S : Scheme.{u})

lemma transition_naturality {n m : ℕ} (h : n ∣ m) {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ (mu S m).X) :
    (pointsEquiv S n T').symm (rootsTransition Γ(T'.left, ⊤) h (pointsEquiv S m T' (a ≫ x))) =
      a ≫ (pointsEquiv S n T).symm (rootsTransition Γ(T.left, ⊤) h (pointsEquiv S m T x)) := by
  apply (pointsEquiv S n _).injective
  rw [MulEquiv.apply_symm_apply, pointsEquiv_naturality, pointsEquiv_naturality,
    MulEquiv.apply_symm_apply, rootsTransition_restrict]

/-- For `n ∣ m`, the homomorphism `μ_{m,S} ⟶ μ_{n,S}` given on points by `ζ ↦ ζ ^ (m / n)`. -/
def transition {n m : ℕ} (h : n ∣ m) : mu S m ⟶ mu S n :=
  Additive.ofMul (homOfPoints
    (fun T => (pointsEquiv S n T).symm.toMonoidHom.comp
      ((rootsTransition Γ(T.left, ⊤) h).comp (pointsEquiv S m T).toMonoidHom))
    (transition_naturality S h))

/-- On points, the transition `μ_m ⟶ μ_n` is the power map `ζ ↦ ζ ^ (m / n)`. -/
lemma pointsEquiv_transition {n m : ℕ} (h : n ∣ m) (T : Over S) (x : T ⟶ (mu S m).X) :
    pointsEquiv S n T (x ≫ (CommGroupScheme.groupHom (transition S h)).hom.hom) =
      rootsTransition Γ(T.left, ⊤) h (pointsEquiv S m T x) := by
  have key : x ≫ (CommGroupScheme.groupHom (transition S h)).hom.hom = _ :=
    comp_homOfPoints _ (transition_naturality S h) T x
  rw [key]
  simp

/-- Under the level identifications, the transition `μ_m ⟶ μ_n` is `TateTwist.transition`. -/
lemma pointsLevelEquiv_transition {n m : ℕ} (h : n ∣ m) (T : Over S) (x : T ⟶ (mu S m).X) :
    pointsLevelEquiv n T
        (Additive.ofMul (x ≫ (CommGroupScheme.groupHom (transition S h)).hom.hom)) =
      TateTwist.transition Γ(T.left, ⊤) h (pointsLevelEquiv m T (Additive.ofMul x)) :=
  pointsEquiv_transition S h T x

/-- Over an affine test scheme, the transition `μ_m ⟶ μ_n` is `TateTwist.transition`. -/
lemma levelEquiv_transition {n m : ℕ} (h : n ∣ m) {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (x : Over.mk f ⟶ (mu S m).X) :
    levelEquiv n f (Additive.ofMul (x ≫ (CommGroupScheme.groupHom (transition S h)).hom.hom)) =
      TateTwist.transition R h (levelEquiv m f (Additive.ofMul x)) := by
  change MulEquiv.restrictRootsOfUnity _ n
      (pointsEquiv S n (Over.mk f) (x ≫ (CommGroupScheme.groupHom (transition S h)).hom.hom)) =
    rootsTransition R h (MulEquiv.restrictRootsOfUnity _ m (pointsEquiv S m (Over.mk f) x))
  rw [pointsEquiv_transition]
  exact (rootsTransition_restrict _ h _).symm

/-- The transition `μ_m ⟶ μ_n` followed by the inclusion is the inclusion followed by the
`(m / n)`-th power map of `𝔾_m`. -/
lemma transition_incl {n m : ℕ} (h : n ∣ m) :
    transition S h ≫ incl S n =
      incl S m ≫ Additive.ofMul (multiplication (Gm S).toGrp (m / n : ℕ)) := by
  apply congrArg Additive.ofMul
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv S T).injective
  change Gm.pointsEquiv S T ((x ≫ (CommGroupScheme.groupHom (transition S h)).hom.hom) ≫
      (torsionι (Gm S).toGrp n).hom.hom) =
    Gm.pointsEquiv S T ((x ≫ (torsionι (Gm S).toGrp m).hom.hom) ≫
      (multiplication (Gm S).toGrp (m / n : ℕ)).hom.hom)
  rw [points_multiplication, ← pointsEquiv_val, pointsEquiv_transition, rootsTransition_val,
    pointsEquiv_val, zpow_natCast, map_pow]

end mu

/-! ### Base change -/

namespace Gm

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- The points of the base change of `𝔾_{m,S}` along `b : S' ⟶ S` are global units. -/
def baseChangeUnitsEquiv (T : Over S') :
    (T ⟶ ((Over.pullback b).mapGrp.obj (Gm S).toGrp).X) ≃* (Γ(T.left, ⊤))ˣ :=
  (baseChangePointsEquiv b (Gm S).toGrp T).trans (pointsEquiv S ((Over.map b).obj T))

lemma baseChangeUnitsEquiv_apply (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (Gm S).toGrp).X) :
    baseChangeUnitsEquiv b T x =
      pointsEquiv S ((Over.map b).obj T) (baseChangePointsEquiv b (Gm S).toGrp T x) := rfl

lemma baseChangeUnitsEquiv_naturality {T T' : Over S'} (a : T' ⟶ T)
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (Gm S).toGrp).X) :
    baseChangeUnitsEquiv b T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (baseChangeUnitsEquiv b T x) := by
  rw [baseChangeUnitsEquiv_apply, baseChangePointsEquiv_naturality, pointsEquiv_naturality]
  rfl

lemma baseChangeIso_naturality {T T' : Over S'} (a : T' ⟶ T)
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (Gm S).toGrp).X) :
    (pointsEquiv S' T').symm (baseChangeUnitsEquiv b T' (a ≫ x)) =
      a ≫ (pointsEquiv S' T).symm (baseChangeUnitsEquiv b T x) := by
  apply (pointsEquiv S' _).injective
  rw [MulEquiv.apply_symm_apply, pointsEquiv_naturality, MulEquiv.apply_symm_apply,
    baseChangeUnitsEquiv_naturality]

/-- The canonical isomorphism between the base change of `𝔾_{m,S}` along `b : S' ⟶ S` and
`𝔾_{m,S'}`: both represent the global units. -/
def baseChangeIso : (Over.pullback b).mapGrp.obj (Gm S).toGrp ≅ (Gm S').toGrp :=
  isoOfPoints (fun T => (baseChangeUnitsEquiv b T).trans (pointsEquiv S' T).symm)
    (baseChangeIso_naturality b)

/-- On points, the base-change isomorphism of `𝔾_m` preserves the underlying unit. -/
@[simp]
lemma pointsEquiv_baseChangeIso_hom (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (Gm S).toGrp).X) :
    pointsEquiv S' T (x ≫ (baseChangeIso b).hom.hom.hom) = baseChangeUnitsEquiv b T x := by
  have key : x ≫ (baseChangeIso b).hom.hom.hom = _ :=
    comp_isoOfPoints_hom _ (baseChangeIso_naturality b) T x
  rw [key]
  simp

@[simp]
lemma baseChangeUnitsEquiv_baseChangeIso_inv (T : Over S') (y : T ⟶ (Gm S').X) :
    baseChangeUnitsEquiv b T (y ≫ (baseChangeIso b).inv.hom.hom) = pointsEquiv S' T y := by
  have key : y ≫ (baseChangeIso b).inv.hom.hom = _ :=
    comp_isoOfPoints_inv _ (baseChangeIso_naturality b) T y
  rw [key]
  simp

/-- The base-change isomorphism of `𝔾_m`, as commutative group schemes. -/
def commBaseChangeIso : (CommGroupScheme.baseChange b).obj (Gm S) ≅ Gm S' where
  hom := Additive.ofMul (baseChangeIso b).hom
  inv := Additive.ofMul (baseChangeIso b).inv
  hom_inv_id := congrArg Additive.ofMul (baseChangeIso b).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (baseChangeIso b).inv_hom_id

lemma groupHom_commBaseChangeIso_hom :
    CommGroupScheme.groupHom (commBaseChangeIso b).hom = (baseChangeIso b).hom := rfl

lemma groupHom_commBaseChangeIso_inv :
    CommGroupScheme.groupHom (commBaseChangeIso b).inv = (baseChangeIso b).inv := rfl

end Gm

namespace mu

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (n : ℕ)

/-- The points of the base change of `μ_{n,S}` along `b : S' ⟶ S` are roots of unity. -/
def baseChangeRootsEquiv (T : Over S') :
    (T ⟶ ((Over.pullback b).mapGrp.obj (mu S n).toGrp).X) ≃* rootsOfUnity n Γ(T.left, ⊤) :=
  (baseChangePointsEquiv b (mu S n).toGrp T).trans (pointsEquiv S n ((Over.map b).obj T))

lemma baseChangeRootsEquiv_apply (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (mu S n).toGrp).X) :
    baseChangeRootsEquiv b n T x =
      pointsEquiv S n ((Over.map b).obj T) (baseChangePointsEquiv b (mu S n).toGrp T x) := rfl

lemma baseChangeRootsEquiv_naturality {T T' : Over S'} (a : T' ⟶ T)
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (mu S n).toGrp).X) :
    baseChangeRootsEquiv b n T' (a ≫ x) =
      restrictRootsOfUnity a.left.appTop.hom n (baseChangeRootsEquiv b n T x) := by
  rw [baseChangeRootsEquiv_apply, baseChangePointsEquiv_naturality, pointsEquiv_naturality]
  rfl

/-- The base change of `μ_{n,S}` along the base change of `μ_n ⟶ 𝔾_m` is the inclusion of
roots of unity into units. -/
lemma baseChangeRootsEquiv_val (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (mu S n).toGrp).X) :
    (baseChangeRootsEquiv b n T x : (Γ(T.left, ⊤))ˣ) =
      Gm.baseChangeUnitsEquiv b T
        (x ≫ ((Over.pullback b).mapGrp.map (torsionι (Gm S).toGrp n)).hom.hom) := by
  rw [Gm.baseChangeUnitsEquiv_apply, baseChangePointsEquiv_comp]
  rfl

lemma baseChangeIso_naturality {T T' : Over S'} (a : T' ⟶ T)
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (mu S n).toGrp).X) :
    (pointsEquiv S' n T').symm (baseChangeRootsEquiv b n T' (a ≫ x)) =
      a ≫ (pointsEquiv S' n T).symm (baseChangeRootsEquiv b n T x) := by
  apply (pointsEquiv S' n _).injective
  rw [MulEquiv.apply_symm_apply, pointsEquiv_naturality, MulEquiv.apply_symm_apply,
    baseChangeRootsEquiv_naturality]

/-- The canonical isomorphism between the base change of `μ_{n,S}` along `b : S' ⟶ S` and
`μ_{n,S'}`: both represent the `n`-th roots of unity. -/
def baseChangeIso : (Over.pullback b).mapGrp.obj (mu S n).toGrp ≅ (mu S' n).toGrp :=
  isoOfPoints (fun T => (baseChangeRootsEquiv b n T).trans (pointsEquiv S' n T).symm)
    (baseChangeIso_naturality b n)

/-- On points, the base-change isomorphism of `μ_n` preserves the underlying root of unity. -/
@[simp]
lemma pointsEquiv_baseChangeIso_hom (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (mu S n).toGrp).X) :
    pointsEquiv S' n T (x ≫ (baseChangeIso b n).hom.hom.hom) = baseChangeRootsEquiv b n T x := by
  have key : x ≫ (baseChangeIso b n).hom.hom.hom = _ :=
    comp_isoOfPoints_hom _ (baseChangeIso_naturality b n) T x
  rw [key]
  simp

@[simp]
lemma baseChangeRootsEquiv_baseChangeIso_inv (T : Over S') (y : T ⟶ (mu S' n).X) :
    baseChangeRootsEquiv b n T (y ≫ (baseChangeIso b n).inv.hom.hom) = pointsEquiv S' n T y := by
  have key : y ≫ (baseChangeIso b n).inv.hom.hom = _ :=
    comp_isoOfPoints_inv _ (baseChangeIso_naturality b n) T y
  rw [key]
  simp

/-- The base-change isomorphisms of `μ_n` and `𝔾_m` are compatible with the inclusions. -/
lemma baseChangeIso_hom_ι :
    (baseChangeIso b n).hom ≫ torsionι (Gm S').toGrp n =
      (Over.pullback b).mapGrp.map (torsionι (Gm S).toGrp n) ≫ (Gm.baseChangeIso b).hom := by
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv S' T).injective
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    ← pointsEquiv_val, pointsEquiv_baseChangeIso_hom, Gm.pointsEquiv_baseChangeIso_hom,
    baseChangeRootsEquiv_val]

/-- The base-change isomorphism of `μ_n`, as commutative group schemes. -/
def commBaseChangeIso : (CommGroupScheme.baseChange b).obj (mu S n) ≅ mu S' n where
  hom := Additive.ofMul (baseChangeIso b n).hom
  inv := Additive.ofMul (baseChangeIso b n).inv
  hom_inv_id := congrArg Additive.ofMul (baseChangeIso b n).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (baseChangeIso b n).inv_hom_id

lemma groupHom_commBaseChangeIso_hom :
    CommGroupScheme.groupHom (commBaseChangeIso b n).hom = (baseChangeIso b n).hom := rfl

/-- The commutative base-change isomorphisms of `μ_n` and `𝔾_m` are compatible with the
inclusions. -/
lemma commBaseChangeIso_hom_incl :
    (commBaseChangeIso b n).hom ≫ incl S' n =
      (CommGroupScheme.baseChange b).map (incl S n) ≫ (Gm.commBaseChangeIso b).hom :=
  congrArg Additive.ofMul (baseChangeIso_hom_ι b n)

end mu

end Langlands.GroupScheme
