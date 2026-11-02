import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Rational characters, the centre and split components

For a group scheme `G` over a scheme `S`, the rational characters of `G` are the homomorphisms
`G ⟶ 𝔾_{m,S}` of group schemes over `S`, with the pointwise product of values written additively.
Over `S = Spec k` this is the group `X^*(G)_k` of Renard (V.2.2), or `Rat(G)` of Waldspurger (I.1).
Characters restrict along homomorphisms and evaluate on points through `Gm.pointsEquiv`.

The centre of `G` is the subgroup functor of points commuting with all points after every base
change of test schemes. Over a field, a central split torus is a split subtorus whose points are
central, and a split component `A_G` is a central split torus that is maximal among central split
tori, in the pattern of `IsMaximalSplitTorus`.

For the general linear group scheme, this module builds the determinant character, the scalar
torus `𝔾_m ⟶ GL_n`, which is central for every `n` and a closed subgroup for nonempty `n`, and the
block determinant characters of the block Levi subgroup schemes.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Rational characters and restriction -/

section Characters

variable {S : Scheme.{u}}

/-- The rational characters of `G`: the homomorphisms `G ⟶ 𝔾_{m,S}` of group schemes over `S`,
an additive commutative group under the pointwise product of values. Over `S = Spec k` this is
`X^*(G)_k`, the characters of `G` defined over `k`. -/
abbrev rationalCharacters (G : GroupScheme S) : Type u :=
  HomAdd G (Gm S).toGrp

namespace rationalCharacters

variable {G : GroupScheme S}

theorem toMul_add (χ ψ : rationalCharacters G) : (χ + ψ).toMul = χ.toMul * ψ.toMul := rfl

theorem toMul_zero : (0 : rationalCharacters G).toMul = 1 := rfl

/-- On points, a sum of characters takes the product of the values. -/
theorem comp_add {T : Over S} (x : T ⟶ G.X) (χ ψ : rationalCharacters G) :
    x ≫ (χ + ψ).toMul.hom.hom = (x ≫ χ.toMul.hom.hom) * (x ≫ ψ.toMul.hom.hom) :=
  MonObj.comp_mul _ _ _

/-- On points, the zero character takes the value `1`. -/
theorem comp_zero {T : Over S} (x : T ⟶ G.X) :
    x ≫ (0 : rationalCharacters G).toMul.hom.hom = 1 :=
  MonObj.comp_one _

/-- For a commutative group scheme `T`, the rational characters of `T` are its character lattice
`X^*(T) = Hom(T, 𝔾_m)`; the two additive groups are the same. -/
def equivCharacterLattice (T : CommGroupScheme S) :
    rationalCharacters T.toGrp ≃+ characterLattice T :=
  AddEquiv.refl _

theorem groupHom_equivCharacterLattice (T : CommGroupScheme S) (χ : rationalCharacters T.toGrp) :
    CommGroupScheme.groupHom (equivCharacterLattice T χ) = χ.toMul :=
  rfl

end rationalCharacters

variable {G H K : GroupScheme S}

/-- Restriction of rational characters along a homomorphism `f : H ⟶ G`: `χ ↦ χ ∘ f`. -/
def characterRestrict (f : H ⟶ G) : rationalCharacters G →+ rationalCharacters H where
  toFun χ := Additive.ofMul (f ≫ χ.toMul)
  map_zero' := congrArg Additive.ofMul (MonObj.comp_one f)
  map_add' χ ψ := congrArg Additive.ofMul (MonObj.comp_mul f χ.toMul ψ.toMul)

theorem characterRestrict_apply (f : H ⟶ G) (χ : rationalCharacters G) :
    (characterRestrict f χ).toMul = f ≫ χ.toMul :=
  rfl

/-- Restriction along the identity is the identity. -/
theorem characterRestrict_id : characterRestrict (𝟙 G) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun χ => congrArg Additive.ofMul (Category.id_comp χ.toMul)

/-- Restriction along a composite is the composite of the restrictions, in reverse order. -/
theorem characterRestrict_comp (g : K ⟶ H) (f : H ⟶ G) :
    characterRestrict (g ≫ f) = (characterRestrict g).comp (characterRestrict f) :=
  AddMonoidHom.ext fun χ => congrArg Additive.ofMul (Category.assoc g f χ.toMul)

end Characters

/-! ### Evaluation on points -/

section Evaluation

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Evaluation of a rational character on `T`-points, with values in the global units of `T`
through the published identification `Gm.pointsEquiv` of the points of `𝔾_m`. -/
def characterEval (χ : rationalCharacters G) (T : Over S) : (T ⟶ G.X) →* (Γ(T.left, ⊤))ˣ where
  toFun x := Gm.pointsEquiv S T (x ≫ χ.toMul.hom.hom)
  map_one' := by rw [MonObj.one_comp, map_one]
  map_mul' x y := by rw [MonObj.mul_comp, map_mul]

theorem characterEval_apply (χ : rationalCharacters G) (T : Over S) (x : T ⟶ G.X) :
    characterEval χ T x = Gm.pointsEquiv S T (x ≫ χ.toMul.hom.hom) :=
  rfl

/-- Evaluation is natural in the test scheme: restriction along `a : T' ⟶ T` acts on the values
by pulling back global units. -/
theorem characterEval_naturality (χ : rationalCharacters G) {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    characterEval χ T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (characterEval χ T x) := by
  rw [characterEval_apply, characterEval_apply, Category.assoc, Gm.pointsEquiv_naturality]

/-- The value of a sum of characters is the product of the values. -/
theorem characterEval_add (χ ψ : rationalCharacters G) (T : Over S) (x : T ⟶ G.X) :
    characterEval (χ + ψ) T x = characterEval χ T x * characterEval ψ T x := by
  rw [characterEval_apply, rationalCharacters.comp_add, map_mul]
  rfl

theorem characterEval_zero (T : Over S) (x : T ⟶ G.X) :
    characterEval (0 : rationalCharacters G) T x = 1 := by
  rw [characterEval_apply, rationalCharacters.comp_zero, map_one]

/-- Evaluation on `T`-points, as an additive map from rational characters to homomorphisms
`G(T) →* Γ(T, 𝒪_T)ˣ` written additively. -/
def characterEvalHom (T : Over S) :
    rationalCharacters G →+ Additive ((T ⟶ G.X) →* (Γ(T.left, ⊤))ˣ) where
  toFun χ := Additive.ofMul (characterEval χ T)
  map_zero' := congrArg Additive.ofMul (MonoidHom.ext (characterEval_zero T))
  map_add' χ ψ := congrArg Additive.ofMul (MonoidHom.ext (characterEval_add χ ψ T))

theorem characterEvalHom_apply (T : Over S) (χ : rationalCharacters G) :
    (characterEvalHom T χ).toMul = characterEval χ T :=
  rfl

/-- The value of an integer multiple of a character is the power of the value. -/
theorem characterEval_zsmul (m : ℤ) (χ : rationalCharacters G) (T : Over S) (x : T ⟶ G.X) :
    characterEval (m • χ) T x = characterEval χ T x ^ m := by
  have h := congrArg Additive.toMul (map_zsmul (characterEvalHom (G := G) T) m χ)
  rw [toMul_zsmul] at h
  exact (DFunLike.congr_fun h x).trans (MonoidHom.zpow_apply _ _ _)

/-- Evaluation is compatible with restriction: `(χ ∘ f)(x) = χ(f(x))`. -/
theorem characterEval_characterRestrict (f : H ⟶ G) (χ : rationalCharacters G) (T : Over S)
    (x : T ⟶ H.X) :
    characterEval (characterRestrict f χ) T x = characterEval χ T (x ≫ f.hom.hom) := by
  rw [characterEval_apply, characterEval_apply, Category.assoc]
  rfl

/-- Rational characters are determined by their values on points. -/
theorem rationalCharacters.ext_characterEval {χ ψ : rationalCharacters G}
    (h : ∀ (T : Over S) (x : T ⟶ G.X), characterEval χ T x = characterEval ψ T x) : χ = ψ :=
  congrArg Additive.ofMul (hom_ext_points fun T x => (Gm.pointsEquiv S T).injective (h T x))

end Evaluation

/-! ### Rational points and evaluation over a ring -/

section RationalPoints

variable {k : Type u} [CommRing k]

/-- The `k`-points `G(k)` of a group scheme over `Spec k`: its sections over `Spec k`, with the
pointwise group law. -/
abbrev rationalPoints (G : GroupScheme (Spec (CommRingCat.of k))) : Type u :=
  Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X

variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism of group schemes over `Spec k` induces a homomorphism on `k`-points. -/
def rationalPoints.map (f : H ⟶ G) : rationalPoints H →* rationalPoints G where
  toFun y := y ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

theorem rationalPoints.map_apply (f : H ⟶ G) (y : rationalPoints H) :
    rationalPoints.map f y = y ≫ f.hom.hom :=
  rfl

/-- Evaluation of a rational character on `k`-points, `χ : G(k) →* kˣ`: the evaluation on the
test scheme `Spec k`, followed by `Γ(Spec k, 𝒪) ≅ k`. -/
def rationalCharacterEval (χ : rationalCharacters G) : rationalPoints G →* kˣ :=
  (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom).comp
    (characterEval χ (Over.mk (𝟙 (Spec (CommRingCat.of k)))))

theorem rationalCharacterEval_val (χ : rationalCharacters G) (g : rationalPoints G) :
    (rationalCharacterEval χ g : k) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom
        (characterEval χ (Over.mk (𝟙 (Spec (CommRingCat.of k)))) g).val :=
  rfl

/-- The `k`-point evaluation agrees with the published affine points of `𝔾_m`. -/
theorem rationalCharacterEval_apply (χ : rationalCharacters G) (g : rationalPoints G) :
    rationalCharacterEval χ g = Gm.affinePointsEquiv (𝟙 _) (g ≫ χ.toMul.hom.hom) :=
  rfl

theorem rationalCharacterEval_add (χ ψ : rationalCharacters G) (g : rationalPoints G) :
    rationalCharacterEval (χ + ψ) g = rationalCharacterEval χ g * rationalCharacterEval ψ g :=
  (congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom)
    (characterEval_add χ ψ _ g)).trans (map_mul _ _ _)

theorem rationalCharacterEval_zero (g : rationalPoints G) :
    rationalCharacterEval (0 : rationalCharacters G) g = 1 :=
  (congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom)
    (characterEval_zero _ g)).trans (map_one _)

/-- Evaluation on `k`-points, as an additive map from rational characters to homomorphisms
`G(k) →* kˣ` written additively. -/
def rationalCharacterEvalHom : rationalCharacters G →+ Additive (rationalPoints G →* kˣ) where
  toFun χ := Additive.ofMul (rationalCharacterEval χ)
  map_zero' := congrArg Additive.ofMul (MonoidHom.ext rationalCharacterEval_zero)
  map_add' χ ψ := congrArg Additive.ofMul (MonoidHom.ext (rationalCharacterEval_add χ ψ))

theorem rationalCharacterEvalHom_apply (χ : rationalCharacters G) :
    (rationalCharacterEvalHom χ).toMul = rationalCharacterEval χ :=
  rfl

/-- Evaluation on `k`-points is compatible with restriction. -/
theorem rationalCharacterEval_characterRestrict (f : H ⟶ G) (χ : rationalCharacters G)
    (y : rationalPoints H) :
    rationalCharacterEval (characterRestrict f χ) y =
      rationalCharacterEval χ (rationalPoints.map f y) :=
  congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom)
    (characterEval_characterRestrict f χ _ y)

end RationalPoints

/-! ### The centre -/

section Center

variable {S : Scheme.{u}}

/-- The centre of a group scheme `G`, as a subgroup functor: a point `g` over `T` is central when,
for every `a : T' ⟶ T`, its restriction `a ≫ g` commutes with every point of `G` over `T'`. -/
def center (G : GroupScheme S) : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | ∀ (T' : Over S) (a : T' ⟶ T) (h : T' ⟶ G.X), Commute (a ≫ g) h}
      mul_mem' := by
        intro g g' hg hg' T' a h
        rw [MonObj.comp_mul]
        exact (hg T' a h).mul_left (hg' T' a h)
      one_mem' := by
        intro T' a h
        rw [MonObj.comp_one]
        exact Commute.one_left h
      inv_mem' := by
        intro g hg T' a h
        rw [GrpObj.comp_inv]
        exact (hg T' a h).inv_left }
  comp_mem a g hg T'' b h := by
    rw [← Category.assoc]
    exact hg T'' (b ≫ a) h

variable {G H H' : GroupScheme S}

theorem mem_center {T : Over S} {g : T ⟶ G.X} :
    g ∈ (center G).carrier T ↔ ∀ (T' : Over S) (a : T' ⟶ T) (h : T' ⟶ G.X), Commute (a ≫ g) h :=
  Iff.rfl

/-- A central point commutes with every point over the same test scheme. -/
theorem commute_of_mem_center {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (center G).carrier T)
    (h : T ⟶ G.X) : Commute g h := by
  have := hg T (𝟙 T) h
  rwa [Category.id_comp] at this

/-- The rational points of the centre lie in the centre of the group of rational points. -/
theorem center_carrier_le_center {k : Type u} [CommRing k]
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    (center G).carrier (Over.mk (𝟙 _)) ≤ Subgroup.center (rationalPoints G) := fun _ hg =>
  Subgroup.mem_center_iff.mpr fun h => (commute_of_mem_center hg h).eq.symm

/-- A homomorphism `i : H ⟶ G` is central when every point of `H` maps into the centre of `G`. -/
def IsCentral (i : H ⟶ G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ H.X), x ≫ i.hom.hom ∈ (center G).carrier T

/-- Precomposition preserves centrality. -/
theorem IsCentral.comp {i : H ⟶ G} (hi : IsCentral i) (f : H' ⟶ H) : IsCentral (f ≫ i) :=
  fun T x => by
    have := hi T (x ≫ f.hom.hom)
    rwa [Category.assoc] at this

/-- The `k`-points of a central homomorphism land in the centre of `G(k)`. -/
theorem IsCentral.map_mem_center {k : Type u} [CommRing k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G} (hi : IsCentral i)
    (y : rationalPoints H) : rationalPoints.map i y ∈ Subgroup.center (rationalPoints G) :=
  center_carrier_le_center G (hi _ y)

/-- The image of `H(k)` under a central homomorphism lies in the centre of `G(k)`. -/
theorem IsCentral.range_le_center {k : Type u} [CommRing k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G} (hi : IsCentral i) :
    (rationalPoints.map i).range ≤ Subgroup.center (rationalPoints G) := by
  rintro _ ⟨y, rfl⟩
  exact hi.map_mem_center y

end Center

/-! ### Central split tori and split components over a field -/

section SplitComponent

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A central split torus of `G`: a split subtorus `i : A ⟶ G` (the published `IsSplitSubtorus`)
whose points all map into the centre of `G`. -/
def IsCentralSplitTorus (i : A.toGrp ⟶ G) : Prop :=
  IsSplitSubtorus i ∧ IsCentral i

/-- A split component `A_G` of `G`: a central split torus `i : A ⟶ G` such that every
factorization `f ≫ i' = i` through a central split torus `i' : A' ⟶ G` has `f` an isomorphism.
This is Renard's *composante déployée* (V.2.1) and Waldspurger's `A_G` (I.1), in the pattern of
`IsMaximalSplitTorus`. -/
def IsSplitComponent (i : A.toGrp ⟶ G) : Prop :=
  IsCentralSplitTorus i ∧
    ∀ (A' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : A'.toGrp ⟶ G),
      IsCentralSplitTorus i' → ∀ f : A.toGrp ⟶ A'.toGrp, f ≫ i' = i → IsIso f

theorem IsCentralSplitTorus.isSplitSubtorus {i : A.toGrp ⟶ G} (hi : IsCentralSplitTorus i) :
    IsSplitSubtorus i :=
  hi.1

theorem IsCentralSplitTorus.isCentral {i : A.toGrp ⟶ G} (hi : IsCentralSplitTorus i) :
    IsCentral i :=
  hi.2

theorem IsSplitComponent.isCentralSplitTorus {i : A.toGrp ⟶ G} (hi : IsSplitComponent i) :
    IsCentralSplitTorus i :=
  hi.1

/-- For a central split torus `i : A ⟶ G`, the image of `A(k)` in `G(k)` lies in the centre of
`G(k)`. -/
theorem IsCentralSplitTorus.range_le_center {i : A.toGrp ⟶ G} (hi : IsCentralSplitTorus i) :
    (rationalPoints.map i).range ≤ Subgroup.center (rationalPoints G) :=
  hi.2.range_le_center

end SplitComponent

/-! ### The general linear group -/

namespace GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {R : CommRingCat.{u}}

/-- Change of coefficients sends scalar matrices to scalar matrices: Mathlib's
`Matrix.GeneralLinearGroup.map_scalar`, with the unit map written as in
`Gm.pointsEquiv_naturality`. -/
theorem map_scalar {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A') (t : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar n t) =
      Matrix.GeneralLinearGroup.scalar n (Units.map f.toMonoidHom t) :=
  Matrix.GeneralLinearGroup.map_scalar f t

/-! #### The determinant character -/

variable (n R) in
/-- The determinant on points over every test scheme, with values in the points of `𝔾_m`. -/
def determinantPoints (T : Over (Spec R)) :
    (T ⟶ (groupScheme n R).X) →* (T ⟶ (Gm (Spec R)).X) :=
  (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
    (Matrix.GeneralLinearGroup.det.comp (pointsEquiv n R T).toMonoidHom)

theorem determinantPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme n R).X) :
    determinantPoints n R T' (a ≫ x) = a ≫ determinantPoints n R T x := by
  apply (Gm.pointsEquiv (Spec R) T').injective
  simp only [determinantPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, pointsEquiv_naturality,
    Matrix.GeneralLinearGroup.map_det]
  rfl

variable (n R) in
/-- The determinant character `det : GL_n ⟶ 𝔾_m` of the general linear group scheme. -/
def determinantCharacter : rationalCharacters (groupScheme n R) :=
  Additive.ofMul (homOfPoints (determinantPoints n R) determinantPoints_naturality)

theorem comp_determinantCharacter (T : Over (Spec R)) (x : T ⟶ (groupScheme n R).X) :
    x ≫ (determinantCharacter n R).toMul.hom.hom = determinantPoints n R T x :=
  comp_homOfPoints (determinantPoints n R) determinantPoints_naturality T x

/-- On points, the determinant character is the determinant of the matrix. -/
theorem characterEval_determinantCharacter (T : Over (Spec R)) (x : T ⟶ (groupScheme n R).X) :
    characterEval (determinantCharacter n R) T x =
      Matrix.GeneralLinearGroup.det (pointsEquiv n R T x) := by
  rw [characterEval_apply, comp_determinantCharacter]
  exact MulEquiv.apply_symm_apply _ _

/-! #### The scalar torus -/

variable (n R) in
/-- Scalar matrices on points over every test scheme. -/
def scalarPoints (T : Over (Spec R)) :
    (T ⟶ (Gm (Spec R)).X) →* (T ⟶ (groupScheme n R).X) :=
  (pointsEquiv n R T).symm.toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.scalar n).comp (Gm.pointsEquiv (Spec R) T).toMonoidHom)

theorem scalarPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec R)).X) :
    scalarPoints n R T' (a ≫ x) = a ≫ scalarPoints n R T x := by
  apply (pointsEquiv n R T').injective
  simp only [scalarPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rw [pointsEquiv_naturality, MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality, map_scalar]

variable (n R) in
/-- The scalar torus `𝔾_m ⟶ GL_n`, `t ↦ t · 1`. -/
def scalarTorus : (Gm (Spec R)).toGrp ⟶ groupScheme n R :=
  homOfPoints (scalarPoints n R) scalarPoints_naturality

/-- On points, the scalar torus sends a unit `t` to the scalar matrix `t · 1`. -/
theorem pointsEquiv_scalarTorus (T : Over (Spec R)) (x : T ⟶ (Gm (Spec R)).X) :
    pointsEquiv n R T (x ≫ (scalarTorus n R).hom.hom) =
      Matrix.GeneralLinearGroup.scalar n (Gm.pointsEquiv (Spec R) T x) := by
  rw [scalarTorus, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

/-- The scalar torus is the diagonal cocharacter with all weights equal to `1`. -/
theorem scalarTorus_eq_diagonalCocharacter :
    scalarTorus n R = diagonalCocharacter n R (fun _ => 1) := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv n R T).injective
  rw [pointsEquiv_scalarTorus, pointsEquiv_diagonalCocharacter]
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagonalUnits, Matrix.scalar_apply]
  simp

/-- The points of the scalar torus are central, for every `n`. -/
theorem isCentral_scalarTorus : IsCentral (scalarTorus n R) := by
  intro T x T' a h
  rw [← Category.assoc]
  have hc : Commute (pointsEquiv n R T' ((a ≫ x) ≫ (scalarTorus n R).hom.hom))
      (pointsEquiv n R T' h) := by
    rw [pointsEquiv_scalarTorus]
    have hz : Matrix.GeneralLinearGroup.scalar n (Gm.pointsEquiv (Spec R) T' (a ≫ x)) ∈
        Subgroup.center (GL n Γ(T'.left, ⊤)) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.mem_center_iff.mp hz _).symm
  exact (pointsEquiv n R T').injective (by rw [map_mul, map_mul]; exact hc)

/-! #### The scalar torus is a closed subgroup for nonempty `n` -/

/-- An invertible matrix is scalar exactly when its off-diagonal entries vanish and its diagonal
entries are equal. -/
theorem mem_range_scalar_iff {A : Type*} [CommRing A] (g : GL n A) :
    g ∈ (Matrix.GeneralLinearGroup.scalar n).range ↔
      (∀ i j, i ≠ j → (g : Matrix n n A) i j = 0) ∧
        ∀ i j, (g : Matrix n n A) i i = (g : Matrix n n A) j j := by
  rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i j hij => ?_, fun i j => ?_⟩
    · rw [← hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
    · rw [← hc, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rintro ⟨h₁, h₂⟩
    cases isEmpty_or_nonempty n with
    | inl _ => exact ⟨0, Subsingleton.elim _ _⟩
    | inr hn =>
      obtain ⟨i₀⟩ := hn
      refine ⟨(g : Matrix n n A) i₀ i₀, ?_⟩
      ext i j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs with hij
      · subst hij
        exact (h₂ i i₀).symm
      · exact (h₁ i j hij).symm

variable (n R) in
/-- The ideal of the coordinate ring of `GL_n` generated by the off-diagonal entries `x_ij`
(`i ≠ j`) and the differences `x_ii - x_jj` of diagonal entries. -/
def scalarIdeal : Ideal (CoordinateRing n R) :=
  Ideal.span ({b | ∃ i j, i ≠ j ∧ quotient n R (MvPolynomial.X (Coordinate.entry i j)) = b} ∪
    {b | ∃ i j, quotient n R (MvPolynomial.X (Coordinate.entry i i)) -
      quotient n R (MvPolynomial.X (Coordinate.entry j j)) = b})

/-- The algebra map classifying an invertible matrix `g` kills `scalarIdeal n R` exactly when `g`
is scalar. -/
theorem classify_eq_zero_iff_scalar {A : Type u} [CommRing A] [Algebra R A] (g : GL n A) :
    (∀ b ∈ scalarIdeal n R, classify (R := R) g b = 0) ↔
      g ∈ (Matrix.GeneralLinearGroup.scalar n).range := by
  rw [mem_range_scalar_iff]
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i j => ?_⟩
    · have hb := h _ (Ideal.subset_span (Or.inl ⟨i, j, hij, rfl⟩))
      rwa [classify_entry] at hb
    · have hb := h _ (Ideal.subset_span (Or.inr ⟨i, j, rfl⟩))
      rwa [map_sub, sub_eq_zero, classify_entry, classify_entry] at hb
  · rintro ⟨h₁, h₂⟩ b hb
    have hle : scalarIdeal n R ≤ RingHom.ker (classify (R := R) g) := by
      refine Ideal.span_le.mpr ?_
      rintro _ (⟨i, j, hij, rfl⟩ | ⟨i, j, rfl⟩)
      · rw [SetLike.mem_coe, RingHom.mem_ker, classify_entry]
        exact h₁ i j hij
      · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero, classify_entry,
          classify_entry]
        exact h₂ i j
    exact hle hb

variable (n R) in
/-- The scalar invertible matrices, as a family of subgroups of the points of `GL_n` over the
`R`-algebras. -/
def scalarSubgroup (A : CommAlgCat.{u} R) : Subgroup ((functor n R).obj A) :=
  (Matrix.GeneralLinearGroup.scalar n).range

theorem mem_scalarSubgroup {A : CommAlgCat.{u} R} (g : GL n A) :
    g ∈ scalarSubgroup n R A ↔ g ∈ (Matrix.GeneralLinearGroup.scalar n).range :=
  Iff.rfl

/-- The scalar matrices are cut out of `GL_n` by `scalarIdeal n R`. -/
theorem isCutOutBy_scalarIdeal :
    Corepresented.IsCutOutBy (corepresentableBy n R) (scalarSubgroup n R) (scalarIdeal n R) :=
  fun _ g => (classify_eq_zero_iff_scalar g).symm

/-- The points of a closed subgroup scheme of `GL_n` cut out by an ideal map to `GL_n` through
`Corepresented.cutHom` by forgetting membership. -/
theorem pointsEquiv_cutHom {H : ∀ A : CommAlgCat.{u} R, Subgroup ((functor n R).obj A)}
    {I : Ideal (CoordinateRing n R)} (hI : Corepresented.IsCutOutBy (corepresentableBy n R) H I)
    {T : Over (Spec R)} (y : T ⟶ (Corepresented.cutGroupScheme hI).X) :
    pointsEquiv n R T (y ≫ (Corepresented.cutHom hI).hom.hom) =
      (Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy hI) T y).val :=
  Corepresented.groupSchemeMap_points _ _ _ y

section Nonempty

variable [Nonempty n]

/-- For nonempty `n`, a unit is determined by the scalar matrix it defines. -/
theorem scalar_injective (A : Type*) [CommRing A] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar n (R := A)) := by
  intro s t h
  obtain ⟨i⟩ := ‹Nonempty n›
  apply Units.ext
  have := congrArg (fun g : GL n A => (g : Matrix n n A) i i) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

variable (n R) in
/-- For nonempty `n`, the units of an `R`-algebra `A` are identified with the scalar invertible
matrices over `A`. -/
def scalarEquiv (A : CommAlgCat.{u} R) : Aˣ ≃* scalarSubgroup n R A :=
  MonoidHom.ofInjective (scalar_injective A)

theorem scalarEquiv_val (A : CommAlgCat.{u} R) (t : Aˣ) :
    (scalarEquiv n R A t).1 = Matrix.GeneralLinearGroup.scalar n t :=
  rfl

variable (n R) in
/-- Points of `𝔾_m` identify with points of the closed subgroup scheme of scalar matrices. -/
def scalarCutPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (Gm (Spec R)).X) ≃*
      (T ⟶ (Corepresented.cutGroupScheme (isCutOutBy_scalarIdeal (n := n) (R := R))).X) :=
  (Gm.pointsEquiv (Spec R) T).trans ((scalarEquiv n R ((algΓ R).obj T).unop).trans
    (Corepresented.pointsEquiv (Corepresented.cutFunctor (isCutOutBy_scalarIdeal (n := n) (R := R)))
      (Corepresented.cutCorepresentableBy (isCutOutBy_scalarIdeal (n := n) (R := R))) T).symm)

/-- The cut-out point attached to a point of `𝔾_m` is the scalar matrix of its unit. -/
theorem pointsEquiv_scalarCutPointsEquiv (T : Over (Spec R)) (x : T ⟶ (Gm (Spec R)).X) :
    Corepresented.pointsEquiv (Corepresented.cutFunctor (isCutOutBy_scalarIdeal (n := n) (R := R)))
        (Corepresented.cutCorepresentableBy (isCutOutBy_scalarIdeal (n := n) (R := R))) T
        (scalarCutPointsEquiv n R T x) =
      scalarEquiv n R ((algΓ R).obj T).unop (Gm.pointsEquiv (Spec R) T x) :=
  MulEquiv.apply_symm_apply _ _

theorem scalarCutPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec R)).X) :
    scalarCutPointsEquiv n R T' (a ≫ x) = a ≫ scalarCutPointsEquiv n R T x := by
  apply (Corepresented.pointsEquiv _
    (Corepresented.cutCorepresentableBy (isCutOutBy_scalarIdeal (n := n) (R := R))) T').injective
  rw [Corepresented.pointsEquiv_naturality, pointsEquiv_scalarCutPointsEquiv,
    pointsEquiv_scalarCutPointsEquiv]
  apply Subtype.ext
  exact (congrArg (Matrix.GeneralLinearGroup.scalar n) (Gm.pointsEquiv_naturality _ a x)).trans
    (map_scalar _ _).symm

variable (n R) in
/-- `𝔾_m` is isomorphic to the closed subgroup scheme of scalar matrices of `GL_n`, for nonempty
`n`. -/
def scalarIso :
    (Gm (Spec R)).toGrp ≅ Corepresented.cutGroupScheme (isCutOutBy_scalarIdeal (n := n) (R := R)) :=
  isoOfPoints (scalarCutPointsEquiv n R) scalarCutPointsEquiv_naturality

/-- The scalar torus is the isomorphism onto the scalar matrices followed by the closed subgroup
inclusion. -/
theorem scalarTorus_eq_scalarIso_comp :
    scalarTorus n R = (scalarIso n R).hom ≫ Corepresented.cutHom _ := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv n R T).injective
  rw [pointsEquiv_scalarTorus, Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_cutHom,
    scalarIso, comp_isoOfPoints_hom, pointsEquiv_scalarCutPointsEquiv]
  rfl

variable (n R) in
/-- For nonempty `n`, the scalar torus is a closed subgroup of `GL_n`. -/
theorem isClosedSubgroup_scalarTorus : IsClosedSubgroup (scalarTorus n R) := by
  rw [scalarTorus_eq_scalarIso_comp]
  exact IsClosedSubgroup.iso_comp _ (Corepresented.isClosedSubgroup_cutHom _)

variable (n) in
/-- Over a field and for nonempty `n`, the scalar torus is a central split torus of `GL_n`. -/
theorem isCentralSplitTorus_scalarTorus (k : Type u) [Field k] :
    IsCentralSplitTorus (scalarTorus n (CommRingCat.of k)) :=
  ⟨⟨isSplitTorus_gm, isClosedSubgroup_scalarTorus n _⟩, isCentral_scalarTorus⟩

end Nonempty

/-! #### Block determinant characters of block Levi subgroups -/

section Blocks

open Langlands.GeneralLinear (BlockShape)

variable {N : ℕ} (B : BlockShape N)

/-- The determinant of the `i`-th diagonal block of a block diagonal invertible matrix for the
block shape `B`. -/
def blockDet (i : Fin B.length) (A : Type u) [CommRing A] :
    blockLeviSubgroup A (blockShapeWeight B) →* Aˣ :=
  Matrix.GeneralLinearGroup.det.comp
    ((Pi.evalMonoidHom (fun j => Langlands.GeneralLinear (B.size j) A) i).comp
      ((B.leviEquiv A).symm.toMonoidHom.comp
        (MulEquiv.subgroupCongr (blockLeviSubgroup_blockShapeWeight B A)).toMonoidHom))

/-- The block determinant is the determinant of the `i`-th diagonal block. -/
theorem blockDet_val (i : Fin B.length) (A : Type u) [CommRing A]
    (g : blockLeviSubgroup A (blockShapeWeight B)) :
    (blockDet B i A g : A) =
      Matrix.det (((g : GL (Fin N) A) : Matrix (Fin N) (Fin N) A).submatrix (B.index i) (B.index i)) :=
  rfl

theorem blockDet_map (i : Fin B.length) {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (g : blockLeviSubgroup A (blockShapeWeight B))
    (hg : Matrix.GeneralLinearGroup.map f (g : GL (Fin N) A) ∈
      blockLeviSubgroup A' (blockShapeWeight B)) :
    blockDet B i A' ⟨_, hg⟩ = Units.map f.toMonoidHom (blockDet B i A g) := by
  apply Units.ext
  rw [blockDet_val, Units.coe_map, blockDet_val]
  change _ = f _
  rw [RingHom.map_det]
  rfl

variable (R) in
/-- The `i`-th block determinant on points of the block Levi subgroup scheme. -/
def blockDetPoints (i : Fin B.length) (T : Over (Spec R)) :
    (T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) →* (T ⟶ (Gm (Spec R)).X) :=
  (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
    ((blockDet B i ((algΓ R).obj T).unop).comp
      (Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy _) T).toMonoidHom)

theorem pointsEquiv_blockDetPoints (i : Fin B.length) (T : Over (Spec R))
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    Gm.pointsEquiv (Spec R) T (blockDetPoints R B i T x) =
      blockDet B i ((algΓ R).obj T).unop
        (Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy _) T x) :=
  MulEquiv.apply_symm_apply _ _

theorem blockDetPoints_naturality (i : Fin B.length) {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    blockDetPoints R B i T' (a ≫ x) = a ≫ blockDetPoints R B i T x := by
  apply (Gm.pointsEquiv (Spec R) T').injective
  rw [Gm.pointsEquiv_naturality, pointsEquiv_blockDetPoints, pointsEquiv_blockDetPoints,
    Corepresented.pointsEquiv_naturality]
  exact blockDet_map B i _ _ _

variable (R) in
/-- The `i`-th block determinant character of the block Levi subgroup scheme of `GL_N` attached
to the block shape `B`. -/
def blockDeterminantCharacter (i : Fin B.length) :
    rationalCharacters (blockLeviScheme (Fin N) R (blockShapeWeight B)) :=
  Additive.ofMul (homOfPoints (blockDetPoints R B i) (blockDetPoints_naturality B i))

theorem comp_blockDeterminantCharacter (i : Fin B.length) (T : Over (Spec R))
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    x ≫ (blockDeterminantCharacter R B i).toMul.hom.hom = blockDetPoints R B i T x :=
  comp_homOfPoints (blockDetPoints R B i) (blockDetPoints_naturality B i) T x

/-- On points, the `i`-th block determinant character is the determinant of the `i`-th diagonal
block of the matrix of the point in `GL_N`. -/
theorem characterEval_blockDeterminantCharacter (i : Fin B.length) (T : Over (Spec R))
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    (characterEval (blockDeterminantCharacter R B i) T x : Γ(T.left, ⊤)) =
      Matrix.det (((pointsEquiv (Fin N) R T
        (x ≫ (blockLeviHom (Fin N) R (blockShapeWeight B)).hom.hom) :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)).submatrix (B.index i) (B.index i))) := by
  rw [characterEval_apply, comp_blockDeterminantCharacter, pointsEquiv_blockDetPoints]
  exact congrArg (fun g : GL (Fin N) Γ(T.left, ⊤) =>
    Matrix.det ((g : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)).submatrix (B.index i) (B.index i)))
    (pointsEquiv_cutHom _ x).symm

end Blocks

end GeneralLinear

end Langlands.GroupScheme
