import Langlands.GroupScheme.Multiplicative

/-! # Relative Laurent coordinates for the actual multiplicative group scheme -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.Gm

universe u

/-- The Laurent coordinate as a unit, over an arbitrary coefficient ring. -/
def relativeCoordUnit (R : Type u) [CommRing R] : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp [LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add]; simp [LaurentPolynomial.T_zero]

lemma relativeCoordUnit_zpow_val (R : Type u) [CommRing R] (m : ℤ) :
    ((relativeCoordUnit R ^ m : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T m := by
  induction m using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ m ih =>
    rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]
    rfl
  | pred m ih =>
    rw [zpow_sub_one, Units.val_mul, ih, LaurentPolynomial.T_sub]
    rfl

lemma specHomEquiv_specMap (X : Scheme.{u}) {A B : CommRingCat.{u}}
    (f : X ⟶ Spec A) (φ : B ⟶ A) :
    specHomEquiv X B (f ≫ Spec.map φ) = φ ≫ specHomEquiv X A f := by
  change (Scheme.ΓSpecIso B).inv ≫ (f ≫ Spec.map φ).appTop =
    φ ≫ (Scheme.ΓSpecIso A).inv ≫ f.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]

/-- The relative Laurent spectrum with its coefficient structural map. -/
def relativeLaurent (R : CommRingCat.{u}) : Over (Spec R) :=
  Over.mk (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := R))))

/-- The Laurent coordinate pulled back along a map to the relative Laurent spectrum. -/
def relativeUnits {R : CommRingCat.{u}} (T : Over (Spec R))
    (x : T ⟶ relativeLaurent R) : (Γ(T.left, ⊤))ˣ :=
  Units.map (specHomEquiv T.left _ x.left).hom.toMonoidHom (relativeCoordUnit R)

lemma relativeUnits_comp {R : CommRingCat.{u}} {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ relativeLaurent R) :
    relativeUnits T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (relativeUnits T x) := rfl

/-- The relative Laurent map determined by a global unit on a test scheme. -/
def relativeLift {R : CommRingCat.{u}} (T : Over (Spec R)) (a : (Γ(T.left, ⊤))ˣ) :
    T ⟶ relativeLaurent R :=
  Over.homMk
    ((specHomEquiv T.left _).symm
      (CommRingCat.ofHom (LaurentPolynomial.eval₂ (specHomEquiv T.left R T.hom).hom a))) (by
        apply (specHomEquiv T.left R).injective
        dsimp only [relativeLaurent, Over.mk_hom]
        rw [specHomEquiv_specMap, Equiv.apply_symm_apply]
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro r
        exact LaurentPolynomial.eval₂_C _ _ r)

lemma relativeUnits_relativeLift {R : CommRingCat.{u}} (T : Over (Spec R))
    (a : (Γ(T.left, ⊤))ˣ) : relativeUnits T (relativeLift T a) = a := by
  apply Units.ext
  change (specHomEquiv T.left (CommRingCat.of (LaurentPolynomial R))
    ((specHomEquiv T.left _).symm _)) (LaurentPolynomial.T 1) = (a : Γ(T.left, ⊤))
  rw [Equiv.apply_symm_apply]
  simp [LaurentPolynomial.eval₂_T]

lemma relativeLift_relativeUnits {R : CommRingCat.{u}} (T : Over (Spec R))
    (x : T ⟶ relativeLaurent R) : relativeLift T (relativeUnits T x) = x := by
  apply Over.OverMorphism.ext
  apply (specHomEquiv T.left _).injective
  change (specHomEquiv T.left _ ((specHomEquiv T.left _).symm _)) = _
  rw [Equiv.apply_symm_apply]
  apply CommRingCat.hom_ext
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C r) =
      (specHomEquiv T.left _ x.left) (LaurentPolynomial.C r)
    rw [LaurentPolynomial.eval₂_C]
    have h := congrArg (specHomEquiv T.left R) (Over.w x)
    dsimp only [relativeLaurent, Over.mk_hom] at h
    rw [specHomEquiv_specMap] at h
    exact (ConcreteCategory.congr_hom h r).symm
  · intro m
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T m) =
      (specHomEquiv T.left _ x.left) (LaurentPolynomial.T m)
    rw [LaurentPolynomial.eval₂_T, ← relativeCoordUnit_zpow_val R m]
    change ((Units.map _ (relativeCoordUnit R) ^ m : (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) = _
    rw [← map_zpow]
    rfl

/-- Maps into the relative Laurent spectrum are exactly global units. -/
def relativeHomEquiv {R : CommRingCat.{u}} (T : Over (Spec R)) :
    (T ⟶ relativeLaurent R) ≃ (Γ(T.left, ⊤))ˣ where
  toFun := relativeUnits T
  invFun := relativeLift T
  left_inv := relativeLift_relativeUnits T
  right_inv := relativeUnits_relativeLift T

/-- The relative Laurent spectrum represents the same units functor as the existing Gm. -/
def relativeRepresentableBy (R : CommRingCat.{u}) :
    (unitsFunctor (Spec R) ⋙ forget CommGrpCat).RepresentableBy (relativeLaurent R) where
  homEquiv := relativeHomEquiv _
  homEquiv_comp := relativeUnits_comp

/-- The existing pullback Gm is the relative Laurent spectrum, canonically over Spec R. -/
def relativeLaurentIso (R : CommRingCat.{u}) :
    (GroupScheme.Gm (Spec R)).X ≅ relativeLaurent R :=
  (representableBy (Spec R)).uniqueUpToIso (relativeRepresentableBy R)

/-- The canonical comparison preserves the global unit of every test-scheme point. -/
lemma relativeHomEquiv_comp_relativeLaurentIso {R : CommRingCat.{u}}
    (T : Over (Spec R)) (x : T ⟶ (GroupScheme.Gm (Spec R)).X) :
    relativeHomEquiv T (x ≫ (relativeLaurentIso R).hom) = pointsEquiv (Spec R) T x := by
  change relativeUnits T (x ≫ relativeLift _ (homEquiv _ (𝟙 _))) = _
  rw [relativeUnits_comp, relativeUnits_relativeLift]
  rw [pointsEquiv_apply]
  simpa only [Category.comp_id] using (homEquiv_comp x (𝟙 _)).symm

/-- On an affine test scheme, T(1) evaluates to the unit already assigned by Gm. -/
lemma relativeLaurentIso_affinePointsEquiv_val {R A : CommRingCat.{u}}
    (f : Spec A ⟶ Spec R) (x : Over.mk f ⟶ (GroupScheme.Gm (Spec R)).X) :
    (Scheme.ΓSpecIso A).hom
      ((specHomEquiv (Spec A) (CommRingCat.of (LaurentPolynomial R))
        (x ≫ (relativeLaurentIso R).hom).left) (LaurentPolynomial.T 1)) =
      (affinePointsEquiv f x : A) := by
  have h := congrArg (fun a : (Γ(Spec A, ⊤))ˣ => (Scheme.ΓSpecIso A).hom a.val)
    (relativeHomEquiv_comp_relativeLaurentIso (Over.mk f) x)
  exact h

end Langlands.GroupScheme.Gm
