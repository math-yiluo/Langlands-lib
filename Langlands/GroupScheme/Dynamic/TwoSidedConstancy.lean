import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Two-sided orbit extensions into an affine scheme are constant -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TwoSidedConstancy

open AffineLine

/-! ### Algebra -/

/-- Global functions along `Spec.map φ`, through the identifications `Γ(Spec R) ≅ R`. -/
theorem ΓSpecIso_hom_specMap_comp_appTop {R R' : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : R ⟶ R') (M : Spec R ⟶ Y) (g : Γ(Y, ⊤)) :
    (Scheme.ΓSpecIso R').hom ((Spec.map φ ≫ M).appTop g) =
      φ ((Scheme.ΓSpecIso R).hom (M.appTop g)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

variable (A : CommRingCat.{u})

/-- Evaluation `A[X, X⁻¹] ⟶ A` at `X = 1`. -/
abbrev evalOneHom : CommRingCat.of (LaurentPolynomial A) ⟶ A :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id A) 1)

theorem polynomialC_toLaurent_evalOneHom :
    polynomialC A ≫ polynomialToLaurent A ≫ evalOneHom A = 𝟙 A := by
  ext a
  simp [Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C]

/-! ### Inversion and the unit point on the Laurent scheme -/

variable {A} {S : Scheme.{u}} (f : Spec A ⟶ S)

/-- The unit point `X = 1` of `Spec A[X, X⁻¹]` over `S`. -/
def unitPointLaurent : Over.mk f ⟶ laurentScheme f :=
  Over.homMk (Spec.map (evalOneHom A)) (by
    change Spec.map (evalOneHom A) ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) ≫ f = f
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, polynomialC_toLaurent_evalOneHom,
      Spec.map_id, Category.id_comp])

/-- The unit point of the Laurent scheme is the unit section of `𝔾ₘ`. -/
theorem unitPointLaurent_comp_laurentPoint :
    unitPointLaurent f ≫ laurentPoint f = lift (𝟙 _) (toUnit _ ≫ η[(Gm S).X]) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, laurentPoint, lift_fst, lift_fst]
    apply Over.OverMorphism.ext
    change Spec.map (evalOneHom A) ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc, polynomialC_toLaurent_evalOneHom,
      Spec.map_id]
  · rw [Category.assoc, laurentPoint, lift_snd, lift_snd]
    apply (Gm.pointsEquiv _ _).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    change _ = Gm.pointsEquiv _ _ 1
    rw [map_one]
    apply Units.ext
    change (Spec.map (evalOneHom A)).appTop
      ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)) = 1
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

/-! ### Two-sided constancy -/

/-- **Two-sided constancy.** Let `o` be a morphism from `𝔾ₘ` (over `Spec A`) to an affine
scheme `V`. If `o` extends over `𝔸¹`, and `o` composed with inversion also extends over `𝔸¹`,
then the value at `0` of the first extension equals the value of `o` at `1`. (A Laurent
polynomial in both `A[s]` and `A[s⁻¹]` is constant.) -/
theorem evalZero_eq_of_twoSided {V : Over (Spec A)} [IsAffine V.left]
    (o : Over.mk (𝟙 (Spec A)) ⊗ (Gm (Spec A)).X ⟶ V)
    (e₀ eInf : Over.mk (𝟙 (Spec A)) ⊗ AffineLine.scheme (Spec A) ⟶ V)
    (h₀ : Over.mk (𝟙 (Spec A)) ◁ AffineLine.unitInclusion (Spec A) ≫ e₀ = o)
    (hInf : Over.mk (𝟙 (Spec A)) ◁ AffineLine.unitInclusion (Spec A) ≫ eInf =
      Over.mk (𝟙 (Spec A)) ◁ (CommGroupScheme.groupHom (Gm.powerHom (Spec A) (-1))).hom.hom ≫ o) :
    Dynamic.evalZero e₀ =
      lift (𝟙 _) (toUnit _ ≫ η[(Gm (Spec A)).X]) ≫ o := by
  have r1 := laurentInclusion_comp_of_whiskerLeft (𝟙 (Spec A)) h₀
  have r2 := laurentInclusion_comp_of_whiskerLeft (𝟙 (Spec A)) hInf
  rw [← Category.assoc (laurentPoint _), ← AffineLine.laurentInvert_comp_laurentPoint,
    Category.assoc] at r2
  have hz : Dynamic.evalZero e₀ =
      polynomialZero (𝟙 (Spec A)) ≫ polynomialPoint (𝟙 (Spec A)) ≫ e₀ := by
    rw [← evalZero_polynomialPointInv, ← Category.assoc, polynomialPointInv_comp_polynomialPoint,
      Category.id_comp]
  rw [hz, ← unitPointLaurent_comp_laurentPoint, Category.assoc]
  have r1' : Spec.map (polynomialToLaurent A) ≫ (polynomialPoint (𝟙 (Spec A)) ≫ e₀).left =
      (laurentPoint (𝟙 (Spec A)) ≫ o).left :=
    congrArg CommaMorphism.left r1
  have r2' : Spec.map (polynomialToLaurent A) ≫ (polynomialPoint (𝟙 (Spec A)) ≫ eInf).left =
      Spec.map AffineLine.laurentInvertRing ≫ (laurentPoint (𝟙 (Spec A)) ≫ o).left :=
    congrArg CommaMorphism.left r2
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  apply ext_of_isAffine
  ext g
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1
  change (Scheme.ΓSpecIso A).hom ((Spec.map (polynomialEvalZero A) ≫
      (polynomialPoint (𝟙 (Spec A)) ≫ e₀).left).appTop g) =
    (Scheme.ΓSpecIso A).hom ((Spec.map (evalOneHom A) ≫
      (laurentPoint (𝟙 (Spec A)) ≫ o).left).appTop g)
  rw [ΓSpecIso_hom_specMap_comp_appTop, ΓSpecIso_hom_specMap_comp_appTop]
  -- The polynomial of `e₀`, the Laurent polynomial of `o`, and the polynomial of `eInf`.
  set a := (Scheme.ΓSpecIso _).hom ((polynomialPoint (𝟙 (Spec A)) ≫ e₀).left.appTop g)
  set b := (Scheme.ΓSpecIso _).hom ((laurentPoint (𝟙 (Spec A)) ≫ o).left.appTop g)
  set c := (Scheme.ΓSpecIso _).hom ((polynomialPoint (𝟙 (Spec A)) ≫ eInf).left.appTop g)
  have hab : Polynomial.toLaurent a = b := by
    have := ΓSpecIso_hom_specMap_comp_appTop (polynomialToLaurent A)
      (polynomialPoint (𝟙 (Spec A)) ≫ e₀).left g
    change _ = Polynomial.toLaurent a at this
    rw [← this, r1']
  have hcb : Polynomial.toLaurent c = LaurentPolynomial.invert b := by
    have := ΓSpecIso_hom_specMap_comp_appTop (polynomialToLaurent A)
      (polynomialPoint (𝟙 (Spec A)) ≫ eInf).left g
    change _ = Polynomial.toLaurent c at this
    rw [← this]
    have h2 := ΓSpecIso_hom_specMap_comp_appTop (AffineLine.laurentInvertRing (A := A))
      (laurentPoint (𝟙 (Spec A)) ≫ o).left g
    change _ = LaurentPolynomial.invert b at h2
    rw [← h2, r2']
  have ha : a = Polynomial.C (a.eval 0) := by
    apply AffineLine.polynomial_eq_C_eval_zero_of_invert (p := c)
    rw [hcb, hab]
    exact (LaurentPolynomial.ext fun n ↦ by
      rw [LaurentPolynomial.invert_apply, LaurentPolynomial.invert_apply, neg_neg]).symm
  change Polynomial.eval 0 a = LaurentPolynomial.eval₂ (RingHom.id A) 1 b
  rw [← hab, ha]
  simp [Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C]

end Langlands.GroupScheme.TwoSidedConstancy
