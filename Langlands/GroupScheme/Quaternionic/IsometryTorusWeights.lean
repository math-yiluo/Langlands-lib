import Langlands.GroupScheme.Quaternionic.IsometryRowAction
import Langlands.GroupScheme.Quaternionic.QuadraticWeightSpaces
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection

/-! # Torus weights in the actual quaternionic row action -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]

/-- The faithful coefficient representation induced by inverse right multiplication on matrices. -/
def isometryRegularRepresentation (q : σ.QuadraticForms n) :
    MatrixRepresentation (σ.isometryGroup q) (Fin (Module.finrank K (Matrix n n D))) :=
  σ.isometryGroupι q ≫ FiniteAlgebraUnits.rightRegularHom (Module.finBasis K (Matrix n n D))

/-- A regular coefficient eigenvector gives the same eigenvalue on each of its actual rows. -/
theorem isometryRowAction_of_regular_eigenvector (q : σ.QuadraticForms n)
    (a : (σ.isometryGroup q).affinePoints (CommAlgCat.of K K)) (M : Matrix n n D) (c : K)
    (h : ((σ.isometryRegularRepresentation q).affineMatrix (CommAlgCat.of K K) a :
        Matrix _ _ K) *ᵥ (Module.finBasis K (Matrix n n D)).equivFun M =
      c • (Module.finBasis K (Matrix n n D)).equivFun M) (r : n) :
    σ.isometryRowAction q a (M r) = c • M r := by
  let b := Module.finBasis K (Matrix n n D)
  have he := FiniteAlgebraUnits.rightRegularHom_affine_action b
    (a ≫ (σ.isometryGroupι q).hom.hom) M
  have hh : M * (σ.isometryMatrixPoint q a⁻¹ : Matrix n n D) = c • M := by
    apply b.equivFun.injective
    rw [b.equivFun.map_smul, (σ.isometryMatrixPoint q).map_inv]
    change b.equivFun (M * Algebra.TensorProduct.lid K (Matrix n n D)
      ((σ.isometryAffineUnits q a)⁻¹ : (K ⊗[K] Matrix n n D)ˣ)) = _
    exact he.symm.trans h
  funext j
  exact congrFun (congrFun hh r) j

variable (I : Type u) [Fintype I] [DecidableEq I]

/-- The actual row operators restricted to rational unit coordinates of a split torus. -/
def torusRowAction (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (t : I → Kˣ) : Module.End D (n → D) :=
  σ.isometryRowAction q ((splitTorus.algebraPointsEquiv I K).symm t ≫ i.hom.hom)

omit [DecidableEq I] in
/-- A nonzero regular eigenvector supplies a nonzero division-algebra row weight space. -/
theorem scalarWeightSpace_ne_bot_of_regular_eigenvector (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (m : I → ℤ) (v : Fin (Module.finrank K (Matrix n n D)) → K) (hv : v ≠ 0)
    (he : ∀ t : I → Kˣ,
      (GeneralLinear.CocharacterDiagonal.matrixAt I (i ≫ σ.isometryRegularRepresentation q) t :
        Matrix _ _ K) *ᵥ v = splitTorus.rationalMonomial I m t • v) :
    scalarWeightSpace (σ.torusRowAction I q i) (splitTorus.rationalMonomial I m) ≠ ⊥ := by
  let b := Module.finBasis K (Matrix n n D)
  let M := b.equivFun.symm v
  have hM : M ≠ 0 := by
    intro hM
    apply hv
    have heq : b.equivFun M = 0 := by rw [hM, b.equivFun.map_zero]
    exact (b.equivFun.apply_symm_apply v).symm.trans heq
  obtain ⟨r, hr⟩ : ∃ r, M r ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hM (funext hn)
  apply (scalarWeightSpace (σ.torusRowAction I q i) (splitTorus.rationalMonomial I m)).ne_bot_iff.mpr
  refine ⟨M r, ?_, hr⟩
  intro t
  apply σ.isometryRowAction_of_regular_eigenvector q _ M _
  have ht := he t
  change ((σ.isometryRegularRepresentation q).affineMatrix (CommAlgCat.of K K)
    ((splitTorus.algebraPointsEquiv I K).symm t ≫ i.hom.hom) :
      Matrix (Fin (Module.finrank K (Matrix n n D))) (Fin (Module.finrank K (Matrix n n D))) K) *ᵥ v = _ at ht
  simpa only [M, b, LinearEquiv.apply_symm_apply] using ht

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.splitTorus

variable {K : Type u} [Field K] [Infinite K]
  (I : Type u) [Fintype I] [DecidableEq I]

omit [Infinite K] [DecidableEq I] in
/-- Addition of exponents multiplies the corresponding rational scalar weights. -/
theorem rationalMonomial_add_apply (m n : I → ℤ) (t : I → Kˣ) :
    rationalMonomial I (m + n) t = rationalMonomial I m t * rationalMonomial I n t := by
  change (exponentValue I t (Multiplicative.ofAdd m * Multiplicative.ofAdd n) : K) = _
  rw [map_mul, Units.val_mul]
  rfl

/-- A nonzero sum of integral weights has nontrivial product at some rational point. -/
theorem exists_rationalMonomial_mul_ne_one {m n : I → ℤ} (h : m + n ≠ 0) :
    ∃ t : I → Kˣ, rationalMonomial I m t * rationalMonomial I n t ≠ 1 := by
  by_contra hn
  push Not at hn
  apply h
  apply rationalMonomial_injective (k := K) I
  apply MonoidHom.ext
  intro t
  rw [rationalMonomial_add_apply, hn]
  simp [rationalMonomial, exponentValue]

/-- The square of a nonzero integral weight is nontrivial at some rational point. -/
theorem exists_rationalMonomial_sq_ne_one {m : I → ℤ} (h : m ≠ 0) :
    ∃ t : I → Kˣ, rationalMonomial I m t * rationalMonomial I m t ≠ 1 := by
  apply exists_rationalMonomial_mul_ne_one I
  intro he
  apply h
  funext j
  have hj := congrFun he j
  change m j + m j = 0 at hj
  change m j = 0
  omega

end Langlands.GroupScheme.splitTorus

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]
  (I : Type u) [Fintype I] [DecidableEq I]

/-- At Witt index one, distinct nonzero occurring torus weights must be opposites. -/
theorem eq_neg_of_scalarWeightSpace_ne_bot (q : σ.QuadraticForms n)
    (hq : σ.quadraticWittIndex q = 1)
    (ρ : (I → Kˣ) → Module.End D (n → D))
    (hρ : ∀ t z, σ.quadraticValue (ρ t z) q = σ.quadraticValue z q)
    {m p : I → ℤ} (hm : m ≠ 0) (hp : p ≠ 0) (hne : m ≠ p)
    (hWm : scalarWeightSpace ρ (splitTorus.rationalMonomial I m) ≠ ⊥)
    (hWp : scalarWeightSpace ρ (splitTorus.rationalMonomial I p) ≠ ⊥) : p = -m := by
  by_contra hn
  have hsum : m + p ≠ 0 := by
    intro he
    apply hn
    funext j
    have hj := congrFun he j
    change m j + p j = 0 at hj
    change p j = -m j
    omega
  have hfun : (splitTorus.rationalMonomial I m : (I → Kˣ) → K) ≠
      splitTorus.rationalMonomial I p := by
    intro he
    apply hne
    apply splitTorus.rationalMonomial_injective (k := K) I
    exact MonoidHom.ext (congrFun he)
  have hb := two_le_quadraticWittIndex_of_scalarWeightSpaces q hρ _ _ hfun
    (splitTorus.exists_rationalMonomial_sq_ne_one I hm)
    (splitTorus.exists_rationalMonomial_sq_ne_one I hp)
    (splitTorus.exists_rationalMonomial_mul_ne_one I hsum) hWm hWp
  omega

/-- Every family of occurring weights is contained in zero and one opposite pair at Witt index one. -/
theorem exists_weight_trichotomy (q : σ.QuadraticForms n)
    (hq : σ.quadraticWittIndex q = 1)
    (ρ : (I → Kˣ) → Module.End D (n → D))
    (hρ : ∀ t z, σ.quadraticValue (ρ t z) q = σ.quadraticValue z q)
    {J : Type*} (w : J → (I → ℤ))
    (hw : ∀ j, scalarWeightSpace ρ (splitTorus.rationalMonomial I (w j)) ≠ ⊥) :
    ∃ m : I → ℤ, ∀ j, w j = 0 ∨ w j = m ∨ w j = -m := by
  classical
  by_cases hz : ∀ j, w j = 0
  · exact ⟨0, fun j => Or.inl (hz j)⟩
  · push Not at hz
    obtain ⟨j, hj⟩ := hz
    refine ⟨w j, fun k => ?_⟩
    by_cases hk : w k = 0
    · exact Or.inl hk
    by_cases he : w k = w j
    · exact Or.inr (Or.inl he)
    exact Or.inr (Or.inr (σ.eq_neg_of_scalarWeightSpace_ne_bot I q hq ρ hρ
      hj hk (Ne.symm he) (hw j) (hw k)))

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
