import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates
import Langlands.GroupScheme.Reductive.GeometricReductivityStatement
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple

/-! # Degree-one invariant separation from semisimple rational-point representations -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SemisimpleFixedSeparation

variable {k : Type u} [Field k] {H : Type v} [Group H]
  {V : Type w} [AddCommGroup V] [Module k V]

/-- A semisimple representation admits an invariant functional taking value one
at any prescribed nonzero fixed vector. -/
theorem exists_invariant_form (τ : Representation k H V)
    (hss : τ.IsSemisimpleRepresentation) (v : V) (hv : v ≠ 0)
    (hfix : ∀ g, τ g v = v) :
    ∃ ℓ : Module.Dual k V, ℓ v = 1 ∧ ∀ g x, ℓ (τ g x) = ℓ x := by
  let := hss
  let W : Subrepresentation τ :=
    { toSubmodule := τ.invariants
      apply_mem_toSubmodule := fun g x hx => by simpa only [hx g] using hx }
  obtain ⟨C, hC⟩ := exists_isCompl W
  have hWC : IsCompl W.toSubmodule C.toSubmodule :=
    ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hC.inf_eq_bot),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hC.sup_eq_top)⟩
  let P := W.toSubmodule.projection C.toSubmodule hWC
  have hPfixed (g : H) (x : V) : τ g (P x) = P x :=
    Submodule.projection_apply_mem hWC x g
  have hP (g : H) (x : V) : P (τ g x) = P x := by
    have hCx : τ g (x - P x) ∈ C.toSubmodule :=
      C.apply_mem_toSubmodule g (Submodule.sub_projection_mem hWC x)
    have hx : τ g x = τ g (P x) + τ g (x - P x) := by
      rw [← map_add, add_sub_cancel]
    rw [hx, hPfixed, map_add,
      Submodule.projection_apply_of_mem_right hWC hCx, add_zero]
    exact Submodule.projection_apply_of_mem_left hWC
      (Submodule.projection_apply_mem hWC x)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hv
  refine ⟨f ∘ₗ P, ?_, ?_⟩
  · change f (P v) = 1
    rw [Submodule.projection_apply_of_mem_left hWC hfix, hf]
  · intro g x
    change f (P (τ g x)) = f (P x)
    rw [hP]

end SemisimpleFixedSeparation

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual action of the group of rational points, on the chosen coordinates. -/
def rationalRepresentation (ρ : MatrixRepresentation G n) :
    Representation k (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (n → k) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (n → k)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ.rationalMatrix))

@[simp] theorem rationalRepresentation_apply (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (x : n → k) :
    ρ.rationalRepresentation g x = (ρ.rationalMatrix g : Matrix n n k) *ᵥ x := rfl

/-- Coefficient coordinates of the dual rational representation are inverse transpose. -/
@[simp] theorem dual_rationalMatrix (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ρ.dual.rationalMatrix g = GeneralLinear.matrixContragredient n k (ρ.rationalMatrix g) := by
  change Matrix.GeneralLinearGroup.map _ (ρ.dual.pointMatrix _ g) = _
  rw [dual_pointMatrix, ← GeneralLinear.matrixContragredient_map]
  rfl

/-- The linear coordinate polynomial attached to a row of coefficients. -/
def linearPolynomial (c : n → k) : MvPolynomial n k :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

omit [DecidableEq n] in
/-- Coordinate linear polynomials are homogeneous of degree one. -/
theorem linearPolynomial_isHomogeneous (c : n → k) :
    (linearPolynomial c).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

omit [DecidableEq n] in
/-- Evaluation of a coordinate linear polynomial commutes with every scalar map. -/
theorem eval_linearPolynomial (c : n → k) {A : Type*} [CommRing A]
    (f : k →+* A) (x : n → A) :
    MvPolynomial.eval₂ f x (linearPolynomial c) = (fun i => f (c i)) ⬝ᵥ x := by
  simp [linearPolynomial, dotProduct]

/-- A fixed vector of the dual gives a linear form invariant on every scheme test. -/
theorem invariant_linearPolynomial_of_dual_fixed (ρ : MatrixRepresentation G n)
    (c : n → k) (hc : ρ.dual.IsFixedVector c)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)) :
    MvPolynomial.eval₂ (scalarMap T)
        ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) (linearPolynomial c) =
      MvPolynomial.eval₂ (scalarMap T) x (linearPolynomial c) := by
  rw [eval_linearPolynomial, eval_linearPolynomial]
  have hp := GeneralLinear.matrixContragredient_pairing n (ρ.pointMatrix T g)
    (fun i => scalarMap T (c i)) x
  rw [← dual_pointMatrix, hc T g] at hp
  exact hp

/-- A dual fixed vector pairing nontrivially with `v` separates it by a degree-one
invariant polynomial on all scheme tests. -/
theorem exists_invariant_polynomial_of_dual_fixed (ρ : MatrixRepresentation G n)
    (v c : n → k) (hc : ρ.dual.IsFixedVector c) (hv : c ⬝ᵥ v ≠ 0) :
    ∃ F : MvPolynomial n k, F.IsHomogeneous 1 ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
          MvPolynomial.eval₂ (scalarMap T) x F) ∧
      MvPolynomial.eval v F ≠ 0 := by
  refine ⟨linearPolynomial c, linearPolynomial_isHomogeneous c,
    invariant_linearPolynomial_of_dual_fixed ρ c hc, ?_⟩
  change MvPolynomial.eval₂ (RingHom.id k) v (linearPolynomial c) ≠ 0
  simpa only [eval_linearPolynomial, RingHom.id_apply] using hv

section RationalDetection

variable [IsAlgClosed k] [Smooth G.X.hom]

/-- For smooth groups over algebraically closed fields, rational-point fixedness
of coordinate vectors is equivalent to the original all-test-scheme definition. -/
theorem isFixedVector_iff_rationalRepresentation (ρ : MatrixRepresentation G n)
    (v : n → k) :
    ρ.IsFixedVector v ↔
      ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        ρ.rationalRepresentation g v = v := by
  have : IsSeparated (coefficientSpace n (CommRingCat.of k)).hom := by
    dsimp [coefficientSpace]
    infer_instance
  rw [isFixedVector_iff_isFixed, ρ.schemeAction.isFixed_iff_rationalPoints]
  constructor
  · intro h g
    have he := congrArg coefficientCoordinates (h g)
    simp only [coefficientCoordinates_act, constantCoefficientPoint,
      coefficientCoordinates_coefficientPoint] at he
    let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    have hM : (ρ.pointMatrix _ g).val.map e.toRingHom =
        (ρ.rationalMatrix g).val := rfl
    have hs (a : k) :
        e.toRingHom (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) a) = a :=
      e.apply_symm_apply a
    funext i
    have hi := congrArg e.toRingHom (congrFun he i)
    rw [e.toRingHom.map_mulVec] at hi
    rw [hM] at hi
    simpa only [Function.comp_def, hs, rationalRepresentation_apply] using hi
  · intro h g
    apply coefficientCoordinates_injective
    simp only [coefficientCoordinates_act, constantCoefficientPoint,
      coefficientCoordinates_coefficientPoint]
    rw [← map_rationalMatrix]
    funext i
    let s := scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    have hi := congrArg s
      (congrFun (h g) i)
    change ((ρ.rationalMatrix g).val.map s *ᵥ (s ∘ v)) i = s (v i)
    exact (s.map_mulVec _ _ i).symm.trans hi

/-- Semisimplicity of the actual rational-point representation supplies a fixed
dual vector taking value one on a prescribed nonzero fixed vector. -/
theorem exists_dual_fixed_of_rational_semisimple (ρ : MatrixRepresentation G n)
    (hss : ρ.rationalRepresentation.IsSemisimpleRepresentation)
    (v : n → k) (hv : v ≠ 0) (hfix : ρ.IsFixedVector v) :
    ∃ c : n → k, ρ.dual.IsFixedVector c ∧ c ⬝ᵥ v = 1 := by
  obtain ⟨ℓ, hℓv, hℓ⟩ := SemisimpleFixedSeparation.exists_invariant_form
    ρ.rationalRepresentation hss v hv
    ((isFixedVector_iff_rationalRepresentation ρ v).1 hfix)
  let c := (dotProductEquiv k n).symm ℓ
  have hcℓ (x : n → k) : c ⬝ᵥ x = ℓ x :=
    congrArg (fun f : Module.Dual k (n → k) => f x)
      ((dotProductEquiv k n).apply_symm_apply ℓ)
  refine ⟨c, (isFixedVector_iff_rationalRepresentation ρ.dual c).2 ?_, hcℓ v |>.trans hℓv⟩
  intro g
  funext i
  have hi := hℓ g⁻¹ (Pi.single i 1)
  rw [rationalRepresentation_apply, dual_rationalMatrix,
    GeneralLinear.matrixContragredient_coe]
  have hp : ((ρ.rationalMatrix g)⁻¹ : GL n k).val.transpose *ᵥ c ⬝ᵥ
      Pi.single i 1 = c ⬝ᵥ Pi.single i 1 := by
    calc
      _ = c ⬝ᵥ (((ρ.rationalMatrix g)⁻¹ : GL n k).val *ᵥ Pi.single i 1) := by
        rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
      _ = ℓ (((ρ.rationalMatrix g)⁻¹ : GL n k).val *ᵥ Pi.single i 1) := hcℓ _
      _ = ℓ (Pi.single i 1) := by
        simpa only [rationalRepresentation_apply, map_inv] using hi
      _ = c ⬝ᵥ Pi.single i 1 := (hcℓ _).symm
  simpa using hp

/-- The degree-one implication from complete reducibility to geometric reductivity,
with the semisimplicity input kept explicit. -/
theorem exists_invariant_polynomial_of_rational_semisimple
    (ρ : MatrixRepresentation G n)
    (hss : ρ.rationalRepresentation.IsSemisimpleRepresentation)
    (v : n → k) (hv : v ≠ 0) (hfix : ρ.IsFixedVector v) :
    ∃ F : MvPolynomial n k, F.IsHomogeneous 1 ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
          MvPolynomial.eval₂ (scalarMap T) x F) ∧
      MvPolynomial.eval v F ≠ 0 := by
  obtain ⟨c, hc, hcv⟩ := exists_dual_fixed_of_rational_semisimple ρ hss v hv hfix
  exact exists_invariant_polynomial_of_dual_fixed ρ v c hc (hcv.trans_ne one_ne_zero)

end RationalDetection
end MatrixRepresentation
end Langlands.GroupScheme
