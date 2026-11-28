import Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting
import Langlands.Algebra.NumberFieldBrauerTwoTorsion
import Langlands.GroupScheme.Rational.NumberFieldHigherRankSkewIsotropy
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexNonTypeAQuadraticIsotropy
import Langlands.GroupScheme.Quaternionic.QuaternionicSkewQuadraticComparison
import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationProof

/-! # Isotropy of classical type D from its scalar and quaternionic forms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Matrix Module

namespace Langlands.GroupScheme

open Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

section Quadratic

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] (σ : FirstKindInvolution F D) {n : ℕ}
  (q : σ.QuadraticForms (Fin n))

omit [NumberField F] [FiniteDimensional F D] in
private theorem quadraticWittIndex_pos_of_singular {x : Fin n → D} (hx : x ≠ 0)
    (hz : σ.quadraticValue x q = 0) : 0 < σ.quadraticWittIndex q := by
  let W : Submodule D (Fin n → D) := D ∙ x
  have hW : σ.IsTotallySingular q W := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact σ.quadraticValue_smul_eq_zero a x q hz
  exact (finrank_span_singleton hx).ge.trans hW.finrank_le_quadraticWittIndex

omit [FiniteDimensional F D] in
/-- A nondegenerate quadratic form of rank greater than four over a
one-dimensional division algebra has positive Witt index over a totally
complex number field. -/
theorem Quaternionic.FirstKindInvolution.quadraticWittIndex_pos_of_finrank_one_totallyComplex
    (hF : IsTotallyComplex F) (hD : finrank F D = 1) (hn : 4 < n)
    (hq : σ.IsNondegenerateQuadratic q) : 0 < σ.quadraticWittIndex q := by
  let j := Langlands.Algebra.CentralSimple.algEquivOfFinrankEqOne hD
  have hσ (a : D) : σ a = a := by
    obtain ⟨k, rfl⟩ := j.surjective a
    exact σ.map_algebraMap k
  let τ := FirstKindInvolution.scalar F
  let φ : Matrix (Fin n) (Fin n) D ≃ₐ[F] Matrix (Fin n) (Fin n) F := j.symm.mapMatrix
  have hm (M : Matrix (Fin n) (Fin n) D) : φ (σ.matrix (Fin n) M) = τ.matrix (Fin n) (φ M) := by
    ext i k
    change j.symm (σ (M k i)) = τ (j.symm (M k i))
    rw [hσ, FirstKindInvolution.scalar_apply]
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective (σ.quadraticKernel (Fin n)) q
  let q' : τ.QuadraticForms (Fin n) := Submodule.Quotient.mk (φ Q)
  have hq' : τ.IsNondegenerateQuadratic q' := by
    change IsUnit (τ.polar (Submodule.Quotient.mk (φ Q)))
    rw [FirstKindInvolution.polar_mk, ← hm, ← _root_.map_add]
    exact hq.map φ.toMonoidHom
  obtain ⟨y, hy, hyq⟩ := τ.exists_nonzero_singular_of_quadraticWittIndex_pos q'
    (Langlands.GroupScheme.FirstKindInvolution.scalarQuadraticWittIndex_pos_of_totallyComplex hF q' hq' hn)
  let x : Fin n → D := j ∘ y
  have hx : x ≠ 0 := by
    intro h
    apply hy
    exact funext fun i => j.injective ((congrFun h i).trans j.map_zero.symm)
  apply quadraticWittIndex_pos_of_singular σ _ hx
  rw [FirstKindInvolution.quadraticValue_mk, Submodule.Quotient.mk_eq_zero]
  have hz : τ.sesqForm (φ Q) y y = 0 := by
    change τ.quadraticValue y (Submodule.Quotient.mk (φ Q)) = 0 at hyq
    rw [FirstKindInvolution.scalar_quadraticValue_mk_eq_zero_iff] at hyq
    simpa only [τ, FirstKindInvolution.scalar_sesqForm] using hyq
  have he : j.symm (σ.sesqForm Q x x) = τ.sesqForm (φ Q) y y := by
    simp only [FirstKindInvolution.sesqForm, φ, AlgEquiv.mapMatrix_apply, Matrix.map_apply,
      _root_.map_sum, _root_.map_mul, x, Function.comp_apply, AlgEquiv.symm_apply_apply,
      hσ, τ, FirstKindInvolution.scalar_apply]
  rw [hz, ← j.symm.map_zero] at he
  rw [j.symm.injective he]
  exact Submodule.zero_mem _

variable [Algebra.IsCentral F D]

/-- Local nonsingular isotropic rows for the quaternionic skew Gram form
imply positive Witt index for its corresponding quadratic form in rank at
least four. -/
theorem Quaternionic.FirstKindInvolution.quadraticWittIndex_pos_of_local_skew
    (hdim : finrank F D = 4) (hsym : finrank F σ.symmetricSubspace = 3) (hn : 4 ≤ n)
    (hq : σ.IsNondegenerateQuadratic q)
    (hl : (σ.quaternionConjugation hdim hsym).IsLocallyNonsingularIsotropic
      (σ.conjugationSkewGram q hdim hsym)) :
    0 < σ.quadraticWittIndex q := by
  let H := σ.conjugationSkewGram q hdim hsym
  let τ := σ.quaternionConjugation hdim hsym
  obtain ⟨x, hx, hz⟩ := numberFieldHigherRankSkewIsotropy F D σ hdim hsym (Fin n)
    (by simpa using hn) H (σ.isAntihermitian_conjugationSkewGram q hdim hsym)
    (σ.isUnit_conjugationSkewGram q hdim hsym hq) hl
  have he : τ.sesqForm H x x = τ.sesqForm H 0 0 := by
    rw [hz]
    simp [FirstKindInvolution.sesqForm]
  exact quadraticWittIndex_pos_of_singular σ q hx
    ((σ.quadraticValue_eq_of_conjugationSkewGram_eq hdim hsym q he).trans
      (σ.quadraticValue_zero q))

end Quadratic

private def involutionOppositeEquiv {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
    (σ : FirstKindInvolution F D) : D ≃ₐ[F] Dᵐᵒᵖ where
  toFun x := MulOpposite.op (σ x)
  invFun x := σ x.unop
  left_inv x := σ.apply_apply x
  right_inv x := congrArg MulOpposite.op (σ.apply_apply x.unop)
  map_mul' x y := congrArg MulOpposite.op (σ.map_mul x y)
  map_add' x y := congrArg MulOpposite.op (σ.map_add x y)
  commutes' c := congrArg MulOpposite.op (σ.map_algebraMap c)

/-- Classical type D of rank at least four over a totally complex number
field is isotropic if the quaternionic case of its spin presentation has
local nonsingular skew-isotropic rows. -/
def NumberFieldTotallyComplexTypeDSpinIsotropyReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
      4 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
      (∀ (γ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
        (e a).val + 2 < n → d.star γ a = a) →
      (∀ (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
        [FiniteDimensional F D] (σ : FirstKindInvolution F D)
        (hdim : finrank F D = 4) (hsym : finrank F σ.symmetricSubspace = 3)
        (q : σ.QuadraticForms (Fin n)), σ.IsNondegenerateQuadratic q →
        ∀ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π →
          (σ.quaternionConjugation hdim hsym).IsLocallyNonsingularIsotropic
            (σ.conjugationSkewGram q hdim hsym)) →
      ¬ IsAnisotropic G

theorem numberFieldTotallyComplexTypeDSpinIsotropyReduction :
    NumberFieldTotallyComplexTypeDSpinIsotropyReductionStatement.{u} := by
  intro F _ _ hF G _ _ d n e hn hsc habs hD hstar hl hAni
  obtain ⟨D, _, _, _, _, degree, m, _, hdim, hm, σ, hsym, q, hq, hw, _, π, hπ⟩ :=
    classicalTypeDSpinPresentation F G d n e hn hsc habs hD hstar
  have hdegree : Langlands.CentralSimple.reducedDegree F D = degree := by
    rw [Langlands.CentralSimple.reducedDegree, hdim, pow_two, Nat.sqrt_eq]
  have hs := Langlands.Brauer.numberField_division_reducedDegree_eq_one_or_two_of_equiv_opposite
    F D (involutionOppositeEquiv σ)
  rw [hdegree] at hs
  clear hdegree
  rw [show splitRank G = 0 from hAni] at hw
  have hw0 : σ.quadraticWittIndex q = 0 := by exact_mod_cast hw
  rcases hs with hd | hd
  · subst degree
    have hpos := σ.quadraticWittIndex_pos_of_finrank_one_totallyComplex q hF
      (by simpa using hdim) (show 4 < m by omega) hq
    exact hpos.ne' hw0
  · subst degree
    have hm' : m = n := by omega
    subst m
    have hdim' : finrank F D = 4 := hdim
    have hsym' : finrank F σ.symmetricSubspace = 3 := hsym
    have hpos := σ.quadraticWittIndex_pos_of_local_skew q hdim' hsym' hn hq
      (hl D σ hdim' hsym' q hq π hπ)
    exact hpos.ne' hw0

end Langlands.GroupScheme
