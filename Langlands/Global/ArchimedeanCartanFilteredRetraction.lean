import Langlands.Algebra.FilteredRetractionSymmetrization
import Langlands.Global.ArchimedeanCartanSeparatedSymmetrization
import Langlands.Global.ArchimedeanFilteredInvariantSymmetrization
import Langlands.Global.ArchimedeanEnvelopingInvariantCenter

/-! # Strict filtered comparison for the actual Cartan restriction -/

noncomputable section
universe u w
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open Langlands.Algebra.UniversalEnveloping

variable (K : Type u) [Field K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The genuine complex compact Lie directions inside the whole Lie algebra. -/
def compactComplexDirections : Submodule ℂ (ComplexLieAlgebra K n) :=
  LinearMap.range (compactComplexInclusion K n).toLinearMap

/-- Removing the actual complementary projection leaves an actual compact direction. -/
theorem sub_cartanComplexProjection_mem (X : ComplexLieAlgebra K n) :
    X - cartanComplexInclusion K n (cartanComplexProjection K n X) ∈
      compactComplexDirections K n := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    refine ⟨z ⊗ₜ[ℝ] compactProjection K n X, ?_⟩
    change z ⊗ₜ[ℝ] (compactProjection K n X : RealLieAlgebra K n) =
      z ⊗ₜ[ℝ] X - z ⊗ₜ[ℝ] (cartanComplementProjection K n X : RealLieAlgebra K n)
    rw [← TensorProduct.tmul_sub]
    congr 1
    exact eq_sub_of_add_eq (compactProjection_add_cartanComplementProjection K n X)
  | add X Y hX hY =>
    simpa only [map_add, add_sub_add_comm] using
      (compactComplexDirections K n).add_mem hX hY

/-- The induced symmetric endomorphism is exactly actual restriction followed
by the actual complementary inclusion. -/
theorem symmetricLinearLift_cartanProjection :
    symmetricLinearLift ℂ (ComplexLieAlgebra K n)
        ((cartanComplexInclusion K n).comp (cartanComplexProjection K n)) =
      (cartanSymmetricInclusion K n).comp (cartanSymmetricProjection K n) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro X
  change symmetricLinearLift ℂ (ComplexLieAlgebra K n)
      ((cartanComplexInclusion K n).comp (cartanComplexProjection K n))
      (SymmetricAlgebra.ι ℂ _ X) =
    cartanSymmetricInclusion K n (cartanSymmetricProjection K n (SymmetricAlgebra.ι ℂ _ X))
  simp only [LinearMap.comp_apply, symmetricLinearLift_ι,
    cartanSymmetricProjection_ι, cartanSymmetricInclusion_ι]

/-- The bounded monomial span in the actual complementary symmetric algebra. -/
def cartanSymmetricDegreeFiltration (d : ℕ) :
    Submodule ℂ (CartanSymmetricAlgebra K n) :=
  Submodule.span ℂ {P | ∃ l : List (ComplexCartanComplement K n),
    l.length ≤ d ∧ (l.map (SymmetricAlgebra.ι ℂ _)).prod = P}

/-- The actual inclusion preserves every symmetric monomial bound. -/
theorem cartanSymmetricInclusion_mem_degreeFiltration {d : ℕ}
    {Q : CartanSymmetricAlgebra K n} (hQ : Q ∈ cartanSymmetricDegreeFiltration K n d) :
    cartanSymmetricInclusion K n Q ∈ lieSymmetricDegreeFiltration K n d := by
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨l, hl, rfl⟩ := hQ
    have heq : cartanSymmetricInclusion K n ((l.map (SymmetricAlgebra.ι ℂ _)).prod) =
        ((l.map (cartanComplexInclusion K n)).map (SymmetricAlgebra.ι ℂ _)).prod := by
      simp only [map_list_prod, List.map_map, Function.comp_def, cartanSymmetricInclusion_ι]
    rw [heq]
    exact prod_mem_symmetricDegreeFiltration ℂ (ComplexLieAlgebra K n) _
      (by simpa using hl)
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    simpa only [map_add] using (lieSymmetricDegreeFiltration K n d).add_mem ihP ihQ
  | smul z Q hQ ih =>
    simpa only [map_smul] using (lieSymmetricDegreeFiltration K n d).smul_mem z ih

/-- Actual Cartan restriction preserves every symmetric monomial bound. -/
theorem cartanSymmetricProjection_mem_degreeFiltration {d : ℕ}
    {P : LieSymmetricAlgebra K n} (hP : P ∈ lieSymmetricDegreeFiltration K n d) :
    cartanSymmetricProjection K n P ∈ cartanSymmetricDegreeFiltration K n d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have heq : cartanSymmetricProjection K n ((l.map (SymmetricAlgebra.ι ℂ _)).prod) =
        ((l.map (cartanComplexProjection K n)).map (SymmetricAlgebra.ι ℂ _)).prod := by
      simp only [map_list_prod, List.map_map, Function.comp_def, cartanSymmetricProjection_ι]
    rw [heq]
    exact Submodule.subset_span ⟨l.map (cartanComplexProjection K n),
      by simpa using hl, rfl⟩
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    simpa only [map_add] using (cartanSymmetricDegreeFiltration K n d).add_mem ihP ihQ
  | smul z P hP ih =>
    simpa only [map_smul] using (cartanSymmetricDegreeFiltration K n d).smul_mem z ih

/-- Bounded coefficients, with at most one genuine compact generator on the right. -/
abbrev cartanRestrictionRemainder (d : ℕ) : Submodule ℂ (EnvelopingAlgebra K n) :=
  rightGeneratorRemainder ℂ (ComplexLieAlgebra K n) (compactComplexDirections K n) d

/-- Whole symmetrization and Cartan-restricted symmetrization agree up to
one-lower-degree coefficients with at most one compact generator on the right. -/
theorem lieSymmetrize_sub_cartanRestriction_mem {d : ℕ}
    {P : LieSymmetricAlgebra K n} (hP : P ∈ lieSymmetricDegreeFiltration K n d) :
    lieSymmetricAlgebraSymmetrize K n P -
      cartanSymmetricAlgebraSymmetrize K n (cartanSymmetricProjection K n P) ∈
        cartanRestrictionRemainder K n (d - 1) := by
  have h := symmetricAlgebraSymmetrize_sub_retraction_mem ℂ (ComplexLieAlgebra K n)
    (compactComplexDirections K n)
    ((cartanComplexInclusion K n).comp (cartanComplexProjection K n))
    (sub_cartanComplexProjection_mem K n) hP
  simpa only [symmetricLinearLift_cartanProjection, AlgHom.comp_apply,
    cartanSymmetricAlgebraSymmetrize_apply, lieSymmetricAlgebraSymmetrize] using h

/-- Multiplying a whole symmetric coefficient and an actual complementary
tensor agrees with restricted multiplication up to the strict compact remainder. -/
theorem lieSymmetrize_mul_cartan_sub_restriction_mem {p q : ℕ}
    {P : LieSymmetricAlgebra K n} {Q : CartanSymmetricAlgebra K n}
    (hP : P ∈ lieSymmetricDegreeFiltration K n p)
    (hQ : Q ∈ cartanSymmetricDegreeFiltration K n q) :
    lieSymmetricAlgebraSymmetrize K n P * cartanSymmetricAlgebraSymmetrize K n Q -
      cartanSymmetricAlgebraSymmetrize K n (cartanSymmetricProjection K n P * Q) ∈
        cartanRestrictionRemainder K n (p + q - 1) := by
  have hfixed :
      symmetricLinearLift ℂ (ComplexLieAlgebra K n)
        ((cartanComplexInclusion K n).comp (cartanComplexProjection K n))
        (cartanSymmetricInclusion K n Q) = cartanSymmetricInclusion K n Q := by
    rw [symmetricLinearLift_cartanProjection, AlgHom.comp_apply,
      cartanSymmetricProjection_inclusion]
  have h := symmetricAlgebraSymmetrize_mul_sub_retraction_mem ℂ
    (ComplexLieAlgebra K n) (compactComplexDirections K n)
    ((cartanComplexInclusion K n).comp (cartanComplexProjection K n))
    (sub_cartanComplexProjection_mem K n) hP
    (cartanSymmetricInclusion_mem_degreeFiltration K n hQ) hfixed
  have hmul :
      cartanSymmetricInclusion K n (cartanSymmetricProjection K n P * Q) =
        cartanSymmetricInclusion K n (cartanSymmetricProjection K n P) *
          cartanSymmetricInclusion K n Q :=
    map_mul (cartanSymmetricInclusion K n) _ _
  simpa only [symmetricLinearLift_cartanProjection, AlgHom.comp_apply,
    cartanSymmetricAlgebraSymmetrize_apply, lieSymmetricAlgebraSymmetrize, hmul] using h

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

/-- A genuine compact-stable subspace absorbs the rightmost compact factor. -/
theorem cartanRestrictionRemainder_smul_mem (W : Submodule ℂ V)
    (hW : ∀ X : CompactComplexLieAlgebra K n, ∀ w ∈ W,
      compactEnvelopingGenerator K n X • w ∈ W)
    {d : ℕ} {a : EnvelopingAlgebra K n} (ha : a ∈ cartanRestrictionRemainder K n d)
    {w : V} (hw : w ∈ W) :
    a • w ∈ envelopingDegreeFiltration K n d • W := by
  apply rightGeneratorRemainder_smul_mem ℂ (ComplexLieAlgebra K n)
    (compactComplexDirections K n) W ?_ ha hw
  rintro X ⟨Y, rfl⟩ w hw
  exact hW Y w hw

/-- The actual restriction product error acts in one lower filtered module piece. -/
theorem lieSymmetrize_mul_cartan_action_sub_mem (W : Submodule ℂ V)
    (hW : ∀ X : CompactComplexLieAlgebra K n, ∀ w ∈ W,
      compactEnvelopingGenerator K n X • w ∈ W)
    {p q : ℕ} {P : LieSymmetricAlgebra K n} {Q : CartanSymmetricAlgebra K n}
    (hP : P ∈ lieSymmetricDegreeFiltration K n p)
    (hQ : Q ∈ cartanSymmetricDegreeFiltration K n q) {w : V} (hw : w ∈ W) :
    lieSymmetricAlgebraSymmetrize K n P • (cartanSymmetricAlgebraSymmetrize K n Q • w) -
      cartanSymmetricAlgebraSymmetrize K n (cartanSymmetricProjection K n P * Q) • w ∈
        envelopingDegreeFiltration K n (p + q - 1) • W := by
  simpa only [sub_smul, mul_smul] using cartanRestrictionRemainder_smul_mem K n W hW
    (lieSymmetrize_mul_cartan_sub_restriction_mem K n hP hQ) hw

end Module

variable [NumberField K]

/-- A full-group invariant coefficient acts by its actual central symmetrization,
with the same strict Cartan-restriction remainder. -/
theorem centralSymmetrize_mul_cartan_sub_restriction_mem {p q : ℕ}
    (P : lieSymmetricGroupInvariants K n) {Q : CartanSymmetricAlgebra K n}
    (hP : P.val ∈ lieSymmetricDegreeFiltration K n p)
    (hQ : Q ∈ cartanSymmetricDegreeFiltration K n q) :
    (lieSymmetricGroupInvariantCentralSymmetrize K n P : EnvelopingAlgebra K n) *
        cartanSymmetricAlgebraSymmetrize K n Q -
      cartanSymmetricAlgebraSymmetrize K n
        ((cartanGroupInvariantRestriction K n P).val * Q) ∈
          cartanRestrictionRemainder K n (p + q - 1) :=
  lieSymmetrize_mul_cartan_sub_restriction_mem K n hP hQ

end Langlands.Global.ArchimedeanGL
