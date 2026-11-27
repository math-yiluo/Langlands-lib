import Langlands.Global.AdelicWeakConstantTermEigenReduction
import Langlands.Global.AdelicSplitComponentShifts

/-! # Split-component translates of weak constant terms -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints HarishChandraSchwartz

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "Param(" J ")" => ComplexCharacterParameter F (fam.P J)

attribute [local instance] positiveSplitComponentCommGroup

private theorem orbitSpan_le_comap (J : Idx) (f : Fun) (a : fam.positiveSplitComponent J) :
    fam.splitComponentOrbitSpan J f ≤
      (fam.splitComponentOrbitSpan J f).comap (fam.splitComponentRepresentation J a) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  change fam.splitComponentRepresentation J a (fam.splitComponentRepresentation J b f) ∈
    fam.splitComponentOrbitSpan J f
  rw [← Module.End.mul_apply, ← map_mul]
  exact Submodule.subset_span ⟨a * b, rfl⟩

private theorem mem_own_orbitSpan (J : Idx) (f : Fun) :
    f ∈ fam.splitComponentOrbitSpan J f :=
  Submodule.subset_span ⟨1, by simp⟩

/-- Every component of a finite exponent expansion lies in the span of the split-component
translates of its sum. -/
theorem exponentComponent_mem_splitComponentOrbitSpan (J : Idx)
    {s : Finset (Param(J))} {c : Param(J) → Fun} (h : ∀ lam ∈ s, fam.HasExponent J lam (c lam))
    (lam : Param(J)) (hlam : lam ∈ s) :
    c lam ∈ fam.splitComponentOrbitSpan J (∑ mu ∈ s, c mu) := by
  let f : Fun := ∑ mu ∈ s, c mu
  let W := fam.splitComponentOrbitSpan J f
  let T := fam.splitComponentRepresentation J
  let R := T.quotient W (fam.orbitSpan_le_comap J f)
  let χ (p : Param(J)) (b : fam.positiveSplitComponent J) :=
    parameterPower F (fam.P J) (p + halfModulusParameter F (fam.P J)) b.val
  have hχ : Function.Injective χ := by
    have hi := (eisensteinPositiveParameters F G (fam.P J) (fam.M J) (fam.A J) (fam.p J) (fam.l J)
      (fam.a J) ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩).2
    intro p q hp
    exact add_right_cancel (hi hp)
  have hGen (p : Param(J)) (hp : p ∈ s) : W.mkQ (c p) ∈ jointGenEigenspace R (χ p) := by
    have hGen₀ : c p ∈ jointGenEigenspace T (χ p) :=
      fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J
        ((fam.hasExponent_iff J p _).mp (h p hp))
    apply mem_jointGenEigenspace.mpr
    intro a
    obtain ⟨m, hm⟩ := (mem_jointGenEigenspace.mp hGen₀) a
    have hpow (k : ℕ) :
        ((R a - χ p a • 1) ^ k) (W.mkQ (c p)) = W.mkQ (((T a - χ p a • 1) ^ k) (c p)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
        rfl
    exact ⟨m, by rw [hpow, hm, map_zero]⟩
  have hsum : ∑ p ∈ s, W.mkQ (c p) = 0 := by
    rw [← map_sum]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (fam.mem_own_orbitSpan J f)
  exact (Submodule.Quotient.mk_eq_zero _).mp
    ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      ((iSupIndep_jointGenEigenspace R).comp hχ) s _ hGen hsum lam hlam)

/-- Span membership is equivalent to being obtained by one complex group-algebra operator. -/
theorem mem_splitComponentOrbitSpan_iff_exists_shift (J : Idx) (f w : Fun) :
    w ∈ fam.splitComponentOrbitSpan J f ↔
      ∃ D : MonoidAlgebra ℂ (fam.positiveSplitComponent J), fam.shiftAlgHom J D f = w := by
  let L := (LinearMap.applyₗ (R := ℂ) f).comp (fam.shiftAlgHom J).toLinearMap
  change w ∈ fam.splitComponentOrbitSpan J f ↔ w ∈ LinearMap.range L
  suffices fam.splitComponentOrbitSpan J f = LinearMap.range L by rw [this]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨MonoidAlgebra.of ℂ _ a, fam.shiftAlgHom_of J a f⟩
  · rintro _ ⟨D, rfl⟩
    change fam.shiftAlgHom J D f ∈ fam.splitComponentOrbitSpan J f
    exact fam.shiftAlgHom_mem _ (fun a _ hv => fam.orbitSpan_le_comap J f a hv) D f
      (fam.mem_own_orbitSpan J f)

/-- The orbit span of a member of a split-component orbit span is contained in that span. -/
theorem splitComponentOrbitSpan_le_of_mem (J : Idx) {f w : Fun}
    (hw : w ∈ fam.splitComponentOrbitSpan J f) :
    fam.splitComponentOrbitSpan J w ≤ fam.splitComponentOrbitSpan J f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact fam.orbitSpan_le_comap J f a hw

variable {N d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {rho : MatrixRepresentation G (Fin N)}

/-- A weak term lies in the split-component orbit span of its ordinary constant term. -/
theorem IsWeakConstantTerm.mem_splitComponentOrbitSpan {J : Idx} {f w : Fun}
    (h : fam.IsWeakConstantTerm hsmooth Kinf rho J f w) :
    w ∈ fam.splitComponentOrbitSpan J (fam.constantTerm J f) := by
  classical
  obtain ⟨s, c, hDec, rfl⟩ := h
  rw [hDec.sum_eq, unitaryExponentSum]
  exact (fam.splitComponentOrbitSpan J _).sum_mem fun mu hmu =>
    fam.exponentComponent_mem_splitComponentOrbitSpan J hDec.exponent mu (Finset.mem_filter.mp hmu).1

/-- The split-component span of an automorphic function consists of automorphic functions on
the same parabolic quotient. -/
theorem isAutomorphicOn_of_mem_splitComponentOrbitSpan (J : Idx) {f w : Fun}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho J f) (hw : w ∈ fam.splitComponentOrbitSpan J f) :
    fam.IsAutomorphicOn hsmooth Kinf rho J w := by
  obtain ⟨D, rfl⟩ := (fam.mem_splitComponentOrbitSpan_iff_exists_shift J f w).mp hw
  exact IsAutomorphicOn.shiftAlgHom fam hsmooth Kinf rho le_rfl hf D

/-- The smaller ordinary constant term of a split-orbit vector belongs to the smaller
split-component orbit span of the original ordinary constant term. -/
theorem constantTerm_mem_splitComponentOrbitSpan {Q P : Idx} (hQP : Q ≤ P) {f w : Fun}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho P f) (hw : w ∈ fam.splitComponentOrbitSpan P f) :
    fam.constantTerm Q w ∈ fam.splitComponentOrbitSpan Q (fam.constantTerm Q f) := by
  obtain ⟨D, rfl⟩ := (fam.mem_splitComponentOrbitSpan_iff_exists_shift P f w).mp hw
  rw [fam.constantTerm_shiftAlgHom hQP
    (fam.mem_radicalIntegrableSubmodule_of_automorphicOn hsmooth Kinf rho hQP le_rfl hf)]
  let u := fam.constantTerm Q f
  exact fam.shiftAlgHom_mem (fam.splitComponentOrbitSpan Q u)
    (fun a v hv => by
      rw [← fam.unnormalizedAction_splitLift hQP a]
      exact fam.orbitSpan_le_comap Q u (fam.splitLift hQP a) hv)
    D u (fam.mem_own_orbitSpan Q u)

/-- For nested parabolics, a group-algebra operator of the larger split component commutes
with taking the smaller weak constant term. -/
theorem IsWeakConstantTerm.shiftAlgHom_of_le {Q P : Idx} (hQP : Q ≤ P) {f w : Fun}
    (h : fam.IsWeakConstantTerm hsmooth Kinf rho Q f w)
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho P f)
    (D : MonoidAlgebra ℂ (fam.positiveSplitComponent P)) :
    fam.IsWeakConstantTerm hsmooth Kinf rho Q (fam.shiftAlgHom P D f) (fam.shiftAlgHom P D w) := by
  classical
  obtain ⟨s, c, hDec, rfl⟩ := h
  refine ⟨s, fun lam => fam.shiftAlgHom P D (c lam), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [fam.constantTerm_shiftAlgHom hQP
      (fam.mem_radicalIntegrableSubmodule_of_automorphicOn hsmooth Kinf rho hQP le_rfl hf),
      hDec.sum_eq, map_sum]
  · exact fun lam hlam => IsAutomorphicOn.shiftAlgHom fam hsmooth Kinf rho hQP (hDec.automorphic lam hlam) D
  · intro lam hlam
    apply (fam.hasExponent_iff Q lam _).mpr
    exact HasUnnormalizedExponent.shiftAlgHom fam hQP
      ((fam.hasExponent_iff Q lam _).mp (hDec.exponent lam hlam)) D
  · simp only [unitaryExponentSum, map_sum]

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

/-- Each component of a finite normalized exponent sum is a linear combination of
split-component translates of the sum. -/
def AdelicExponentOrbitSpanStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    (s : Finset (ComplexCharacterParameter F (fam.P J)))
    (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
    (∀ lam ∈ s, fam.HasExponent J lam (c lam)) →
      ∀ lam ∈ s, c lam ∈ fam.splitComponentOrbitSpan J (∑ mu ∈ s, c mu)

theorem adelicExponentOrbitSpan : AdelicExponentOrbitSpanStatement := by
  intro F _ _ G _ _ _ fam J s c h lam hlam
  exact fam.exponentComponent_mem_splitComponentOrbitSpan J h lam hlam

end Langlands.Global
