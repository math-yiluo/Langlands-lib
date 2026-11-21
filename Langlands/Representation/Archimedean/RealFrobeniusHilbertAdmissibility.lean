import Langlands.Representation.Archimedean.RealFrobeniusCompactRecovery

/-! # Irreducibility and compact admissibility of the Frobenius Hilbert closure -/

noncomputable section

open Filter MeasureTheory
open scoped Matrix Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open OrthogonalFinitePolynomial RealPrincipalSeriesDuality

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] measurableSpaceK borelSpaceK

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "K" => unitaryCompact ℝ n
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)

local notation "W" => (frobeniusClosure hgk hℓ : Type)
local notation "R" => frobeniusClosureRepresentation hgk hℓ
local notation "B" => frobeniusHilbert hgk hℓ

private theorem mem_of_hasDerivAt_of_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {P : Submodule ℂ H} (hP : IsClosed (P : Set H))
    {f : ℝ → H} {v : H} {t : ℝ} (hf : HasDerivAt f v t) (h : ∀ s, f s ∈ P) : v ∈ P := by
  have : CompleteSpace P := hP.isComplete.completeSpace_coe
  let Q := P.starProjection.restrictScalars ℝ
  have heq : (fun s => Q (f s)) = f :=
    funext fun s => P.starProjection_mem_subspace_eq_self ⟨f s, h s⟩
  have hd : HasDerivAt (fun s => Q (f s)) (Q v) t := Q.hasFDerivAt.comp_hasDerivAt t hf
  rw [heq] at hd
  rw [← hd.unique hf]
  exact P.starProjection_apply_mem v

/-- Irreducibility of a real algebraic GK module gives topological irreducibility of its
Frobenius Hilbert closure. -/
theorem isTopologicallyIrreducible_frobeniusClosureRepresentation
    (hirr : IsIrreducibleGKModule ρ π) (h₀ : ℓ ≠ 0) :
    IsTopologicallyIrreducible (E := W) R := by
  have : Nontrivial V := hirr.1
  refine ⟨(frobeniusClosureMap_injective hgk hℓ hirr h₀).nontrivial, ?_⟩
  intro P hP hPstable
  let U := P.map (frobeniusClosure hgk hℓ).subtype
  have hUc : IsClosed (U : Set (Hilbert a e)) := by
    rw [Submodule.map_coe]
    exact (isClosed_frobeniusClosure hgk hℓ).isClosedEmbedding_subtypeVal.isClosedMap _ hP
  have hUstable (g : GL) (x : Hilbert a e) (hx : x ∈ U) : representation a e g x ∈ U := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨R g y, hPstable g y hy, rfl⟩
  let Z := U.comap B
  have hK (k : O) (v : V) (hv : v ∈ Z) : ρ k v ∈ Z := by
    change B (ρ k v) ∈ U
    have h := hUstable (Unitary.toUnits k) (B v) hv
    change representation a e ((orthogonalCompactEquiv n k : K) : GL) (B v) ∈ U at h
    rw [representation_frobeniusHilbert_compact hgk hℓ] at h
    exact h
  have hLie (X : ℂ ⊗[ℝ] Mat) (v : V) (hv : v ∈ Z) : π X v ∈ Z := by
    refine TensorProduct.inductionOn (motive := fun X => π X v ∈ Z) X ?_ ?_
    · intro c Y
      have hc : c ⊗ₜ[ℝ] Y = c • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, LinearMap.smul_apply]
      refine Z.smul_mem c ?_
      exact mem_of_hasDerivAt_of_mem hUc (hasDerivAt_exponential_frobeniusHilbert_zero hgk hℓ Y v)
        (fun t => hUstable (matrixExpUnit n (t • Y)) (B v) hv)
    · intro X Y hX hY
      rw [map_add, LinearMap.add_apply]
      exact Z.add_mem hX hY
  rcases hirr.2 Z hK hLie with hZ | hZ
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have hxU : (x : Hilbert a e) ∈ U := ⟨x, hx, rfl⟩
    have hu : Continuous (Unitary.toUnits : O → GL) :=
      continuous_subtype_val.comp (continuous_orthogonalCompactEquiv (n := n))
    have hIn : Continuous (fun k : O => (Unitary.toUnits k, (x : Hilbert a e))) :=
      hu.prodMk continuous_const
    have h := (isContinuousRepresentation a e).comp hIn
    let f : C(O, Hilbert a e) := ⟨fun k => representation a e (Unitary.toUnits k) x, h⟩
    have havg (φ : C(O, ℂ)) (hφ : φ ∈ polynomialStar n) :
        (∫ k, φ k • f k ∂haarOrthogonal n) ∈ (⊥ : Submodule ℂ (Hilbert a e)) := by
      change orthogonalAverage a e φ x ∈ (⊥ : Submodule ℂ (Hilbert a e))
      obtain ⟨v, hv⟩ := orthogonalAverage_mem_frobeniusRange hgk hℓ hφ x.2
      have hU := orthogonalAverage_mem φ hUc (fun k => hUstable (Unitary.toUnits k) x hxU)
      rw [← hv] at hU ⊢
      have hvZ : v ∈ Z := hU
      rw [hZ, Submodule.mem_bot] at hvZ
      simp [hvZ]
    have hmem := mem_closedSubmodule_of_polynomial_integrals_mem (E := Hilbert a e)
      (haarOrthogonal n) f (isClosed_singleton (x := (0 : Hilbert a e))) havg 1
    have h1 : f 1 = (x : Hilbert a e) := by
      change representation a e (Unitary.toUnits (1 : O)) x = x.1
      simp
    rw [h1, Submodule.mem_bot] at hmem
    simpa only [Submodule.mem_bot] using (Subtype.ext hmem : x = 0)
  · right
    apply le_antisymm le_top
    intro x _
    have hle : Set.range B ⊆ (U : Set (Hilbert a e)) := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ Z := by rw [hZ]; trivial
      exact hv
    obtain ⟨y, hy, he⟩ := closure_minimal hle hUc x.2
    exact (Subtype.ext he : y = x) ▸ hy

variable (d : ℕ) (τ : unitaryCompact ℝ n →* Matrix (Fin d) (Fin d) ℂ)

local notation "J" => intertwiners (E := W) R (unitaryCompact ℝ n) d τ

private theorem hilbertIntertwiner_mem_frobeniusRange (T : J) (x : Fin d → ℂ) :
    (T.1 x : Hilbert a e) ∈ LinearMap.range B := by
  let A := (frobeniusClosure hgk hℓ).subtype.comp T.1
  have hle : Submodule.span ℂ (Set.range fun k : O => representation a e (Unitary.toUnits k) (A x)) ≤
      LinearMap.range A := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨τ (orthogonalCompactEquiv n k) *ᵥ x, ?_⟩
    exact congrArg Subtype.val (T.2 (orthogonalCompactEquiv n k) x)
  exact mem_frobenius_range_of_finite_orbit hgk hℓ (A x) (T.1 x).2
    (Submodule.finiteDimensional_of_le hle)

private def postcomposeOnSubmodule {X H : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H]
    (P : Submodule ℂ (X →ₗ[ℂ] H)) (C : H →ₗ[ℂ] V) : P →ₗ[ℂ] (X →ₗ[ℂ] V) :=
  (LinearMap.compRight ℂ C).comp P.subtype

set_option backward.isDefEq.respectTransparency true in
private def pullbackIntertwiner :=
  postcomposeOnSubmodule (H := W) (X := Fin d → ℂ) J
    ((frobeniusHilbert hgk hℓ).leftInverse.comp (frobeniusClosure hgk hℓ).subtype)

private theorem frobeniusHilbert_leftInverse_intertwiner
    (hinj : Function.Injective (frobeniusHilbert hgk hℓ)) (T : J) (x : Fin d → ℂ) :
    B ((frobeniusHilbert hgk hℓ).leftInverse (T.1 x : Hilbert a e)) = (T.1 x : Hilbert a e) := by
  obtain ⟨v, hv⟩ := hilbertIntertwiner_mem_frobeniusRange hgk hℓ d τ T x
  let F := B
  calc
    _ = F (F.leftInverse (F v)) := congrArg (fun y : Hilbert a e => F (F.leftInverse y)) hv.symm
    _ = F v := congrArg F (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hinj) v)
    _ = _ := hv

/-- Pull compact intertwiners into the Frobenius completion back to the algebraic module. -/
def frobeniusIntertwinerComparison (hinj : Function.Injective (frobeniusHilbert hgk hℓ)) :
    J →ₗ[ℂ] gkIntertwiners ρ d (τ.comp (orthogonalCompactEquiv n).toMonoidHom) := by
  refine (pullbackIntertwiner hgk hℓ d τ).codRestrict _ (fun T k x => ?_)
  let L := (frobeniusHilbert hgk hℓ).leftInverse
  change L (T.1 (τ (orthogonalCompactEquiv n k) *ᵥ x) : Hilbert a e) =
    ρ k (L (T.1 x : Hilbert a e))
  apply hinj
  have hk : representation a e (Unitary.toUnits k) (B (L (T.1 x : Hilbert a e))) =
      B (ρ k (L (T.1 x : Hilbert a e))) :=
    representation_frobeniusHilbert_compact hgk hℓ (orthogonalCompactEquiv n k) _
  rw [← hk, frobeniusHilbert_leftInverse_intertwiner hgk hℓ d τ hinj,
    frobeniusHilbert_leftInverse_intertwiner hgk hℓ d τ hinj]
  exact congrArg Subtype.val (T.2 (orthogonalCompactEquiv n k) x)

/-- Compact admissibility transfers to the Frobenius Hilbert closure. -/
theorem isAdmissible_frobeniusClosureRepresentation
    (hirr : IsIrreducibleGKModule ρ π) (h₀ : ℓ ≠ 0) (hadm : IsAdmissibleGKModule ρ) :
    IsAdmissible (E := W) R (unitaryCompact ℝ n) := by
  intro d' τ' hτ
  have hinj := frobeniusHilbert_injective hgk hℓ hirr h₀
  have hG : FiniteDimensional ℂ (gkIntertwiners ρ d' (τ'.comp (orthogonalCompactEquiv n).toMonoidHom)) :=
    hadm d' _ (hτ.comp (continuous_orthogonalCompactEquiv (n := n)))
  let A := frobeniusIntertwinerComparison hgk hℓ d' τ' hinj
  have hA : Function.Injective A := by
    intro S T he
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    let L := (frobeniusHilbert hgk hℓ).leftInverse
    have he' : L (S.1 x : Hilbert a e) = L (T.1 x : Hilbert a e) :=
      congrArg (fun C => C.1 x) he
    calc
      _ = B (L (S.1 x : Hilbert a e)) :=
        (frobeniusHilbert_leftInverse_intertwiner hgk hℓ d' τ' hinj S x).symm
      _ = B (L (T.1 x : Hilbert a e)) := congrArg (frobeniusHilbert hgk hℓ) he'
      _ = _ := frobeniusHilbert_leftInverse_intertwiner hgk hℓ d' τ' hinj T x
  exact FiniteDimensional.of_injective A hA

end Langlands.Archimedean.RealPrincipalSeriesHilbert
