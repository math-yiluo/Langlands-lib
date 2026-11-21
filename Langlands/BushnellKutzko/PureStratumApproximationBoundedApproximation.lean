import Langlands.BushnellKutzko.CorestrictionIntegers
import Langlands.BushnellKutzko.ElementFieldInvariants
import Langlands.BushnellKutzko.SplittingBasis
import Langlands.BushnellKutzko.AdjointLatticeBounds
import Langlands.BushnellKutzko.RefinementElementExactness

/-! # Bounded approximation of a field generator by lower-degree elements

An algebraic replacement for the compactness argument in the termination step after (2.4.6) in
the proof of BK93 (2.4.1)(i), printed pp. 69–70.
-/

noncomputable section

open ValuativeRel Polynomial

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

/-- A field generator cannot be approximated arbitrarily well, inside any chain order, by
elements generating algebras of strictly smaller degree. The bound `M` depends only on the
generator and the chosen uniformizer. -/
def BoundedApproximationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (β : Module.End F V), IsField (elementAlgebra β) →
    ∀ (π : 𝒪[F]), Irreducible π →
    ∃ M : ℤ, ∀ (𝓛 : LatticeChain 𝒪[F] F V) (γ : Module.End F V) (t : ℤ),
      β ∈ 𝓛.endFiltration 0 → γ ∈ 𝓛.endFiltration 0 →
      elementDegree F γ < elementDegree F β →
      ((π : F) ^ (-t)) • (β - γ) ∈ 𝓛.endFiltration 0 → t ≤ M

section Denominator

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]

/-- Finitely many `F`-linear functionals take values with a common denominator on `𝔬_E`. -/
theorem exists_common_denominator {ι : Type*} [Finite ι] (c : ι → E →ₗ[F] F) :
    ∃ s : 𝒪[F], s ≠ 0 ∧ ∀ z ∈ subfieldIntegers F E, ∀ i, (s : F) * c i z ∈ 𝒪[F] := by
  let O : Submodule 𝒪[F] E := Subalgebra.toSubmodule (subfieldIntegers F E)
  have hO : O.FG := Module.Finite.iff_fg.mp (inferInstanceAs
    (Module.Finite 𝒪[F] (subfieldIntegers F E)))
  let I : Submodule 𝒪[F] F := ⨆ i, O.map ((c i).restrictScalars 𝒪[F])
  have hI : I.FG := Submodule.fg_iSup _ fun i => hO.map _
  obtain ⟨s, hs, hsI⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors 𝒪[F]) hI
  refine ⟨s, nonZeroDivisors.ne_zero hs, fun z hz i => ?_⟩
  have hmem : c i z ∈ I := Submodule.mem_iSup_of_mem i ⟨z, hz, rfl⟩
  obtain ⟨r, hr⟩ := hsI _ hmem
  have hr' : (r : F) = (s : F) * c i z := by
    rw [Algebra.smul_def] at hr
    exact hr
  rw [← hr']
  exact r.2

end Denominator

section Core

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
private theorem isIntegral_of_mem_order (𝓛 : LatticeChain 𝒪[F] F V) {x : Module.End F V}
    (hx : x ∈ 𝓛.endFiltration 0) : IsIntegral 𝒪[F] x :=
  IsIntegral.of_mem_of_fg 𝓛.order (𝓛.toSubmodule_order.symm ▸ 𝓛.endFiltration_zero_fg) x hx

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
private theorem smul_pow_sub_mem (𝓛 : LatticeChain 𝒪[F] F V) (c : F) {x y : Module.End F V}
    (hx : x ∈ 𝓛.endFiltration 0) (hy : y ∈ 𝓛.endFiltration 0)
    (hxy : c • (x - y) ∈ 𝓛.endFiltration 0) (i : ℕ) :
    c • (x ^ i - y ^ i) ∈ 𝓛.endFiltration 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hyi : y ^ i ∈ 𝓛.endFiltration 0 :=
      𝓛.mem_order_iff_mem_endFiltration.mp (𝓛.order.pow_mem
        (𝓛.mem_order_iff_mem_endFiltration.mpr hy) i)
    have e : c • (x ^ (i + 1) - y ^ (i + 1)) =
        x * (c • (x ^ i - y ^ i)) + (c • (x - y)) * y ^ i := by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_add, pow_succ', pow_succ']
      congr 1
      noncomm_ring
    rw [e]
    apply add_mem
    · simpa using 𝓛.mul_mem_endFiltration hx ih
    · simpa using 𝓛.mul_mem_endFiltration hxy hyi

/-- The core bound for a fixed field generator. -/
theorem boundedApproximation_aux (β : Module.End F V) (hβ : IsField (elementAlgebra β))
    {π : 𝒪[F]} (hπ : Irreducible π) :
    ∃ M : ℤ, ∀ (𝓛 : LatticeChain 𝒪[F] F V) (γ : Module.End F V) (t : ℤ),
      β ∈ 𝓛.endFiltration 0 → γ ∈ 𝓛.endFiltration 0 →
      elementDegree F γ < elementDegree F β →
      ((π : F) ^ (-t)) • (β - γ) ∈ 𝓛.endFiltration 0 → t ≤ M := by
  classical
  let : Field (elementAlgebra β) := hβ.toField
  have htop : Algebra.adjoin F ({elementGenerator β} : Set (elementAlgebra β)) = ⊤ :=
    adjoin_elementGenerator β
  have hgenF : IsIntegral F (elementGenerator β) := IsIntegral.of_finite F _
  let pb := PowerBasis.ofAdjoinEqTop hgenF htop
  obtain ⟨s, hs0, hs⟩ := exists_common_denominator (E := elementAlgebra β)
    (fun i : Fin pb.dim => pb.basis.coord i)
  refine ⟨ordOf hπ (s : F), fun 𝓛 γ t hβ0 hγ0 hdeg hdiff => ?_⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] F) := Subtype.val_injective
  -- A monic integral polynomial killing `γ`, of degree at most `[F[γ]:F]`.
  have hγF : IsIntegral F γ := IsIntegral.of_finite F γ
  obtain ⟨g, hgm, hg⟩ := isIntegral_of_mem_order 𝓛 hγ0
  have hdvd : minpoly F γ ∣ g.map (algebraMap 𝒪[F] F) :=
    minpoly.dvd F γ (by rw [aeval_map_algebraMap, aeval_def, hg])
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := F) hgm hdvd
  rw [(minpoly.monic hγF).leadingCoeff, map_one, mul_one] at hp
  have hpm : p.Monic := monic_of_injective hinj (hp ▸ minpoly.monic hγF)
  have hpdeg : p.natDegree ≤ elementDegree F γ := by
    rw [← natDegree_map_eq_of_injective hinj, hp]
    have h := minpoly.algHom_eq (elementAlgebra γ).val Subtype.val_injective
      (elementGenerator γ)
    change minpoly F γ = _ at h
    rw [h]
    exact minpoly.natDegree_le (elementGenerator γ)
  have hpγ : aeval γ p = 0 := by
    rw [← aeval_map_algebraMap F, hp, minpoly.aeval]
  have hD : elementDegree F β = pb.dim := pb.finrank
  have hdD : p.natDegree < pb.dim := by rw [← hD]; omega
  -- The element `z = π^{-t} p(β)` lies in the order.
  set c : F := (π : F) ^ (-t) with hc
  have hz : c • aeval β p ∈ 𝓛.endFiltration 0 := by
    have hsplit : aeval β p = aeval β p - aeval γ p := by rw [hpγ, sub_zero]
    rw [hsplit, aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_sub_distrib,
      Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_sub, smul_comm]
    exact Submodule.smul_mem _ _ (smul_pow_sub_mem 𝓛 c hβ0 hγ0 hdiff i)
  -- Its image in `F[β]` is integral, so its coordinates have a bounded denominator.
  have hzE : c • aeval β p ∈ elementAlgebra β := by
    apply Subalgebra.smul_mem
    rw [← aeval_map_algebraMap F]
    exact aeval_mem_adjoin_singleton F β
  let z : elementAlgebra β := ⟨c • aeval β p, hzE⟩
  have hzint : z ∈ subfieldIntegers F (elementAlgebra β) := by
    have h := isIntegral_of_mem_order 𝓛 hz
    exact (isIntegral_algHom_iff ((elementAlgebra β).val.restrictScalars 𝒪[F])
      Subtype.val_injective).mp h
  let q : F[X] := p.map (algebraMap 𝒪[F] F)
  have hqdeg : q.natDegree < pb.dim := by
    rw [natDegree_map_eq_of_injective hinj]
    exact hdD
  have hzq : z = c • aeval pb.gen q := by
    apply Subtype.ext
    change c • aeval β p = ((c • aeval pb.gen q : elementAlgebra β) : Module.End F V)
    rw [Subalgebra.coe_smul]
    congr 1
    have h := aeval_algHom_apply (elementAlgebra β).val pb.gen q
    rw [Subalgebra.coe_val] at h
    change aeval β p = ((aeval pb.gen q : elementAlgebra β) : Module.End F V)
    rw [← h]
    change aeval β p = aeval β q
    exact (aeval_map_algebraMap F β p).symm
  have hsum : aeval pb.gen q = pb.basis.equivFun.symm (fun i : Fin pb.dim => q.coeff i) := by
    rw [Module.Basis.equivFun_symm_apply, aeval_eq_sum_range' hqdeg, Finset.sum_range]
    simp only [pb.basis_eq_pow]
  have hcoord : pb.basis.coord ⟨p.natDegree, hdD⟩ z = c := by
    rw [Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, hzq, hsum, map_smul,
      LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    simp [q, coeff_map, hpm.coeff_natDegree]
  have hmem := hs z hzint ⟨p.natDegree, hdD⟩
  simp only [hcoord] at hmem
  have hs0' : (s : F) ≠ 0 := fun h => hs0 (Subtype.ext h)
  have hc0 : c ≠ 0 := zpow_ne_zero _ (coe_uniformizer_ne_zero hπ)
  have hord := ordOf_nonneg hπ (mul_ne_zero hs0' hc0) hmem
  rw [ordOf_mul hπ hs0' hc0, hc, ordOf_zpow] at hord
  omega

/-- The algebraic bound replacing compactness. -/
theorem boundedApproximation : BoundedApproximationStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ β hβ π hπ
  exact boundedApproximation_aux β hβ hπ

end Core

end Langlands.BushnellKutzko.PureApproximation
