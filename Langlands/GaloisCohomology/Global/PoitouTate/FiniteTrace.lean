import Langlands.GaloisCohomology.Global.PoitouTate.FinitePlaces
import Langlands.GaloisCohomology.Global.RealPlaces.HighDegree
import Langlands.GaloisCohomology.Global.Dimension.Proof

/-!
# The trace for the cohomology with compact support at the finite places

When `N` is odd or `K` is totally complex, the real places contribute nothing to the sum formula for
classes of `H²(G_S, μ_N)`: the sum over `v ∈ S` of the local invariants of the localizations vanishes
(`sum_invariantAt_localization`). Hence the sum of the local invariants on
`∏_{v ∈ S} H²(K_v, μ_N)` factors through `H_c³(G_S, μ_N)` (cohomology with compact support at the
places of `S`), which gives the trace `finiteTrace : H_c³(G_S, μ_N) → ℤ/N` with
`IsFiniteTrace` (`isFiniteTrace_finiteTrace`). When moreover `S` contains the places above `N`, the
map `∏_{v ∈ S} H²(K_v, μ_N) → H_c³(G_S, μ_N)` is onto (`H³(G_S, μ_N) = 0`), and a trace with
`IsFiniteTrace` is unique (`eq_finiteTrace_of_isFiniteTrace`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ IsTotallyComplex K)

omit [Finite S] in
include hK in
/-- **The sum formula at the places of `S`.** For `N` odd or `K` totally complex, the local invariants
at the places of `S` of a class of `H²(G_S, μ_N)` sum to zero. -/
theorem sum_invariantAt_localization [Fintype S] (x : cohomology (dualizingModule K Ω S N) 2) :
    ∑ v : S, invariantAt ι S N v (localization ι (dualizingModule K Ω S N) v 2 x) = 0 := by
  have h := sum_invariantAt_add_sum_realInvariantAt ι S N x
  have h0 : ∑ w : {w : InfinitePlace K // w.IsReal},
      realInvariantAt ι S N w (realLocalization ι (dualizingModule K Ω S N) w 2 x) = 0 :=
    Finset.sum_eq_zero fun w _ => by
      rcases hK with ho | hc
      · rw [eq_zero_cohomology_closureGalois_of_odd w.1 w.2 _ ho (nsmul_dualizingModule S N)
          two_ne_zero (realLocalization ι (dualizingModule K Ω S N) w 2 x), map_zero]
      · exact absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (hc.isComplex w.1))
  rwa [h0, add_zero] at h

/-- The sum of the local invariants on `∏_{v ∈ S} H²(K_v, μ_N)`. -/
def finiteSumInvariants :
    (∀ v : S, cohomology (localModule ι (dualizingModule K Ω S N) v.1) 2) →+ QZ :=
  letI : Fintype S := Fintype.ofFinite S
  { toFun := fun ξ => ∑ v : S, invariantAt ι S N v (ξ v)
    map_zero' := by simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]
    map_add' := fun ξ η => by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib] }

omit [NeZero N] in
theorem finiteSumInvariants_apply
    (ξ : ∀ v : S, cohomology (localModule ι (dualizingModule K Ω S N) v.1) 2) :
    finiteSumInvariants ι S N ξ = letI : Fintype S := Fintype.ofFinite S
      ∑ v : S, invariantAt ι S N v (ξ v) :=
  rfl

include hK in
/-- The sum of the local invariants vanishes on the kernel of
`∏_{v ∈ S} H²(K_v, μ_N) → H_c³(G_S, μ_N)`. -/
theorem ker_ptLocalToCompact_le_ker_finiteSumInvariants :
    (ptLocalToCompact (localFamily ι S) (dualizingModule K Ω S N) 2).hom.toAddMonoidHom.ker ≤
      (finiteSumInvariants ι S N).ker := by
  let _ : Fintype S := Fintype.ofFinite S
  intro ξ hξ
  obtain ⟨x, rfl⟩ := (ptExact_local (localFamily ι S) (dualizingModule K Ω S N) 2 ξ).1 hξ
  exact sum_invariantAt_localization ι S N hK x

/-- The trace `H_c³(G_S, μ_N) → ℚ/ℤ` at the finite places: an extension of the sum of the local
invariants. -/
def finiteTraceQZ :
    compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3 →+ QZ :=
  (QZ.exists_comp_eq_of_ker_le _ _
    (ker_ptLocalToCompact_le_ker_finiteSumInvariants ι S N hK)).choose

theorem finiteTraceQZ_comp :
    (finiteTraceQZ ι S N hK).comp (ptLocalToCompact (localFamily ι S)
      (dualizingModule K Ω S N) 2).hom.toAddMonoidHom = finiteSumInvariants ι S N :=
  (QZ.exists_comp_eq_of_ker_le _ _
    (ker_ptLocalToCompact_le_ker_finiteSumInvariants ι S N hK)).choose_spec

/-- The values of `finiteTraceQZ` are killed by `N`. -/
theorem nsmul_finiteTraceQZ
    (z : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3) :
    N • finiteTraceQZ ι S N hK z = 0 := by
  rw [← map_nsmul, nsmul_compactSupportCohomologyRes_eq_zero (localFamily ι S)
    (nsmul_dualizingModule S N) 3 z, map_zero]

/-- **The trace** `H_c³(G_S, μ_N) → ℤ/N` at the finite places (`N` odd or `K` totally complex). -/
def finiteTrace :
    compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3 →+ ZMod N :=
  zmodOfQZ (finiteTraceQZ ι S N hK) (nsmul_finiteTraceQZ ι S N hK)

/-- On the image of the local terms, `finiteTrace` is the sum of the local invariants. -/
theorem isFiniteTrace_finiteTrace : IsFiniteTrace ι S N (finiteTrace ι S N hK) := fun ξ =>
  (zmodToQZ_zmodOfQZ _ _ _).trans (DFunLike.congr_fun (finiteTraceQZ_comp ι S N hK) ξ)

omit [Finite S] in
include hK in
/-- With the places above `N` in `S`, `∏_{v ∈ S} H²(K_v, μ_N) → H_c³(G_S, μ_N)` is surjective. -/
theorem surjective_ptLocalToCompact_two
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Function.Surjective
      (ptLocalToCompact (localFamily ι S) (dualizingModule K Ω S N) 2).hom := by
  intro z
  have h3 := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S (NeZero.ne N) hS
    hK (dualizingModule K Ω S N) (nsmul_dualizingModule S N) (le_refl 3)
  exact (ptExact_compact (localFamily ι S) (dualizingModule K Ω S N) 2 z).1 (Subsingleton.elim _ _)

include hK in
/-- With the places above `N` in `S`, a trace with `IsFiniteTrace` is `finiteTrace`. -/
theorem eq_finiteTrace_of_isFiniteTrace
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (T : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3 →+ ZMod N)
    (hT : IsFiniteTrace ι S N T) : T = finiteTrace ι S N hK := by
  refine AddMonoidHom.ext fun z => ?_
  refine (surjective_ptLocalToCompact_two ι S N hK hS z).elim fun ξ hξ => ?_
  rw [← hξ]
  apply zmodToQZ_injective (n := N)
  rw [hT ξ, isFiniteTrace_finiteTrace ι S N hK ξ]

end

end Langlands.GaloisCohomology.PoitouTate
