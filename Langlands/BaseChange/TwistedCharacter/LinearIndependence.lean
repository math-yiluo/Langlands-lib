import Langlands.Algebra.RankOneGradedAlgebra
import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.Representation.Character.SeparationProof
import Langlands.LinearAlgebra.FiniteSimpleTrace
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Linear independence of twisted characters

Let `θ` be an automorphism of a totally disconnected locally compact group `G` that preserves
arbitrarily small compact open subgroups (for example a continuous automorphism of finite
order). For pairwise inequivalent irreducible admissible representations `ρ i` and injective
endomorphisms `T i` with `T i ∘ ρ i g = ρ i (θ g) ∘ T i`, the twisted distributions
`twistedDistribution μ (ρ i) (hρ i) (T i)` are linearly independent over `ℂ`.

The proof restricts everything to the fixed vectors of a `θ`-stable compact open subgroup `K`
and uses Jacobson density to isolate a simple module over the Hecke corner `H_K`.
Burnside's theorem realizes the inverse of the twisting operator on that module.
-/

noncomputable section

namespace Langlands

open MeasureTheory HarmonicAnalysis

universe uI uG uV

namespace BaseChange

section StableSubgroups

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- A continuous automorphism of finite order preserves arbitrarily small compact open
subgroups: inside every open subgroup there is a compact open subgroup `K` with
`θ⁻¹(K) ⊆ K`. -/
theorem exists_compact_openSubgroup_symm_mem (θ : G ≃* G) (hθ : Continuous θ) (N : ℕ)
    (hN : 0 < N) (hθN : ∀ g, (⇑θ)^[N] g = g) (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K := by
  obtain ⟨K₀, hK₀U, hK₀, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
  let H : Subgroup G :=
    { carrier := {g | ∀ j < N, (⇑θ)^[j] g ∈ K₀}
      mul_mem' := fun {a b} ha hb j hj => by
        rw [iterate_map_mul θ j]
        exact K₀.mul_mem (ha j hj) (hb j hj)
      one_mem' := fun j _ => by
        rw [iterate_map_one θ j]
        exact K₀.one_mem
      inv_mem' := fun {a} ha j hj => by
        rw [iterate_map_inv θ j]
        exact K₀.inv_mem (ha j hj) }
  have hHopen : IsOpen (H : Set G) := by
    have hset : (H : Set G) = ⋂ j ∈ Finset.range N, (⇑θ)^[j] ⁻¹' (K₀ : Set G) := by
      ext g
      simp only [Set.mem_iInter, Finset.mem_range, Set.mem_preimage, SetLike.mem_coe]
      rfl
    rw [hset]
    exact isOpen_biInter_finset fun j _ => K₀.isOpen.preimage (hθ.iterate j)
  let K : OpenSubgroup G := ⟨H, hHopen⟩
  have hKK₀ : (K : Set G) ⊆ K₀ := fun g hg => hg 0 hN
  refine ⟨K, fun g hg => hK₀U (hKK₀ hg), hK₀.of_isClosed_subset K.isClosed hKK₀, ?_⟩
  intro k hk j hj
  cases j with
  | zero =>
    have h1 : θ ((⇑θ)^[N - 1] k) = k := by
      rw [← Function.iterate_succ_apply' (⇑θ) (N - 1) k, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hN]
      exact hθN k
    have h2 : θ.symm k = (⇑θ)^[N - 1] k := by
      conv_lhs => rw [← h1]
      exact θ.symm_apply_apply _
    rw [Function.iterate_zero_apply, h2]
    exact hk (N - 1) (by omega)
  | succ j =>
    rw [Function.iterate_succ_apply, MulEquiv.apply_symm_apply]
    exact hk j (by omega)

end StableSubgroups

section Corner

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- An endomorphism `T` with `T ∘ ρ(g) = ρ(θ g) ∘ T` maps the `K`-fixed vectors into
themselves when `θ⁻¹(K) ⊆ K`. -/
theorem mem_fixedVectors_of_twisted (ρ : Representation ℂ G V) (θ : G ≃* G)
    (T : Module.End ℂ V) (hT : ∀ g, T ∘ₗ ρ g = ρ (θ g) ∘ₗ T) (K : Subgroup G)
    (hK : ∀ k ∈ K, θ.symm k ∈ K) {v : V} (hv : v ∈ fixedVectors ρ K) :
    T v ∈ fixedVectors ρ K := by
  intro k
  change ρ k (T v) = T v
  have hk : θ.symm k ∈ K := hK k k.property
  have h := LinearMap.congr_fun (hT (θ.symm k)) v
  rw [MulEquiv.apply_symm_apply] at h
  change T (ρ (θ.symm k) v) = ρ k (T v) at h
  have hv' : ρ (θ.symm k) v = v := hv ⟨θ.symm k, hk⟩
  rw [← h, hv']

/-- On an element of the Hecke corner `H_K`, the twisted distribution of `(ρ, T)` is the
trace of the corner action composed with `T` on the `K`-fixed vectors, provided `T`
preserves them. -/
theorem twistedDistribution_corner_of_preserves_fixedVectors
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (T : Module.End ℂ V) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hTK : ∀ v ∈ fixedVectors ρ K.toSubgroup, T v ∈ fixedVectors ρ K.toSubgroup)
    (e : Hecke.HeckeAlgebra.Corner μ K hK) :
    twistedDistribution μ ρ hρ T
        (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e)) =
      LinearMap.trace ℂ (fixedVectors ρ K.toSubgroup)
        (Hecke.cornerAction μ ρ hρ.1 K hK e ∘ₗ T.restrict hTK) := by
  have : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  have hrange : LinearMap.range (Hecke.integratedAction μ ρ hρ.1
      (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e))
        ∘ₗ T) ≤ fixedVectors ρ K.toSubgroup :=
    (LinearMap.range_comp_le_range _ _).trans
      (Hecke.integratedAction_range_le_fixedVectors μ ρ hρ.1 e.property)
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_subspace _ _ hrange]
  congr 1

end Corner

section Independence

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Fixed-corner interpolation of twisted characters on a finite family. If every
irreducible represented in the family has a nonzero fixed vector for a compact open
subgroup `K` preserved by `θ⁻¹`, every family of values of its twisted distributions
is attained by one test function in the Hecke corner of `K`. -/
theorem exists_twistedDistribution_corner_values (θ : G ≃* G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hθK : ∀ k ∈ K, θ.symm k ∈ K)
    {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    (hρ : ∀ i, IsAdmissible (ρ i)) (hirr : ∀ i, (ρ i).IsIrreducible)
    (hne : Pairwise fun i j => ¬ Nonempty ((ρ i).Equiv (ρ j)))
    (hfix : ∀ i, fixedVectors (ρ i) K.toSubgroup ≠ ⊥)
    (T : ∀ i, Module.End ℂ (V i)) (hT : ∀ i g, T i ∘ₗ ρ i g = ρ i (θ g) ∘ₗ T i)
    (hTinj : ∀ i, Function.Injective (T i)) (c : ι → ℂ) :
    ∃ e : Hecke.HeckeAlgebra.Corner μ K hK, ∀ i,
      twistedDistribution μ (ρ i) (hρ i) (T i)
        (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e)) =
      c i := by
  classical
  have hvex : ∀ i, ∃ v : V i, v ∈ fixedVectors (ρ i) K.toSubgroup ∧ v ≠ 0 := fun i => by
    have := Submodule.nontrivial_iff_ne_bot.mpr (hfix i)
    obtain ⟨v, hv⟩ := exists_ne (0 : fixedVectors (ρ i) K.toSubgroup)
    exact ⟨v, v.property, fun h => hv (Subtype.ext h)⟩
  choose v hvK hv using hvex
  let M : ι → Type uV := fun i => fixedVectors (ρ i) K.toSubgroup
  let : ∀ i, Module (Hecke.HeckeAlgebra.Corner μ K hK) (M i) :=
    fun i => Hecke.cornerModule μ (ρ i) (hρ i).1 K hK
  have : ∀ i, IsScalarTower ℂ (Hecke.HeckeAlgebra.Corner μ K hK) (M i) :=
    fun i => Hecke.cornerModule_isScalarTower μ (ρ i) (hρ i).1 K hK
  have : ∀ i, FiniteDimensional ℂ (M i) := fun i => (hρ i).2 K
  have : ∀ i, IsSimpleModule (Hecke.HeckeAlgebra.Corner μ K hK) (M i) := by
    intro i
    apply CompactCoefficientClass.isSimpleModule_fixedVectors μ
      (ρ i) (hρ i).1 K hK (hirr i)
    intro h
    exact hv i ((Submodule.mem_bot ℂ).mp (h ▸ hvK i))
  have hcorner : Pairwise (fun i j =>
      ¬ Nonempty (M i ≃ₗ[Hecke.HeckeAlgebra.Corner μ K hK] M j)) := by
    intro i j hij ⟨φ⟩
    apply hne hij
    let a : M i := ⟨v i, hvK i⟩
    have hb : ((φ a : M j) : V j) ≠ 0 := by
      intro h
      have h0 : φ a = 0 := Subtype.ext h
      exact hv i (congrArg Subtype.val (φ.map_eq_zero_iff.mp h0))
    refine Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff μ K hK
      (hρ i).1 (hirr i) (hρ j).1 (hirr j) a (φ a) (hv i) hb
      fun e => ?_
    have hφ : φ (Hecke.cornerAction μ (ρ i) (hρ i).1 K hK e a) =
        Hecke.cornerAction μ (ρ j) (hρ j).1 K hK e (φ a) :=
      φ.map_smul e a
    rw [← hφ, φ.map_eq_zero_iff]
  have hTK : ∀ i, ∀ w ∈ fixedVectors (ρ i) K.toSubgroup,
      T i w ∈ fixedVectors (ρ i) K.toSubgroup :=
    fun i w hw => mem_fixedVectors_of_twisted (ρ i) θ (T i) (hT i) K.toSubgroup hθK hw
  let B : ∀ i, Module.End ℂ (M i) := fun i => (T i).restrict (hTK i)
  have hBinj : ∀ i, Function.Injective (B i) := fun i x y hxy =>
    Subtype.ext (hTinj i (congrArg Subtype.val hxy))
  let C := Hecke.HeckeAlgebra.Corner μ K hK
  let toTest : C →ₗ[ℂ] SchwartzBruhat G :=
    (Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup).subtype.comp
      (Hecke.HeckeAlgebra.Corner.toBiInvariant μ K hK).toLinearMap
  let D (i : ι) : C →ₗ[ℂ] ℂ := (twistedDistribution μ (ρ i) (hρ i) (T i)).comp toTest
  change ∃ e, ∀ i, D i e = c i
  have hsep (j : ι) : ∃ e, ∀ i, D i e = if i = j then 1 else 0 := by
    obtain ⟨r, hr⟩ := FiniteSimpleTrace.exists_action_projection M hcorner j
    let Ej := LinearEquiv.ofInjectiveEndo (B j) (hBinj j)
    obtain ⟨s, hs⟩ := RankOneGraded.exists_forall_eq_smul_of_isSimpleModule
      (A := C) Ej.symm.toLinearMap
    let d : ℂ := Module.finrank ℂ (M j)
    refine ⟨d⁻¹ • (r * s), fun i => ?_⟩
    rw [map_smul, smul_eq_mul]
    change d⁻¹ * twistedDistribution μ (ρ i) (hρ i) (T i) (toTest (r * s)) = _
    rw [show toTest (r * s) =
        Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (r * s))
        from rfl, twistedDistribution_corner_of_preserves_fixedVectors μ (ρ i) (hρ i)
          (T i) K hK (hTK i)]
    by_cases hij : i = j
    · subst i
      have hrj : Hecke.cornerAction μ (ρ j) (hρ j).1 K hK r = LinearMap.id := by
        have h := hr j
        simp only [↓reduceIte] at h
        exact h
      have hsj : Hecke.cornerAction μ (ρ j) (hρ j).1 K hK s = Ej.symm.toLinearMap :=
        LinearMap.ext fun x => (hs x).symm
      have hact : Hecke.cornerAction μ (ρ j) (hρ j).1 K hK (r * s) ∘ₗ (T j).restrict (hTK j) =
          LinearMap.id := by
        rw [map_mul, Module.End.mul_eq_comp, hrj, hsj, LinearMap.id_comp]
        ext x
        exact congrArg Subtype.val (Ej.symm_apply_apply x)
      have : Nontrivial (M j) := IsSimpleModule.nontrivial C (M j)
      have hd : d ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := M j)).ne'
      rw [hact, LinearMap.trace_id]
      simpa only [↓reduceIte] using inv_mul_cancel₀ hd
    · have hri : Hecke.cornerAction μ (ρ i) (hρ i).1 K hK r = 0 := by
        have h := hr i
        simp only [hij, ↓reduceIte] at h
        exact h
      rw [map_mul, Module.End.mul_eq_comp, hri, LinearMap.zero_comp, LinearMap.zero_comp,
        map_zero, mul_zero]
      simp [hij]
  choose e he using hsep
  refine ⟨∑ j, c j • e j, fun i => ?_⟩
  simp [map_sum, he, smul_eq_mul]

/-- Interpolate the twisted distributions of finitely many pairwise inequivalent
irreducible admissible representations on one test function, using a common compact
open subgroup preserved by `θ⁻¹`. -/
theorem exists_twistedDistribution_test_values (θ : G ≃* G)
    (hθ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K)
    {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    (hρ : ∀ i, IsAdmissible (ρ i)) (hirr : ∀ i, (ρ i).IsIrreducible)
    (hne : Pairwise fun i j => ¬ Nonempty ((ρ i).Equiv (ρ j)))
    (T : ∀ i, Module.End ℂ (V i)) (hT : ∀ i g, T i ∘ₗ ρ i g = ρ i (θ g) ∘ₗ T i)
    (hTinj : ∀ i, Function.Injective (T i)) (c : ι → ℂ) :
    ∃ f : SchwartzBruhat G, ∀ i, twistedDistribution μ (ρ i) (hρ i) (T i) f = c i := by
  classical
  have hvex : ∀ i, ∃ v : V i, v ≠ 0 := fun i => by
    have := CharacterSeparation.nontrivial_of_isIrreducible (hirr i)
    exact exists_ne 0
  choose v hv using hvex
  choose U hU using fun i => (hρ i).1 (v i)
  obtain ⟨K, hKU, hK, hθK⟩ := hθ (Finset.univ.inf U)
  have hfix i : fixedVectors (ρ i) K.toSubgroup ≠ ⊥ := by
    have hvK : v i ∈ fixedVectors (ρ i) K.toSubgroup := by
      intro k
      have hKi : K ≤ U i := hKU.trans (Finset.inf_le (Finset.mem_univ i))
      exact hU i ⟨k, hKi k.property⟩
    intro h
    exact hv i ((Submodule.mem_bot ℂ).mp (h ▸ hvK))
  obtain ⟨e, he⟩ := exists_twistedDistribution_corner_values μ θ K hK hθK ρ hρ hirr hne hfix
    T hT hTinj c
  exact ⟨Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e), he⟩

/-- Linear independence of twisted characters. Let `θ` be an automorphism of `G` such that
 every open subgroup contains a compact open subgroup `K` with `θ⁻¹(K) ⊆ K`. Let `ρ i` be
 pairwise inequivalent irreducible admissible representations and `T i` injective
 endomorphisms with `T i ∘ ρ i g = ρ i (θ g) ∘ T i`. Then the twisted distributions of the
 pairs `(ρ i, T i)` are linearly independent over `ℂ`. -/
theorem twistedDistribution_linearIndependent (θ : G ≃* G)
    (hθ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K)
    {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    (hρ : ∀ i, IsAdmissible (ρ i)) (hirr : ∀ i, (ρ i).IsIrreducible)
    (hne : Pairwise fun i j => ¬ Nonempty ((ρ i).Equiv (ρ j)))
    (T : ∀ i, Module.End ℂ (V i)) (hT : ∀ i g, T i ∘ₗ ρ i g = ρ i (θ g) ∘ₗ T i)
    (hTinj : ∀ i, Function.Injective (T i)) :
    LinearIndependent ℂ fun i => twistedDistribution μ (ρ i) (hρ i) (T i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  obtain ⟨f, hf⟩ := exists_twistedDistribution_test_values μ θ hθ ρ hρ hirr hne T hT hTinj
    (fun i => if i = j then 1 else 0)
  have h := LinearMap.congr_fun hc f
  simpa [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hf] using h

/-- Linear independence of twisted characters for a continuous automorphism `θ` of finite
order `N > 0`. -/
theorem twistedDistribution_linearIndependent_of_iterate (θ : G ≃* G) (hθ : Continuous θ)
    (N : ℕ) (hN : 0 < N) (hθN : ∀ g, (⇑θ)^[N] g = g)
    {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    (hρ : ∀ i, IsAdmissible (ρ i)) (hirr : ∀ i, (ρ i).IsIrreducible)
    (hne : Pairwise fun i j => ¬ Nonempty ((ρ i).Equiv (ρ j)))
    (T : ∀ i, Module.End ℂ (V i)) (hT : ∀ i g, T i ∘ₗ ρ i g = ρ i (θ g) ∘ₗ T i)
    (hTinj : ∀ i, Function.Injective (T i)) :
    LinearIndependent ℂ fun i => twistedDistribution μ (ρ i) (hρ i) (T i) :=
  twistedDistribution_linearIndependent μ θ
    (exists_compact_openSubgroup_symm_mem θ hθ N hN hθN) ρ hρ hirr hne T hT hTinj

end Independence

end BaseChange

end Langlands
