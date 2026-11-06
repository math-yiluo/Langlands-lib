import Langlands.Cohomology.SupercuspidalExtCharZero.Positivity
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.MatrixCoefficient.Definitions
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.RepresentationTheory.Irreducible

/-!
# Coefficient maps of a representation with compact coefficients

Let `ρ` be a representation of `G` on `V` over a field `k` of characteristic zero, `U` an
open subgroup and `ξ` a `U`-invariant functional on `V` whose coefficients
`g ↦ ξ (ρ g v)` have compact support. For a representation `σ` on `W` and a `U`-fixed
vector `x`, the coefficient map is

`v ↦ ∑_{gU} ξ (ρ g⁻¹ v) • σ g x`,

a finite sum over the left cosets of `U`. It is an intertwiner `ρ → σ`, natural in
`(σ, x)`. If `ρ` is smooth with compactly supported coefficients and `V ≠ 0`, there are a
compact open `U`, a functional `ξ` and a vector `w` with nonzero coefficient map
`V → V`; for irreducible `ρ` it is then bijective.

The module also contains the facts about compact open subgroups and averaging used by
the proofs of projectivity and injectivity.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open Function Filter _root_.Topology
open Langlands.Compact.CharZero

universe uk uG uV uW uM

variable {k : Type uk} [Field k]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {W : Type uW} [AddCommGroup W] [Module k W]

section FixedVectors

theorem mem_fixedVectors_iff {ρ : Representation k G V} {K : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ K ↔ ∀ g ∈ K, ρ g v = v :=
  ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

/-- A functional is fixed by `K` under the dual action exactly when it is invariant under
the operators `ρ g`, `g ∈ K`. -/
theorem mem_fixedVectors_dual_iff {ρ : Representation k G V} {K : Subgroup G}
    {ℓ : Module.Dual k V} :
    ℓ ∈ fixedVectors ρ.dual K ↔ ∀ g ∈ K, ∀ v, ℓ (ρ g v) = ℓ v := by
  rw [mem_fixedVectors_iff]
  constructor
  · intro h g hg v
    have := LinearMap.congr_fun (h g⁻¹ (K.inv_mem hg)) v
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this
  · intro h g hg
    ext v
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h g⁻¹ (K.inv_mem hg) v

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ w : V, w ≠ 0 := by
  by_contra h
  push Not at h
  have : Subsingleton V := ⟨fun a b => by rw [h a, h b]⟩
  exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    (Subrepresentation.ext (Subsingleton.elim _ _))

end FixedVectors

section CompactOpen

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Every neighbourhood of `1` contains a compact open subgroup (van Dantzig). -/
theorem exists_compact_openSubgroup_subset {S : Set G} (hS : S ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ S :=
  ((Langlands.Topology.LocallyProfiniteProof.vanDantzig G).1
    (Langlands.Topology.isLocallyProfinite_of_mathlib (X := G))).2 S hS

/-- A smooth vector is fixed by a compact open subgroup. -/
theorem exists_compact_fixing {ρ : Representation k G V} {v : V} (hv : IsSmoothVector ρ v) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ v ∈ fixedVectors ρ K.toSubgroup := by
  obtain ⟨L, hL⟩ := hv
  obtain ⟨K, hKc, hKL⟩ := exists_compact_openSubgroup_subset L.mem_nhds_one
  refine ⟨K, hKc, ?_⟩
  rw [mem_fixedVectors_iff] at hL ⊢
  exact fun g hg => hL g (hKL hg)

end CompactOpen

section Averaging

variable [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A linear map that is invariant under a compact open subgroup `K` is unchanged by
`K`-averaging. -/
theorem apply_averageMap_of_invariant {M : Type uM} [AddCommGroup M] [Module k M]
    (ρ : Representation k G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (φ : V →ₗ[k] M) (hφ : ∀ g ∈ K, ∀ v, φ (ρ g v) = φ v)
    (v : V) : φ (averageMap ρ hρ K hK v) = φ v := by
  have := finite_orbit_of_smooth ρ hρ K hK v
  have hfin : Finite (orbit (Representation.trivial k K.toSubgroup M) (φ v)) := by
    refine Set.Finite.to_subtype ((Set.finite_singleton (φ v)).subset ?_)
    rintro _ ⟨g, rfl⟩
    simp [Representation.trivial_apply]
  have h := orbitMean_map (ρ.comp K.toSubgroup.subtype)
    (Representation.trivial k K.toSubgroup M) φ
    (fun g x => by simpa [Representation.trivial_apply] using hφ g g.2 x) v
  show φ (orbitMean _ v) = φ v
  rw [h]
  exact orbitMean_id _ _ fun g => by simp [Representation.trivial_apply]

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- A nonzero vector of a smooth representation, and a smooth functional not vanishing on
it, are fixed by a common compact open subgroup. -/
theorem exists_dual_apply_ne_zero (ρ : Representation k G V) (hρ : IsSmooth ρ) {w : V}
    (hw : w ≠ 0) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ w ∈ fixedVectors ρ K.toSubgroup ∧
      ∃ ℓ : Module.Dual k V, ℓ ∈ fixedVectors ρ.dual K.toSubgroup ∧ ℓ w ≠ 0 := by
  obtain ⟨K, hKc, hwK⟩ := exists_compact_fixing (hρ w)
  obtain ⟨ℓ₀, hℓ₀⟩ := Module.Projective.exists_dual_ne_zero k hw
  refine ⟨K, hKc, hwK, ℓ₀ ∘ₗ averageMap ρ hρ K hKc, ?_, ?_⟩
  · rw [mem_fixedVectors_dual_iff]
    intro g hg v
    simp only [LinearMap.comp_apply]
    rw [averageMap_apply_rho ρ hρ K hKc ⟨g, hg⟩ v]
  · simpa [averageMap_id ρ hρ K hKc w hwK] using hℓ₀

/-- Smooth functionals separate the vectors of a smooth representation. -/
theorem eq_zero_of_forall_smooth_dual (ρ : Representation k G V) (hρ : IsSmooth ρ) {v : V}
    (h : ∀ ℓ : Module.Dual k V, IsSmoothVector ρ.dual ℓ → ℓ v = 0) : v = 0 := by
  by_contra hv
  obtain ⟨K, -, -, ℓ, hℓ, hne⟩ := exists_dual_apply_ne_zero ρ hρ hv
  exact hne (h ℓ ⟨K, hℓ⟩)

end Averaging

section CoefficientMap

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : Representation k G V) (σ : Representation k G W)

/-- The coefficient map `v ↦ ∑_{gU} ξ (ρ g⁻¹ v) • σ g x`, a sum over the left cosets of
`U`. -/
def coefficientMap (U : Subgroup G) (ξ : Module.Dual k V) (x : W) (v : V) : W :=
  cosetSum U fun g => ξ (ρ g⁻¹ v) • σ g x

variable {ρ σ} {U : Subgroup G} {ξ : Module.Dual k V} {x : W}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem matrixCoefficient_eq (ℓ : Module.Dual k V) (v : V) :
    matrixCoefficient ρ ℓ v = fun g => ℓ (ρ g v) :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A linear map commutes with a coset sum with finitely many nonzero terms. -/
theorem map_cosetSum {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] {F : Type*}
    [FunLike F M N] [AddMonoidHomClass F M N] (f : F) {φ : G → M}
    (hφ : (fun q : G ⧸ U => φ q.out).HasFiniteSupport) :
    f (cosetSum U φ) = cosetSum U fun g => f (φ g) :=
  map_finsum f hφ

theorem coefficientMap_hasFiniteSupport (hU : IsOpen (U : Set G))
    (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v)) (v : V) :
    (fun q : G ⧸ U => ξ (ρ q.out⁻¹ v) • σ q.out x).HasFiniteSupport := by
  have h1 : HasCompactSupport fun g : G => ξ (ρ g⁻¹ v) :=
    (hc v).comp_homeomorph (Homeomorph.inv G)
  exact (hasFiniteSupport_out_of_hasCompactSupport hU h1).subset
    (support_smul_subset_left _ _)

theorem coefficientMap_add (hU : IsOpen (U : Set G))
    (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v)) (v v' : V) :
    coefficientMap ρ σ U ξ x (v + v') =
      coefficientMap ρ σ U ξ x v + coefficientMap ρ σ U ξ x v' := by
  unfold coefficientMap cosetSum
  simp only [map_add, add_smul]
  exact finsum_add_distrib (coefficientMap_hasFiniteSupport hU hc v)
    (coefficientMap_hasFiniteSupport hU hc v')

theorem coefficientMap_smul (hU : IsOpen (U : Set G))
    (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v)) (c : k) (v : V) :
    coefficientMap ρ σ U ξ x (c • v) = c • coefficientMap ρ σ U ξ x v := by
  unfold coefficientMap cosetSum
  rw [smul_finsum' c (coefficientMap_hasFiniteSupport hU hc v)]
  simp only [map_smul, smul_eq_mul, mul_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem coefficientMap_rightInvariant (hξ : ∀ u ∈ U, ∀ v, ξ (ρ u v) = ξ v)
    (hx : ∀ u ∈ U, σ u x = x) (v : V) :
    RightInvariant U fun g => ξ (ρ g⁻¹ v) • σ g x := by
  intro g u hu
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [hξ u⁻¹ (U.inv_mem hu), hx u hu]

/-- Composition with a linear map `W → M` moves inside the coefficient sum. -/
theorem map_coefficientMap {M : Type*} [AddCommMonoid M] {F : Type*} [FunLike F W M]
    [AddMonoidHomClass F W M] (f : F) (hU : IsOpen (U : Set G))
    (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v)) (v : V) :
    f (coefficientMap ρ σ U ξ x v) = cosetSum U fun g => f (ξ (ρ g⁻¹ v) • σ g x) :=
  map_cosetSum f (coefficientMap_hasFiniteSupport hU hc v)

theorem coefficientMap_apply_rep (hU : IsOpen (U : Set G))
    (hξ : ∀ u ∈ U, ∀ v, ξ (ρ u v) = ξ v) (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v))
    (hx : ∀ u ∈ U, σ u x = x) (h : G) (v : V) :
    coefficientMap ρ σ U ξ x (ρ h v) = σ h (coefficientMap ρ σ U ξ x v) := by
  rw [map_coefficientMap (σ h) hU hc]
  unfold coefficientMap
  rw [← cosetSum_mul_left (coefficientMap_rightInvariant hξ hx (ρ h v)) h]
  refine cosetSum_congr fun g => ?_
  simp only [mul_inv_rev, map_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The coefficient map as an intertwiner. -/
def coefficientIntertwiningMap (hU : IsOpen (U : Set G))
    (hξ : ∀ u ∈ U, ∀ v, ξ (ρ u v) = ξ v) (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v))
    (hx : ∀ u ∈ U, σ u x = x) : ρ.IntertwiningMap σ where
  toFun := coefficientMap ρ σ U ξ x
  map_add' := coefficientMap_add hU hc
  map_smul' := coefficientMap_smul hU hc
  isIntertwining' h := LinearMap.ext fun v => coefficientMap_apply_rep hU hξ hc hx h v

@[simp]
theorem coefficientIntertwiningMap_apply (hU : IsOpen (U : Set G))
    (hξ : ∀ u ∈ U, ∀ v, ξ (ρ u v) = ξ v) (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v))
    (hx : ∀ u ∈ U, σ u x = x) (v : V) :
    coefficientIntertwiningMap hU hξ hc hx v = coefficientMap ρ σ U ξ x v :=
  rfl

/-- Naturality: an intertwiner `f : σ → τ` carries the coefficient map of `(σ, x)` to that
of `(τ, f x)`. -/
theorem map_coefficientMap_intertwining {X : Type*} [AddCommGroup X] [Module k X]
    {τ : Representation k G X} (f : σ.IntertwiningMap τ) (hU : IsOpen (U : Set G))
    (hc : ∀ v, HasCompactSupport fun g => ξ (ρ g v)) (v : V) :
    f (coefficientMap ρ σ U ξ x v) = coefficientMap ρ τ U ξ (f x) v := by
  rw [map_coefficientMap f hU hc]
  unfold coefficientMap
  refine cosetSum_congr fun g => ?_
  rw [map_smul, f.isIntertwining]

end CoefficientMap

section NonVanishing

variable [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- A smooth representation with compactly supported coefficients and a nonzero vector has
a nonzero coefficient map `V → V` at a compact open subgroup. -/
theorem exists_coefficientMap_ne_zero (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (hc : ∀ (v : V) (ℓ : Module.Dual k V), IsSmoothVector ρ.dual ℓ →
      HasCompactSupport (matrixCoefficient ρ ℓ v)) {w : V} (hw : w ≠ 0) :
    ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ ∃ ξ : Module.Dual k V,
      ξ ∈ fixedVectors ρ.dual U.toSubgroup ∧ w ∈ fixedVectors ρ U.toSubgroup ∧
        coefficientMap ρ ρ U ξ w w ≠ 0 := by
  classical
  obtain ⟨U₀, -, hwU₀, ℓ, hℓU₀, hℓw⟩ := exists_dual_apply_ne_zero ρ hρ hw
  have hw₀ := mem_fixedVectors_iff.1 hwU₀
  have hℓ₀ := mem_fixedVectors_dual_iff.1 hℓU₀
  set F : G → k := fun g => ℓ (ρ g w) with hFdef
  have hF : HasCompactSupport F := hc w ℓ ⟨U₀, hℓU₀⟩
  have hF1 : F 1 ≠ 0 := by simpa [F] using hℓw
  -- the cosets of `U₀` meeting `(tsupport F)⁻¹`
  set C : Set G := (tsupport F)⁻¹
  have hC : IsCompact C := hF.isCompact.inv
  have hS := finite_image_mk (U := U₀.toSubgroup) U₀.isOpen hC
  set N : Set G := (U₀ : Set G) ∩
    ⋂ q ∈ (QuotientGroup.mk '' C : Set (G ⧸ U₀.toSubgroup)),
      {g | (q.out : G)⁻¹ * g * q.out ∈ U₀}
  have hN : N ∈ 𝓝 (1 : G) := by
    refine inter_mem U₀.mem_nhds_one ((Filter.biInter_mem hS).2 fun q _ => ?_)
    have hcont : Continuous fun g : G => (q.out : G)⁻¹ * g * q.out := by fun_prop
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using U₀.mem_nhds_one
  obtain ⟨U, hUc, hUN⟩ := exists_compact_openSubgroup_subset hN
  have hUU₀ : ∀ u ∈ U, u ∈ U₀ := fun u hu => (hUN hu).1
  have hl : ∀ u ∈ U.toSubgroup, ∀ g, F (u * g) = F g := fun u hu g => by
    simp only [F, map_mul, Module.End.mul_apply, hℓ₀ u (hUU₀ u hu)]
  have hr : RightInvariant U.toSubgroup F := fun g u hu => by
    simp only [F, map_mul, Module.End.mul_apply, hw₀ u (hUU₀ u hu)]
  obtain ⟨x, y, hx, hxy⟩ := exists_cosetSum_ne_zero U.isOpen hl hr hF hF1
  -- `U` lies in `x U₀ x⁻¹`
  have hxC : x ∈ C := by
    change x⁻¹ ∈ tsupport F
    exact subset_tsupport F hx
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U₀.toSubgroup x
  have hconj : ∀ u ∈ U, x⁻¹ * u * x ∈ U₀ := by
    intro u hu
    have h1 := Set.mem_iInter₂.1 (hUN hu).2 (QuotientGroup.mk x) ⟨x, hxC, rfl⟩
    simp only [Set.mem_ofPred_eq, hh] at h1
    have he : x⁻¹ * u * x = (h : G) * ((x * h)⁻¹ * u * (x * h)) * (h : G)⁻¹ := by group
    rw [he]
    exact U₀.mul_mem (U₀.mul_mem h.2 h1) (U₀.inv_mem h.2)
  have hξU : ℓ ∘ₗ ρ x⁻¹ ∈ fixedVectors ρ.dual U.toSubgroup := by
    rw [mem_fixedVectors_dual_iff]
    intro u hu v
    have he : x⁻¹ * u = (x⁻¹ * u * x) * x⁻¹ := by group
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply,
      hℓ₀ _ (hconj u hu)]
  refine ⟨U, hUc, ℓ ∘ₗ ρ x⁻¹, hξU, ?_, ?_⟩
  · rw [mem_fixedVectors_iff]
    exact fun u hu => hw₀ u (hUU₀ u hu)
  · intro h0
    have hc' : ∀ v, HasCompactSupport fun g => (ℓ ∘ₗ ρ x⁻¹) (ρ g v) := fun v =>
      hc v (ℓ ∘ₗ ρ x⁻¹) ⟨U, hξU⟩
    have h2 := congrArg (ℓ ∘ₗ ρ y⁻¹) h0
    rw [map_zero, map_coefficientMap (ℓ ∘ₗ ρ y⁻¹) U.isOpen hc'] at h2
    apply hxy
    rw [← h2]
    refine cosetSum_congr fun p => ?_
    simp only [F, LinearMap.comp_apply, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]

/-- For an irreducible smooth representation with compactly supported coefficients there
is a bijective coefficient map `V → V` at a compact open subgroup. -/
theorem exists_coefficientMap_bijective (ρ : Representation k G V) (hρ : IsSmooth ρ)
    [ρ.IsIrreducible]
    (hc : ∀ (v : V) (ℓ : Module.Dual k V), IsSmoothVector ρ.dual ℓ →
      HasCompactSupport (matrixCoefficient ρ ℓ v)) :
    ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ ∃ ξ : Module.Dual k V,
      ∃ hξ : ξ ∈ fixedVectors ρ.dual U.toSubgroup, ∃ w : V,
        ∃ hw : w ∈ fixedVectors ρ U.toSubgroup,
          Bijective (coefficientIntertwiningMap (σ := ρ) U.isOpen
            (mem_fixedVectors_dual_iff.1 hξ) (fun v => hc v ξ ⟨U, hξ⟩)
            (mem_fixedVectors_iff.1 hw)) := by
  obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible ρ
  obtain ⟨U, hUc, ξ, hξ, hwU, hne⟩ := exists_coefficientMap_ne_zero ρ hρ hc hw
  refine ⟨U, hUc, ξ, hξ, w, hwU, ?_⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero
    (coefficientIntertwiningMap (σ := ρ) U.isOpen (mem_fixedVectors_dual_iff.1 hξ)
      (fun v => hc v ξ ⟨U, hξ⟩) (mem_fixedVectors_iff.1 hwU)) with hb | h0
  · exact hb
  · have h1 := DFunLike.congr_fun h0 w
    simp only [Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at h1
    exact absurd h1 hne

end NonVanishing

end Langlands.Cohomology.SupercuspidalExtCharZero
