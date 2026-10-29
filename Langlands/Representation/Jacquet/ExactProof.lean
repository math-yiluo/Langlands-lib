import Langlands.Representation.Compact.OrbitMeanTranslation
import Langlands.Representation.Jacquet.ExactStatement
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

namespace Langlands

open Representation
open scoped BigOperators

universe uG uU uV uW

section Algebra
variable {G : Type uG} [Group G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Restricting the acting group only removes coinvariant relations. -/
theorem coinvariants_ker_comp_subgroup_le (ρ : Representation ℂ G V) (K : Subgroup G) :
    Coinvariants.ker (ρ.comp K.subtype) ≤ Coinvariants.ker ρ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, v⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ) g.val v

/-- Finite averaging preserves the class of a vector in the coinvariants. -/
theorem Compact.mk_orbitMean (ρ : Representation ℂ G V) (v : V)
    [Finite (Compact.orbit ρ v)] :
    Coinvariants.mk ρ (Compact.orbitMean ρ v) = Coinvariants.mk ρ v := by
  classical
  let := Fintype.ofFinite (Compact.orbit ρ v)
  have hval (x : Compact.orbit ρ v) : Coinvariants.mk ρ x.val = Coinvariants.mk ρ v := by
    obtain ⟨g, hg⟩ := x.property
    rw [← hg]
    exact Coinvariants.mk_self_apply ρ g v
  have hcard : (Fintype.card (Compact.orbit ρ v) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Compact.orbitMean_eq_finiteMean]
  simp only [Compact.finiteMean, map_smul, map_sum, hval, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard,
    one_smul]

/-- A surjective intertwiner maps the relation submodule onto the target relations. -/
theorem coinvariants_ker_map_of_surjective
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (p : ρ.IntertwiningMap τ) (hp : Function.Surjective p) :
    (Coinvariants.ker ρ).map p.toLinearMap = Coinvariants.ker τ := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change p (ρ g v - v) ∈ Coinvariants.ker τ
    rw [map_sub, p.isIntertwining]
    exact Coinvariants.sub_mem_ker g (p v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨ρ g v - v, Coinvariants.sub_mem_ker g v, ?_⟩
    exact (map_sub p _ _).trans (congrArg (fun z => z - p v) (p.isIntertwining ρ τ g v))

/-- Coinvariants preserve surjections without a smoothness or topology hypothesis. -/
theorem coinvariants_map_surjective
    {σ : Representation ℂ G V} {τ : Representation ℂ G W}
    (p : σ.IntertwiningMap τ) (hp : Function.Surjective p) :
    Function.Surjective (Coinvariants.map σ τ p) := by
  intro x
  obtain ⟨w, rfl⟩ := Coinvariants.mk_surjective τ x
  obtain ⟨v, rfl⟩ := hp w
  exact ⟨Coinvariants.mk σ v, rfl⟩

/-- The algebraic middle exactness of coinvariants. -/
theorem coinvariants_map_range_eq_ker
    {ρ : Representation ℂ G U} {σ : Representation ℂ G V} {τ : Representation ℂ G W}
    (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap τ)
    (hp : Function.Surjective p)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    LinearMap.range (Coinvariants.map ρ σ i) = LinearMap.ker (Coinvariants.map σ τ p) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := Coinvariants.mk_surjective ρ x
    have hpu : p (i u) = 0 := by
      change i u ∈ LinearMap.ker p.toLinearMap
      rw [← hex]
      exact ⟨u, rfl⟩
    change Coinvariants.mk τ (p (i u)) = 0
    rw [hpu, map_zero]
  · intro x hx
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective σ x
    have hpv : p v ∈ Coinvariants.ker τ := (Coinvariants.mk_eq_zero τ).mp hx
    rw [← coinvariants_ker_map_of_surjective p hp] at hpv
    obtain ⟨z, hz, hpz⟩ := hpv
    change p z = p v at hpz
    have hvz : v - z ∈ LinearMap.range i.toLinearMap := by
      rw [hex]
      change p (v - z) = 0
      rw [map_sub, hpz, sub_self]
    obtain ⟨u, hu⟩ := hvz
    refine ⟨Coinvariants.mk ρ u, ?_⟩
    change Coinvariants.mk σ (i u) = Coinvariants.mk σ v
    change i u = v - z at hu
    rw [hu, map_sub, (Coinvariants.mk_eq_zero σ).mpr hz, sub_zero]

end Algebra

section Topology
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

omit [IsTopologicalGroup G] in
/-- A relation involves only finitely many group elements, hence one compact open subgroup. -/
theorem coinvariants_mem_ker_iff_compact
    (hG : ∀ s : Finset G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ ∀ g ∈ s, g ∈ K)
    (ρ : Representation ℂ G V) (v : V) :
    v ∈ Coinvariants.ker ρ ↔ ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      v ∈ Coinvariants.ker (ρ.comp K.toSubgroup.subtype) := by
  classical
  constructor
  · intro hv
    obtain ⟨T, hT, hvT⟩ := Submodule.mem_span_finite_of_mem_span hv
    choose gv hgv using hT
    let s : Finset G := T.attach.image (fun x => (gv x.property).1)
    obtain ⟨K, hK, hsK⟩ := hG s
    refine ⟨K, hK, ?_⟩
    apply (Submodule.span_le.mpr ?_) hvT
    intro x hx
    have hg : (gv hx).1 ∈ K :=
      hsK _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
    exact Coinvariants.mem_ker_of_eq (ρ := ρ.comp K.toSubgroup.subtype)
      ⟨(gv hx).1, hg⟩ (gv hx).2 x (hgv hx)
  · rintro ⟨K, _, hv⟩
    exact coinvariants_ker_comp_subgroup_le ρ K.toSubgroup hv

/-- The kernel of compact averaging is exactly the compact-subgroup relation span. -/
theorem Compact.averageMap_eq_zero_iff (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V) :
    Compact.averageMap ρ hρ K hK v = 0 ↔
      v ∈ Coinvariants.ker (ρ.comp K.toSubgroup.subtype) := by
  constructor
  · intro hv
    let := Compact.finite_orbit_of_smooth ρ hρ K hK v
    apply (Coinvariants.mk_eq_zero _).mp
    rw [← Compact.mk_orbitMean (ρ.comp K.toSubgroup.subtype) v]
    change Coinvariants.mk _ (Compact.averageMap ρ hρ K hK v) = 0
    rw [hv, map_zero]
  · intro hv
    have hle : Coinvariants.ker (ρ.comp K.toSubgroup.subtype) ≤
        LinearMap.ker (Compact.averageMap ρ hρ K hK) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, x⟩, rfl⟩
      change Compact.averageMap ρ hρ K hK (_ - _) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (Compact.orbitMean_apply (ρ.comp K.toSubgroup.subtype) g x)
    exact hle hv

/-- Coinvariants preserve injections into smooth complex representations under finite containment. -/
theorem coinvariants_map_injective_of_smooth
    (hG : ∀ s : Finset G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ ∀ g ∈ s, g ∈ K)
    {ρ : Representation ℂ G U} {σ : Representation ℂ G V}
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) (hσ : IsSmooth σ) :
    Function.Injective (Coinvariants.map ρ σ i) := by
  have hρ := isSmooth_of_injective i hi hσ
  suffices hz : ∀ x, Coinvariants.map ρ σ i x = 0 → x = 0 from
    fun x y h => sub_eq_zero.mp (hz (x - y) (by simp [map_sub, h]))
  intro x
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ x
  intro hv
  have hiv : i v ∈ Coinvariants.ker σ := (Coinvariants.mk_eq_zero σ).mp hv
  obtain ⟨K, hK, hivK⟩ := (coinvariants_mem_ker_iff_compact hG σ (i v)).mp hiv
  have hav : Compact.averageMap ρ hρ K hK v = 0 := by
    apply hi
    rw [map_zero]
    have hc := LinearMap.congr_fun (Compact.averageMap_commute ρ σ hρ hσ K hK i) v
    exact hc.trans ((Compact.averageMap_eq_zero_iff σ hσ K hK (i v)).mpr hivK)
  apply (Coinvariants.mk_eq_zero ρ).mpr
  exact coinvariants_ker_comp_subgroup_le ρ K.toSubgroup
    ((Compact.averageMap_eq_zero_iff ρ hρ K hK v).mp hav)

end Topology

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Compact detection and exactness, with exactly the published target telescope. -/
theorem smoothCoinvariantExactness :
    SmoothCoinvariantExactnessStatement (G := G) (U := U) (V := V) (W := W) := by
  intro _ hG
  constructor
  · intro ρ _ v
    exact coinvariants_mem_ker_iff_compact hG ρ v
  · intro ρ σ τ i p hi hp hex hσ
    exact ⟨coinvariants_map_injective_of_smooth hG i hi hσ,
      coinvariants_map_range_eq_ker i p hp hex, coinvariants_map_surjective p hp⟩

end Langlands
