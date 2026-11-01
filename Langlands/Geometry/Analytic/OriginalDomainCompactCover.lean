import Langlands.Geometry.Analytic.OriginalDomainTopology
import Mathlib.Topology.Compactness.Compact

/-! # Finite original-chart refinements on compact Hausdorff domains -/

noncomputable section

universe u v w t

namespace Langlands.Analytic

open Set Filter Topology CategoryTheory
open scoped Topology

namespace AtlasTopology

variable {X : Type v} [TopologicalSpace X]

/-- Compactness collects finitely many finite relative neighborhood witnesses
into a finite family whose union is exactly the target subset. -/
theorem LocallyRefines.exists_finite_cover {υ : Set (Set X)} {S : Set X}
    (h : LocallyRefines υ {S}) (hS : IsCompact S) :
    ∃ σ : Set (Set X), σ.Finite ∧ σ ⊆ υ ∧ ⋃₀ σ = S := by
  classical
  have hw : ∀ x : S, ∃ σ : Set (Set X),
      σ.Finite ∧ σ ⊆ υ ∧ (∀ V ∈ σ, V ⊆ S ∧ x.val ∈ V) ∧
        ⋃₀ σ ∈ 𝓝[S] x.val :=
    fun x => h S (mem_singleton _) x.val x.property
  choose σ hf hs hm hn using hw
  obtain ⟨I, hI⟩ := hS.elim_nhdsWithin_subcover'
    (fun x hx => ⋃₀ σ ⟨x, hx⟩) (fun x hx => hn ⟨x, hx⟩)
  let δ : Set (Set X) := ⋃ x : I, σ x.val
  refine ⟨δ, finite_iUnion (fun x : I => hf x.val), ?_, ?_⟩
  · intro V hV
    obtain ⟨x, hx⟩ := mem_iUnion.mp hV
    exact hs x.val hx
  · apply Subset.antisymm
    · rintro x ⟨V, hV, hx⟩
      obtain ⟨y, hy⟩ := mem_iUnion.mp hV
      exact (hm y.val V hy).1 hx
    · intro x hx
      obtain ⟨y, hyI, V, hV, hxV⟩ := mem_iUnion₂.mp (hI hx)
      exact ⟨V, mem_iUnion.mpr ⟨⟨y, hyI⟩, hV⟩, hxV⟩

/-- The finite subcover can retain indices of the actual supplied family. -/
theorem LocallyRefines.exists_finset_cover {ι : Type t} {D : ι → Set X} {S : Set X}
    (h : LocallyRefines (Set.range D) {S}) (hS : IsCompact S) :
    ∃ I : Finset ι, (⋃ i ∈ I, D i) = S := by
  classical
  obtain ⟨σ, hf, hs, hσ⟩ := h.exists_finite_cover hS
  have hw : ∀ V : σ, ∃ i, D i = V.val := fun V => hs V.property
  choose i hi using hw
  let : Fintype σ := hf.fintype
  refine ⟨Finset.univ.image i, ?_⟩
  rw [← hσ]
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨V.val, V.property, hi V ▸ hxj⟩
  · rintro ⟨V, hV, hxV⟩
    exact mem_iUnion₂.mpr ⟨i ⟨V, hV⟩,
      Finset.mem_image.mpr ⟨⟨V, hV⟩, Finset.mem_univ _, rfl⟩,
      (hi ⟨V, hV⟩).symm ▸ hxV⟩

/-- A finite closed family covering the space is a quasinet. At a point,
remove the closed union of members that do not contain that point. -/
theorem isQuasinet_of_finite_closed_cover {τ : Set (Set X)}
    (hf : τ.Finite) (hc : ∀ V ∈ τ, IsClosed V) (hcover : ⋃₀ τ = Set.univ) :
    IsQuasinet τ := by
  classical
  intro x
  let σ : Set (Set X) := {V ∈ τ | x ∈ V}
  refine ⟨σ, hf.subset (fun _ hV => hV.1),
    fun _ hV => hV.1, fun _ hV => hV.2, ?_⟩
  have hclosed : IsClosed (⋃₀ (τ \ σ)) :=
    (hf.subset Set.sdiff_subset).isClosed_sUnion (fun V hV => hc V hV.1)
  have hx : x ∈ (⋃₀ (τ \ σ))ᶜ := by
    rintro ⟨V, hV, hxV⟩
    exact hV.2 ⟨hV.1, hxV⟩
  apply Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hx)
  intro y hy
  have hycover : y ∈ ⋃₀ τ := hcover.symm ▸ Set.mem_univ y
  obtain ⟨V, hV, hyV⟩ := hycover
  by_cases hxV : x ∈ V
  · exact ⟨V, ⟨hV, hxV⟩, hyV⟩
  · exact False.elim (hy ⟨V, ⟨hV, fun h => hxV h.2⟩, hyV⟩)

end AtlasTopology

namespace IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {S : OriginalChartDomain a}

/-- An actual original chart contained in S whose inclusion belongs to R. -/
def SieveChart (R : Sieve S) :=
  {c : a.SubspaceChart S.carrier //
    R (homOfLE (show ofChart c.val ≤ S from c.property))}

namespace SieveChart

variable {R : Sieve S}

def domain (c : SieveChart R) : OriginalChartDomain a := ofChart c.val.val

def inclusion (c : SieveChart R) : c.domain ⟶ S := homOfLE c.val.property

theorem mem (c : SieveChart R) : R c.inclusion := c.property

end SieveChart

/-- The actual subset family of original charts already belonging to a sieve. -/
def sieveChartFamily (R : Sieve S) : Set (Set X) :=
  Set.range (fun c : SieveChart R => (c.domain : Set X))

/-- Original charts in a sieve give relative local refinements of every one
of its domains, by the actual contained-chart domain condition. -/
theorem sieveChartFamily_locallyRefines (R : Sieve S) :
    AtlasTopology.LocallyRefines (sieveChartFamily R) (sieveFamily R) := by
  rintro U ⟨V, hVS, hRV, rfl⟩ x hx
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp V.is_domain
      V.carrier (mem_singleton _) x hx
  refine ⟨σ, hf, ?_, hm, hn⟩
  intro W hW
  obtain ⟨i, hi⟩ := hs hW
  change Set.range (a.chart i) = W at hi
  have hiV : ofChart i ≤ V := by
    change Set.range (a.chart i) ⊆ V.carrier
    rw [hi]
    exact (hm W hW).1
  exact ⟨⟨⟨i, hiV.trans hVS⟩, R.downward_closed hRV (homOfLE hiV)⟩, hi⟩

/-- Every covering sieve admits a covering refinement by its original charts,
without compactness or ambient Hausdorffness. -/
theorem IsCovering.sieveChartFamily {R : Sieve S} (hR : IsCovering R) :
    AtlasTopology.LocallyRefines (sieveChartFamily R) {S.carrier} :=
  hR.trans (sieveChartFamily_locallyRefines R)

/-- A finite family of actual original-chart inclusions in the given sieve. -/
def finiteChartSieve (R : Sieve S) (I : Finset (SieveChart R)) : Sieve S :=
  Sieve.ofArrows (fun c : I => c.val.domain) (fun c => c.val.inclusion)

theorem finiteChartSieve_le (R : Sieve S) (I : Finset (SieveChart R)) :
    finiteChartSieve R I ≤ R := by
  intro V f hf
  obtain ⟨c, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ f).mp hf
  exact R.downward_closed c.val.mem g

/-- Finite point covers by original charts are genuine quasinet covers
when the target domain is Hausdorff. -/
theorem finiteChartSieve_mem_of_covers [T2Space S.carrier]
    (R : Sieve S) (I : Finset (SieveChart R))
    (hcover : (⋃ c ∈ I, (c.domain : Set X)) = S.carrier) :
    finiteChartSieve R I ∈ quasinetTopology a S := by
  apply ofArrows_mem_of_locallyRefines
  apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp
  let τ : Set (Set S.carrier) :=
    Set.range (fun c : I => (Subtype.val ⁻¹' (c.val.domain : Set X) : Set S.carrier))
  have hτ : AtlasTopology.IsQuasinet τ := by
    apply AtlasTopology.isQuasinet_of_finite_closed_cover (Set.finite_range _) ?_ ?_
    · rintro V ⟨c, rfl⟩
      have hcompact : IsCompact
          (Subtype.val ⁻¹' (c.val.domain : Set X) : Set S.carrier) := by
        apply Subtype.isCompact_iff.mpr
        have heq : Subtype.val ''
            (Subtype.val ⁻¹' (c.val.domain : Set X) : Set S.carrier) =
              (c.val.domain : Set X) := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact hy
          · intro hx
            exact ⟨⟨x, c.val.val.property hx⟩, hx, rfl⟩
        rw [heq]
        exact isCompact_range (a.isEmbedding_chart c.val.val.val).continuous
      exact hcompact.isClosed
    · apply Set.eq_univ_of_forall
      intro x
      have hx : x.val ∈ ⋃ c ∈ I, (c.domain : Set X) := hcover.symm ▸ x.property
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
      exact ⟨_, ⟨⟨c, hc⟩, rfl⟩, hxc⟩
  apply hτ.mono
  rintro V ⟨c, rfl⟩
  exact ⟨c.val.domain, ⟨c, rfl⟩, c.val.val.property, rfl⟩

/-- Compact Hausdorff original-chart domains have finite original-chart
covering refinements inside every arbitrary covering sieve. -/
theorem exists_finite_chart_cover [T2Space S.carrier] (hS : IsCompact S.carrier)
    (R : Sieve S) (hR : R ∈ quasinetTopology a S) :
    ∃ I : Finset (SieveChart R), finiteChartSieve R I ∈ quasinetTopology a S := by
  obtain ⟨I, hI⟩ := hR.sieveChartFamily.exists_finset_cover hS
  exact ⟨I, finiteChartSieve_mem_of_covers R I hI⟩

/-- A constructed finite original-chart refinement of the covering sieve. -/
def compactChartRefinement [T2Space S.carrier] (hS : IsCompact S.carrier)
    (R : Sieve S) (hR : R ∈ quasinetTopology a S) : Finset (SieveChart R) :=
  Classical.choose (exists_finite_chart_cover hS R hR)

theorem compactChartRefinement_mem [T2Space S.carrier] (hS : IsCompact S.carrier)
    (R : Sieve S) (hR : R ∈ quasinetTopology a S) :
    finiteChartSieve R (compactChartRefinement hS R hR) ∈ quasinetTopology a S :=
  Classical.choose_spec (exists_finite_chart_cover hS R hR)

/-- A sieve on a compact Hausdorff domain covers exactly when it contains
one of these finite covering families of actual original charts. -/
theorem mem_quasinetTopology_iff_finite_chart_cover [T2Space S.carrier]
    (hS : IsCompact S.carrier) (R : Sieve S) :
    R ∈ quasinetTopology a S ↔
      ∃ I : Finset (SieveChart R), finiteChartSieve R I ∈ quasinetTopology a S := by
  constructor
  · exact exists_finite_chart_cover hS R
  · rintro ⟨I, hI⟩
    exact hI.mono (finiteChartSieve_le R I)

end IndexedAffinoidAtlas.OriginalChartDomain

end Langlands.Analytic
