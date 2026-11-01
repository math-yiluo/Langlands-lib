import Langlands.Geometry.Analytic.OriginalChartDomains
import Mathlib.CategoryTheory.Sites.Grothendieck

/-! # Quasinet covering topology of fixed-original-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain

open Set CategoryTheory
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {S T : OriginalChartDomain a}

/-- The actual source subsets of all arrows in a domain sieve. -/
def sieveFamily (R : Sieve S) : Set (Set X) :=
  {U | ∃ (V : OriginalChartDomain a) (h : V ≤ S), R (homOfLE h) ∧ U = (V : Set X)}

theorem sieveFamily_subset (R : Sieve S) {U : Set X} (hU : U ∈ sieveFamily R) :
    U ⊆ S := by
  obtain ⟨V, hVS, _, rfl⟩ := hU
  exact hVS

theorem sieveFamily_mono {R Q : Sieve S} (h : R ≤ Q) :
    sieveFamily R ⊆ sieveFamily Q := by
  rintro U ⟨V, hVS, hR, rfl⟩
  exact ⟨V, hVS, h _ hR, rfl⟩

/-- At each target point, finitely many sieve domains all contain the point
and their union is a relative neighborhood in the target. -/
def IsCovering (R : Sieve S) : Prop :=
  AtlasTopology.LocallyRefines (sieveFamily R) {(S : Set X)}

/-- The covering condition is exactly a quasinet on the actual target
subspace, rather than pointwise surjectivity alone. -/
theorem isCovering_iff_isQuasinet (R : Sieve S) :
    IsCovering R ↔ AtlasTopology.IsQuasinet
      (AtlasTopology.restrictedFamily (sieveFamily R) (S : Set X)) :=
  (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).symm

theorem IsCovering.mono {R Q : Sieve S} (hR : IsCovering R) (hRQ : R ≤ Q) :
    IsCovering Q :=
  AtlasTopology.LocallyRefines.mono hR (sieveFamily_mono hRQ) Subset.rfl

theorem isCovering_top (S : OriginalChartDomain a) :
    IsCovering (⊤ : Sieve S) := by
  apply (AtlasTopology.LocallyRefines.refl {(S : Set X)}).mono ?_ Subset.rfl
  intro U hU
  obtain rfl := mem_singleton_iff.mp hU
  exact ⟨S, le_refl S, trivial, rfl⟩

/-- Base change is constructed by literal intersections of actual domains.
The finite relative neighborhood witnesses are intersected with the source. -/
theorem IsCovering.pullback {R : Sieve S} (hR : IsCovering R) (f : T ⟶ S) :
    IsCovering (R.pullback f) := by
  have h := hR.intersectionFamily (AtlasTopology.LocallyRefines.refl {(T : Set X)})
  rw [AtlasTopology.intersectionFamily_singletons,
    inter_eq_right.mpr (show (T : Set X) ⊆ S from leOfHom f)] at h
  apply h.mono ?_ Subset.rfl
  rintro U ⟨V, ⟨W, hWS, hRW, rfl⟩, V', hV', rfl⟩
  obtain rfl := mem_singleton_iff.mp hV'
  refine ⟨W ⊓ T, inf_le_right, ?_, rfl⟩
  change R (homOfLE (inf_le_right : W ⊓ T ≤ T) ≫ f)
  have heq : homOfLE (inf_le_right : W ⊓ T ≤ T) ≫ f =
      homOfLE (inf_le_left : W ⊓ T ≤ W) ≫ homOfLE hWS :=
    Subsingleton.elim _ _
  rw [heq]
  exact R.downward_closed hRW _

/-- Substitute finite relative neighborhood witnesses on the members of
a covering sieve, retaining the full local neighborhood condition. -/
theorem IsCovering.transitive {R : Sieve S} (hR : IsCovering R) (Q : Sieve S)
    (hQ : ∀ ⦃V⦄ ⦃f : V ⟶ S⦄, R f → IsCovering (Q.pullback f)) :
    IsCovering Q := by
  apply hR.trans
  rintro U ⟨V, hVS, hRV, rfl⟩ x hx
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    hQ hRV (V : Set X) (mem_singleton _) x hx
  refine ⟨σ, hf, ?_, hm, hn⟩
  rintro W hW
  obtain ⟨Z, hZV, hQZ, rfl⟩ := hs hW
  refine ⟨Z, hZV.trans hVS, ?_, rfl⟩
  exact hQZ

/-- The quasinet covering topology on the actual fixed-original-chart
domain category. Its objects retain their constructed affinoid atlases. -/
def quasinetTopology (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    GrothendieckTopology (OriginalChartDomain a) where
  sieves _ := {R | IsCovering R}
  top_mem' := isCovering_top
  pullback_stable' := by
    intro S T R f hR
    exact hR.pullback f
  transitive' := by
    intro S R hR Q hQ
    exact hR.transitive Q hQ

@[simp]
theorem mem_quasinetTopology (R : Sieve S) :
    R ∈ quasinetTopology a S ↔ IsCovering R := Iff.rfl

/-- A family with finite relative neighborhood witnesses generates a
covering sieve. Arbitrary index universes and empty families are allowed. -/
theorem ofArrows_mem_of_locallyRefines {ι : Type*}
    (D : ι → OriginalChartDomain a) (f : ∀ i, D i ⟶ S)
    (hD : AtlasTopology.LocallyRefines (Set.range (fun i => (D i : Set X)))
      {(S : Set X)}) :
    Sieve.ofArrows D f ∈ quasinetTopology a S := by
  apply hD.mono ?_ Subset.rfl
  rintro U ⟨i, rfl⟩
  refine ⟨D i, leOfHom (f i), ?_, rfl⟩
  have heq : homOfLE (leOfHom (f i)) = f i := Subsingleton.elim _ _
  rw [heq]
  exact Sieve.ofArrows_mk D f i

/-- Downward closure introduces no extra covering families: finite sieve
witnesses can be enlarged to finitely many of the generating domains. -/
theorem ofArrows_mem_iff_locallyRefines {ι : Type*}
    (D : ι → OriginalChartDomain a) (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows D f ∈ quasinetTopology a S ↔
      AtlasTopology.LocallyRefines (Set.range (fun i => (D i : Set X)))
        {(S : Set X)} := by
  classical
  constructor
  · intro h U hU x hx
    obtain rfl := mem_singleton_iff.mp hU
    obtain ⟨σ, hf, hs, hm, hn⟩ := h _ (mem_singleton _) x hx
    have hw : ∀ V : σ, ∃ i, V.val ⊆ (D i : Set X) := by
      intro V
      obtain ⟨W, hWS, hRW, hVW⟩ := hs V.property
      obtain ⟨i, g, _⟩ := (Sieve.mem_ofArrows_iff D f _).mp hRW
      refine ⟨i, ?_⟩
      rw [hVW]
      exact leOfHom g
    choose i hi using hw
    let : Fintype σ := hf.fintype
    refine ⟨Set.range (fun V : σ => (D (i V) : Set X)), finite_range _, ?_, ?_, ?_⟩
    · rintro V ⟨W, rfl⟩
      exact ⟨i W, rfl⟩
    · rintro V ⟨W, rfl⟩
      exact ⟨leOfHom (f (i W)), hi W (hm W.val W.property).2⟩
    · apply Filter.mem_of_superset hn
      rintro y ⟨V, hV, hy⟩
      exact ⟨D (i ⟨V, hV⟩), ⟨⟨V, hV⟩, rfl⟩, hi ⟨V, hV⟩ hy⟩
  · exact ofArrows_mem_of_locallyRefines D f

/-- Covering families are exactly quasinets on the actual target subspace. -/
theorem ofArrows_mem_iff_isQuasinet {ι : Type*}
    (D : ι → OriginalChartDomain a) (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows D f ∈ quasinetTopology a S ↔
      AtlasTopology.IsQuasinet
        (AtlasTopology.restrictedFamily (Set.range (fun i => (D i : Set X)))
          (S : Set X)) :=
  (ofArrows_mem_iff_locallyRefines D f).trans
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).symm

/-- The actual original charts contained in a domain form a covering family.
This follows from the domain's finite neighborhood condition. -/
theorem ofArrows_originalCharts_mem (S : OriginalChartDomain a) :
    Sieve.ofArrows
      (fun c : a.SubspaceChart (S : Set X) => ofChart c.val)
      (fun c => homOfLE (show ofChart c.val ≤ S from c.property)) ∈
        quasinetTopology a S := by
  apply ofArrows_mem_of_locallyRefines
  intro U hU x hx
  obtain rfl := mem_singleton_iff.mp hU
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    ((AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp S.is_domain)
      _ (mem_singleton _) x hx
  refine ⟨σ, hf, ?_, hm, hn⟩
  intro V hV
  obtain ⟨i, hi⟩ := hs hV
  refine ⟨⟨i, ?_⟩, hi⟩
  change Set.range (a.chart i) = V at hi
  rw [hi]
  exact (hm V hV).1

/-- Covering gives point coverage by actual domains belonging to the sieve. -/
theorem IsCovering.exists_mem {R : Sieve S} (hR : IsCovering R)
    {x : X} (hx : x ∈ S) :
    ∃ (V : OriginalChartDomain a) (hVS : V ≤ S), R (homOfLE hVS) ∧ x ∈ V := by
  obtain ⟨σ, _, hs, _, hn⟩ := hR _ (mem_singleton _) x hx
  obtain ⟨U, hU, hxU⟩ := mem_of_mem_nhdsWithin hx hn
  obtain ⟨V, hVS, hRV, rfl⟩ := hs hU
  exact ⟨V, hVS, hRV, hxU⟩

/-- The empty sieve covers exactly the empty actual domain. -/
theorem bot_mem_quasinetTopology_iff (S : OriginalChartDomain a) :
    (⊥ : Sieve S) ∈ quasinetTopology a S ↔ S = ⊥ := by
  constructor
  · intro h
    apply SetLike.coe_injective
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨V, hVS, hV, _⟩ := h.exists_mem hx
    exact hV
  · rintro rfl
    intro U hU x hx
    obtain rfl := mem_singleton_iff.mp hU
    exact False.elim hx

end Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain
