import Langlands.GroupScheme.Reductive.FiniteCentralizerNeighbourhood
import Langlands.GroupScheme.Dynamic.CentralizerRestriction

/-! # Restricting radical-free root centralizers to a closed subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Dynamic

variable {B : Scheme.{u}} {G M L : GroupScheme B}

/-- An ambient cocharacter centralizer contained in a monic subgroup is the
centralizer of that same cocharacter in the subgroup. -/
theorem isRepresentedBy_factorHom_centralizer
    (q : M ⟶ G) [Mono q.hom.hom]
    (χ : (Gm B).toGrp ⟶ M) (l : L ⟶ G)
    (hl : (centralizer (χ ≫ q)).IsRepresentedBy l)
    (hle : SubgroupFunctor.range l ≤ SubgroupFunctor.range q) :
    (centralizer χ).IsRepresentedBy
      ((show (SubgroupFunctor.range q).IsRepresentedBy q from
        ⟨inferInstance, rfl⟩).factorHom l hle) := by
  let hq : (SubgroupFunctor.range q).IsRepresentedBy q := ⟨inferInstance, rfl⟩
  let f := hq.factorHom l hle
  have hf : f ≫ q = l := hq.factorHom_comp l hle
  have : Mono l.hom.hom := hl.1
  have : Mono f.hom.hom := mono_of_mono_fac (congrArg (fun z => z.hom.hom) hf)
  change (centralizer χ).IsRepresentedBy f
  refine ⟨inferInstance, ?_⟩
  ext V x
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    apply (mem_centralizer_comp_iff q χ _).mp
    rw [← hl.2]
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨y, by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        (congrArg (fun z : L ⟶ G => y ≫ z.hom.hom) hf).symm⟩
  · intro hx
    have hx' := (mem_centralizer_comp_iff q χ x).mpr hx
    rw [← hl.2] at hx'
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx'
    refine ⟨y, (cancel_mono q.hom.hom).mp ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      (congrArg (fun z : L ⟶ G => y ≫ z.hom.hom) hf).trans hy

end Dynamic

namespace RadicalFreeRootCentralizerData

variable {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ M) (q : M ⟶ G) [Mono q.hom.hom]
    {α : characterLattice T}

/-- Restrict an actual radical-free root centralizer to a monic subgroup
containing its entire all-test range. -/
def restrict
    (d : RadicalFreeRootCentralizerData (t ≫ q) α)
    (hle : SubgroupFunctor.range d.inclusion ≤ SubgroupFunctor.range q) :
    RadicalFreeRootCentralizerData t α where
  cocharacter := d.cocharacter
  groupScheme := d.groupScheme
  inclusion := (show (SubgroupFunctor.range q).IsRepresentedBy q from
    ⟨inferInstance, rfl⟩).factorHom d.inclusion hle
  represents := Dynamic.isRepresentedBy_factorHom_centralizer q
    (CommGroupScheme.groupHom d.cocharacter ≫ t) d.inclusion
    (by simpa only [Category.assoc] using d.represents) hle
  annihilates := d.annihilates
  radical := d.radical

end RadicalFreeRootCentralizerData

/-- A smooth connected closed subgroup is reductive when it contains a split
self-centralizing torus and radical-free ambient centralizers for each of its
actual roots. Each ambient centralizer must be contained on all scheme tests. -/
theorem isConnectedReductive_of_contained_rootCentralizers
    {k : Type u} [Field k] [IsAlgClosed k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ M) (q : M ⟶ G) (hq : IsClosedSubgroup q)
    (hT : IsSplitTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hself : torusCentralizer t = SubgroupFunctor.range t)
    (hsmall : ∀ (α : characterLattice T) (_ : α ∈ roots t),
      ∃ d : RadicalFreeRootCentralizerData (t ≫ q) α,
        SubgroupFunctor.range d.inclusion ≤ SubgroupFunctor.range q) :
    IsConnectedReductive M := by
  let : IsClosedImmersion q.hom.hom.left := hq
  let : Mono q.hom.hom := Over.mono_of_mono_left _
  apply RadicalFreeRootCentralizerData.isConnectedReductive t hT ht hself
  intro α hα
  obtain ⟨d, hd⟩ := hsmall α hα
  exact ⟨d.restrict t q hd⟩

end Langlands.GroupScheme
