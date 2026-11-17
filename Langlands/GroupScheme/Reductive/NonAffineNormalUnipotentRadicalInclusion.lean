import Langlands.GroupScheme.Reductive.NonAffineUnipotentRadicalAction

/-! # Radicals of normal subgroups in smooth nonaffine ambient groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H U V : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom]
    {r : U ⟶ G} {s : V ⟶ H}

/-- Ambient conjugation acts on the radical of a normal closed
subgroup, as an actual automorphic action. -/
def IsUnipotentRadical.normalAmbientActionOfSmooth
    (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) : AutomorphicAction G V := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact hs.actionOfSmooth (AutomorphicAction.ofNormalizedConjugation i (𝟙 G)
    (fun T g h _ hh => hn T g h (Subgroup.mem_top _) hh))

/-- The action on the subgroup radical is ambient conjugation after its
composite inclusion. -/
theorem IsUnipotentRadical.normalAmbientActionOfSmooth_act_comp
    (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (v : T ⟶ V.X) :
    (hs.normalAmbientActionOfSmooth i hi hn).act g v ≫ (s ≫ i).hom.hom =
      g * (v ≫ (s ≫ i).hom.hom) * g⁻¹ := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change (hs.actionOfSmooth (AutomorphicAction.ofNormalizedConjugation i (𝟙 G)
    (fun T g h _ hh => hn T g h (Subgroup.mem_top _) hh))).act g v ≫
      (s ≫ i).hom.hom = _
  rw [Grp.comp_hom_hom, ← Category.assoc, hs.actionOfSmooth_isEquivariant]
  simpa only [Grp.id_hom_hom, Category.comp_id, Category.assoc] using
    (AutomorphicAction.ofNormalizedConjugation_act_comp i (𝟙 G)
      (fun T g h _ hh => hn T g h (Subgroup.mem_top _) hh)
      g (v ≫ s.hom.hom))

/-- The radical of a normal closed subgroup is normal in the
ambient smooth group, on all test schemes. -/
theorem IsUnipotentRadical.isNormal_comp_of_smooth
    (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    (SubgroupFunctor.range (s ≫ i)).IsNormal := by
  intro T g x _ hx
  obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  exact SubgroupFunctor.mem_range.2
    ⟨(hs.normalAmbientActionOfSmooth i hi hn).act g v,
      hs.normalAmbientActionOfSmooth_act_comp i hi hn g v⟩

/-- The subgroup radical maps into any supplied ambient radical. -/
theorem IsUnipotentRadical.range_comp_le_of_smooth
    (hs : IsUnipotentRadical s) (hr : IsUnipotentRadical r)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    SubgroupFunctor.range (s ≫ i) ≤ SubgroupFunctor.range r :=
  hr.greatest V (s ≫ i) (hs.isClosedSubgroup.comp hi) hs.smooth
    hs.connectedSpace hs.isUnipotent (hs.isNormal_comp_of_smooth i hi hn)

end Langlands.GroupScheme
