import Langlands.GroupScheme.Reductive.UnipotentRadicalAction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # The radical of a normal subgroup inside the ambient radical -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section GeneralBase

variable {B : Scheme.{u}} {G H K : GroupScheme B}

/-- The normalized conjugation action has the original ambient conjugation
formula on every test scheme. -/
theorem AutomorphicAction.ofNormalizedConjugation_act_comp
    (i : H ⟶ G) (j : K ⟶ G)
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j))
    [Mono i.hom.hom] {T : Over B} (g : T ⟶ K.X) (h : T ⟶ H.X) :
    (AutomorphicAction.ofNormalizedConjugation i j hn).act g h ≫ i.hom.hom =
      (g ≫ j.hom.hom) * (h ≫ i.hom.hom) * (g ≫ j.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp i j hn g h

end GeneralBase

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H U V : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    {r : U ⟶ G} {s : V ⟶ H}

/-- Ambient conjugation acts on the radical of a smooth connected normal
subgroup, as an actual automorphic action. -/
def IsUnipotentRadical.normalAmbientAction
    (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) : AutomorphicAction G V := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact hs.action (AutomorphicAction.ofNormalizedConjugation i (𝟙 G)
    (fun T g h _ hh => hn T g h (Subgroup.mem_top _) hh))

/-- The action on the subgroup radical is ambient conjugation after its
composite inclusion. -/
theorem IsUnipotentRadical.normalAmbientAction_act_comp
    (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (v : T ⟶ V.X) :
    (hs.normalAmbientAction i hi hn).act g v ≫ (s ≫ i).hom.hom =
      g * (v ≫ (s ≫ i).hom.hom) * g⁻¹ := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change (hs.action (AutomorphicAction.ofNormalizedConjugation i (𝟙 G)
    (fun T g h _ hh => hn T g h (Subgroup.mem_top _) hh))).act g v ≫
      (s ≫ i).hom.hom = _
  rw [Grp.comp_hom_hom, ← Category.assoc, hs.action_isEquivariant]
  simpa only [Grp.id_hom_hom, Category.comp_id, Category.assoc] using
    (AutomorphicAction.ofNormalizedConjugation_act_comp i (𝟙 G)
      (fun T g h _ hh => hn T g h (Subgroup.mem_top _) hh)
      g (v ≫ s.hom.hom))

/-- The radical of a normal smooth connected subgroup is normal in the
ambient smooth group, on all test schemes. -/
theorem IsUnipotentRadical.isNormal_comp
    (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    (SubgroupFunctor.range (s ≫ i)).IsNormal := by
  intro T g x _ hx
  obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  exact SubgroupFunctor.mem_range.2
    ⟨(hs.normalAmbientAction i hi hn).act g v,
      hs.normalAmbientAction_act_comp i hi hn g v⟩

/-- The subgroup radical maps into any supplied ambient radical. -/
theorem IsUnipotentRadical.range_comp_le
    (hs : IsUnipotentRadical s) (hr : IsUnipotentRadical r)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    SubgroupFunctor.range (s ≫ i) ≤ SubgroupFunctor.range r :=
  hr.greatest V (s ≫ i) (hs.isClosedSubgroup.comp hi) hs.smooth
    hs.connectedSpace hs.isUnipotent (hs.isNormal_comp i hi hn)

/-- One direction of the full radical-intersection comparison, retaining
arbitrary test schemes. -/
theorem IsUnipotentRadical.le_comap
    (hs : IsUnipotentRadical s) (hr : IsUnipotentRadical r)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    SubgroupFunctor.range s ≤ (SubgroupFunctor.range r).comap i := by
  intro T x hx
  obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  change (v ≫ s.hom.hom) ≫ i.hom.hom ∈ (SubgroupFunctor.range r).carrier T
  exact hs.range_comp_le hr i hi hn T
    (SubgroupFunctor.mem_range.2 ⟨v, by simp only [Grp.comp_hom_hom, Category.assoc]⟩)

/-- The canonical homomorphism from the radical of the normal subgroup to
the supplied ambient radical, over the original composite inclusion. -/
def IsUnipotentRadical.normalSubgroupFactor
    (hr : IsUnipotentRadical r) (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) : V ⟶ U := by
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  exact (show (SubgroupFunctor.range r).IsRepresentedBy r from
    ⟨inferInstance, rfl⟩).factorHom (s ≫ i) (hs.range_comp_le hr i hi hn)

@[simp] theorem IsUnipotentRadical.normalSubgroupFactor_comp
    (hr : IsUnipotentRadical r) (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    hr.normalSubgroupFactor hs i hi hn ≫ r = s ≫ i := by
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  exact (show (SubgroupFunctor.range r).IsRepresentedBy r from
    ⟨inferInstance, rfl⟩).factorHom_comp (s ≫ i) (hs.range_comp_le hr i hi hn)

/-- The radical factor is a closed subgroup inclusion. -/
theorem IsUnipotentRadical.normalSubgroupFactor_isClosedSubgroup
    (hr : IsUnipotentRadical r) (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    IsClosedSubgroup (hr.normalSubgroupFactor hs i hi hn) :=
  IsClosedSubgroup.of_comp hr.isClosedSubgroup
    (by rw [hr.normalSubgroupFactor_comp]; exact hs.isClosedSubgroup.comp hi)

/-- The inclusion in the ambient radical uniquely determines the factor. -/
theorem IsUnipotentRadical.normalSubgroupFactor_unique
    (hr : IsUnipotentRadical r) (hs : IsUnipotentRadical s)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (f : V ⟶ U) (hf : f ≫ r = s ≫ i) :
    f = hr.normalSubgroupFactor hs i hi hn := by
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  apply hom_ext_points
  intro T v
  apply (cancel_mono r.hom.hom).mp
  have he := congrArg (fun a => a.hom.hom) (hf.trans
    (hr.normalSubgroupFactor_comp hs i hi hn).symm)
  simpa only [Grp.comp_hom_hom, Category.assoc] using congrArg (fun a => v ≫ a) he

end Langlands.GroupScheme
