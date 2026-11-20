import Langlands.GroupScheme.FiniteTypeIdentityComponent
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.RelativeIdentityComponent.OpenConstruction
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Langlands.GroupScheme.Torus.ConnectedCentralizerNormalizer
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Openness of a torus centralizer in its normalizer over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open Langlands.AlgebraicGeometry
open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)
open Langlands.CategoryTheory.GroupObjectDescent
open SubgroupFunctor

section Field

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)

private theorem exists_clopen_neutralSubgroup (N : GroupScheme S) [LocallyOfFiniteType N.X.hom] :
    ∃ (P : GroupScheme S) (j : P ⟶ N),
      IsOpenImmersion j.hom.hom.left ∧ IsClosedSubgroup j ∧ ConnectedSpace P.X.left ∧
      Set.range j.hom.hom.left = IdentityComponent.identitySet N :=
  ⟨finiteTypeIdentityComponent N, finiteTypeIdentityComponentι N, inferInstance,
    IdentityComponent.FiniteType.isClosedSubgroup_finiteTypeIdentityComponentι N, inferInstance,
    IdentityComponent.FiniteType.range_finiteTypeIdentityComponentι N⟩

private theorem range_le_postcomp {G H N : GroupScheme S} (q : H ⟶ N) (n : N ⟶ G) :
    range (q ≫ n) ≤ range n := by
  intro U x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  exact mem_range.mpr ⟨y ≫ q.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩

set_option maxHeartbeats 1200000 in
private theorem centralizer_open_in_normalizer_of_isSplitTorus
    {G H N : GroupScheme S} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [GeometricallyConnected H.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (he : range i = torusCentralizer t)
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : range n ≤ (range i).normalizer)
    (a : H ⟶ N) (ha : a ≫ n = i) : IsOpenImmersion a.hom.hom.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion n.hom.hom.left := hn
  have : Mono n.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion i.hom.hom.left := hi
  have : LocallyOfFiniteType N.X.hom := by rw [← Over.w n.hom.hom]; infer_instance
  obtain ⟨P, j, hjo, hjc, hP, hjr⟩ := exists_clopen_neutralSubgroup N
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : IsAffine N.X.left := isAffine_of_isAffineHom n.hom.hom.left
  have : IsAffine P.X.left := isAffine_of_isAffineHom j.hom.hom.left
  have hLe : range (j ≫ n) ≤ range i := by
    rw [he]
    apply range_le_torusCentralizer_of_connected_normalizer_splitTorus t hT (range i)
    · rw [he]
      exact range_le_torusCentralizer t
    · exact he.le
    · exact (range_le_postcomp j n).trans hN
  let r := rangeFactor (j ≫ n) i hLe
  have hr : r ≫ a = j := by
    apply Grp.hom_ext
    apply (cancel_mono n.hom.hom).mp
    rw [← Grp.comp_hom_hom, Category.assoc, ha, rangeFactor_comp, Grp.comp_hom_hom]
  have : ConnectedSpace H.X.left := GeometricallyConnected.connectedSpace_of_subsingleton H.X.hom
  have hA : Set.range a.hom.hom.left ⊆ Set.range j.hom.hom.left := by
    rw [hjr]
    exact IdentityComponent.range_subset_identitySet N a.hom.hom η[H.X] (IsMonHom.one_hom _)
  let s := IdentityComponent.liftHom j a hA
  have hs : s ≫ j = a := IdentityComponent.liftHom_fac j a hA
  have hmono : Mono a.hom.hom.left := by
    apply mono_of_mono_fac (congrArg (fun f => f.hom.hom.left) ha)
  have : Mono a.hom.hom := Over.mono_of_mono_left _
  let e : H ≅ P :=
    { hom := s
      inv := r
      hom_inv_id := by
        apply Grp.hom_ext
        apply (cancel_mono a.hom.hom).mp
        rw [← Grp.comp_hom_hom, Category.assoc, hr, hs, Grp.id_hom_hom, Category.id_comp]
      inv_hom_id := by
        apply Grp.hom_ext
        apply (cancel_mono j.hom.hom).mp
        rw [← Grp.comp_hom_hom, Category.assoc, hs, hr, Grp.id_hom_hom, Category.id_comp] }
  have : IsIso e.hom := e.isIso_hom
  have : IsIso s.hom.hom.left := (Grp.forget (Over S) ⋙ Over.forget S).map_isIso e.hom
  rw [← hs]
  change IsOpenImmersion (s.hom.hom.left ≫ j.hom.hom.left)
  infer_instance

set_option maxHeartbeats 1200000 in
/-- The geometrically connected centralizer over a field is open in any
closed normalizing group through which it factors. -/
theorem centralizer_open_in_normalizing_group {G H N : GroupScheme S}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [GeometricallyConnected H.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : IsTorus T.toGrp)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (he : range i = torusCentralizer t)
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : range n ≤ (range i).normalizer)
    (a : H ⟶ N) (ha : a ≫ n = i) : IsOpenImmersion a.hom.hom.left := by
  obtain ⟨K, _, _, _, _, hTK⟩ := torusFiniteGaloisSplitting k T.toGrp hT
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Q := baseChange b
  let G' := Q.obj G
  let H' := Q.obj H
  let T' := (CommGroupScheme.baseChange b).obj T
  let t' : T'.toGrp ⟶ G' := Q.map t
  have : IsAffineHom G'.X.hom := MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  have : LocallyOfFiniteType G'.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  have : GeometricallyConnected H'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ inferInstance
  have he' : range (Q.map i) = torusCentralizer t' := by
    rw [range_baseChangeHom, he, torusCentralizer_baseChange]
  have hN' : range (Q.map n) ≤ (range (Q.map i)).normalizer := by
    rw [range_baseChangeHom, range_baseChangeHom, ← normalizer_baseChange]
    exact baseChange_mono b hN
  have ha' : Q.map a ≫ Q.map n = Q.map i := by rw [← Functor.map_comp, ha]
  have hOpen := centralizer_open_in_normalizer_of_isSplitTorus t' hTK (Q.map i) (hi.baseChange b)
    he' (Q.map n) (hn.baseChange b) hN' (Q.map a) ha'
  obtain ⟨hbS, hbF, hbQ⟩ := fieldExtension_fpqc k K
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (baseChange_map_isPullback b a) ?_ hOpen
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end Field

/-- A geometrically connected closed torus centralizer in an affine group
is open in its represented closed normalizer over a field. -/
def TorusCentralizerOpenNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H N : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [GeometricallyConnected H.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G), IsTorus T.toGrp →
    ∀ (i : H ⟶ G), IsClosedSubgroup i → range i = torusCentralizer t →
    ∀ (n : N ⟶ G), IsClosedSubgroup n → (range i).normalizer.IsRepresentedBy n →
      ∃ a : H ⟶ N, a ≫ n = i ∧ IsOpenImmersion a.hom.hom.left

theorem torusCentralizerOpenNormalizer : TorusCentralizerOpenNormalizerStatement.{u} := by
  intro k _ G H N _ _ _ T t hT i hi he n hn hN
  let a := hN.factorHom i (le_normalizer (range i))
  have ha : a ≫ n = i := hN.factorHom_comp _ _
  exact ⟨a, ha, centralizer_open_in_normalizing_group t hT i hi he n hn hN.2.le a ha⟩

end Langlands.GroupScheme.TorusSubgroupModuli
