/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # The filtered system of stage Hom sets
Source: Stacks Project, Tags 09RE and 0D5S.
(blueprint: lem-pc-perfect-hom-stage-colimit).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem homMap_identity
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {Y S : Scheme.{u}} (s : Y ⟶ S) (T : Over S) {P Q : schemeDerivedCategory Y}
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s (𝟙 T) f = f := by
  let e := Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  have : (derivedPullback (𝟙 (pullback s T.hom))).Faithful :=
    Functor.Faithful.of_iso (e (pullback s T.hom)).symm
  have hi : Function.Injective (fun a :
      (derivedPullback (pullback.fst s T.hom)).obj P ⟶
        (derivedPullback (pullback.fst s T.hom)).obj Q ↦ perfectHomMap s (𝟙 T) a) := by
    intro a b h
    have hh := (perfectHomMap_eq_iff s (𝟙 T) a b).1 h
    rw [baseChangeMap_id] at hh
    exact (derivedPullback (𝟙 (pullback s T.hom))).map_injective hh
  apply hi
  simpa only [Category.id_comp] using perfectHomMap_trans s (𝟙 T) (𝟙 T) f

/-- The stage Hom sets and canonical transport form a functor with a set colimit.
No geometric finiteness, perfectness, or local continuity is needed.

Source: Stacks Project, Tag 09RE, filtered Hom system; Tag 0D5S, composition coherence.
(blueprint: lem-pc-perfect-hom-stage-colimit).

Proof: At j take the Hom set between the pullbacks of P and Q, using ULift if
needed to put it in Type (max u w). Transport along j ≤ k is perfectStageMap.
For identity arrows, perfectHomMap_trans makes the transport idempotent.
It is injective: base change of an identity is an identity, its derived pullback
is naturally isomorphic to the identity by exists_derivedPullbackComposition,
and conjugation by the composition comparisons preserves injectivity. An
injective idempotent map is the identity. For two consecutive
arrows, perfectHomMap_trans and the pullback identity baseChangeMap_comp give
the composition law; the equal proofs of inequalities are identified by proof
irrelevance. These laws define H, with the evident ident equivalences. Take its
set colimit and canonical colimit cocone, which exist for this small diagram.
The transition equation follows from the definition of H.map. This also covers
an empty Hom set; no element or arbitrarily chosen geometric object is required. -/
theorem perfect_hom_stage_colimit
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (i : I)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y) :
    ∃ (H : Set.Ici i ⥤ Type (max u w)) (d : Cocone H),
      Nonempty (IsColimit d) ∧
      ∃ (ident : ∀ j : Set.Ici i, H.obj j ≃
          ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q)),
        (∀ (j k : Set.Ici i) (hjk : j ≤ k) (f : H.obj j),
          ident k (H.map (homOfLE hjk) f) =
            perfectStageMap R s j.property hjk (ident j f)) := by
  classical
  let F (j : Set.Ici i) :=
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q
  let H : Set.Ici i ⥤ Type (max u w) :=
    { obj := fun j ↦ ULift.{u} (F j)
      map := fun {j k} h ↦ TypeCat.ofHom
        (fun f ↦ ⟨perfectStageMap R s j.property (leOfHom h) f.down⟩)
      map_id := by
        intro j
        ext f
        change perfectStageMap R s j.property le_rfl f.down = f.down
        unfold perfectStageMap
        have he : (Over.homMk (Spec.map (R.map (homOfLE (le_refl j.val))))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl) :
            Over.mk (Spec.map (R.map (homOfLE j.property))) ⟶
              Over.mk (Spec.map (R.map (homOfLE j.property)))) = 𝟙 _ := by
          ext
          change Spec.map (R.map (𝟙 j.val)) = 𝟙 _
          rw [R.map_id, Spec.map_id]
        rw [he]
        exact homMap_identity s (Over.mk (Spec.map (R.map (homOfLE j.property))))
          (P := P) (Q := Q) f.down
      map_comp := by
        intro j k l h g
        ext f
        change perfectStageMap R s j.property _ f.down =
          perfectStageMap R s k.property _ (perfectStageMap R s j.property _ f.down)
        unfold perfectStageMap
        rw [perfectHomMap_trans]
        congr 1
        ext
        change Spec.map (R.map (homOfLE _)) =
          Spec.map (R.map (homOfLE _)) ≫ Spec.map (R.map (homOfLE _))
        rw [← Spec.map_comp, ← R.map_comp]
        rfl }
  exact ⟨H, colimit.cocone H, ⟨colimit.isColimit H⟩, fun j ↦ Equiv.ulift,
    fun j k hjk f ↦ rfl⟩

end AlgebraicGeometry
