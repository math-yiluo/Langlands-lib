/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap

/-! # The constant ring underlying finite discrete continuous coefficients

Source: Bhatt--Scholze, Section 5.3. A continuous function into a finite discrete ring
is constant on the members of the finite clopen covering by its fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonObj
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace Profinite

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

/-- The constant-function map from the constant ring presheaf to continuous sections. -/
noncomputable def constantToContinuousRing :
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B)) ⟶
      continuousMapRingPresheaf.{u} B where
  app S := RingCat.ofHom
    { toFun b := ULift.up (ContinuousMap.const S.unop b.down)
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

private noncomputable abbrev constantToContinuousAb :=
  Functor.whiskerRight (constantToContinuousRing.{u} B) (forget₂ RingCat.{u + 1} Ab.{u + 1})

private instance locallySurjective_constantToContinuousAb :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (constantToContinuousAb B) where
  imageSieve_mem {S} s := by
    let f : C(S, B) := s.down
    have hclosed (b : B) : IsClosed {x : S | f x = b} :=
      isClosed_singleton.preimage f.continuous
    let (b : B) : CompactSpace {x : S // f x = b} :=
      isCompact_iff_compactSpace.mp (hclosed b).isCompact
    let U (b : B) : Profinite.{u} := Profinite.of {x : S // f x = b}
    let incl (b : B) : U b ⟶ S := CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ ⟨f x, ⟨x, rfl⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨B, inferInstance, U, incl, hι, ?_⟩
    intro b
    refine ⟨ULift.up b, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private instance locallyInjective_constantToContinuousAb :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (constantToContinuousAb B) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (congrArg ULift.up (congrArg
        (fun t : ULift.{u + 1} C(S.unop, B) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

/-- Continuous finite discrete coefficients are the sheafified constant ring, as ring
objects in condensed abelian groups.

Source: Bhatt--Scholze, Section 5.3
(auxiliary; not a blueprint node).

Proof. The constant-function map is locally surjective on the finite covering of each
profinite set by the clopen fibres of a section. It is locally injective: distinct
constants can agree only on an empty profinite set, covered by the empty family.
Sheafification therefore inverts it. It is a map of ring presheaves, so its
sheafification, followed by the sheafification counit, is a morphism of ring objects.
The empty profinite set and the zero ring are included in the same argument. -/
theorem finiteDiscreteCondensedRing_constant :
    ∃ e : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
      continuousMapRingObj.{u} B, IsMonHom e.hom := by
  let J : GrothendieckTopology Profinite.{u} := coherentTopology Profinite.{u}
  let φ := constantToContinuousAb.{u} B
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have hmap : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  let e := asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso.{u + 1, u, u + 1} J (continuousMapRingSheaf.{u} B)
  refine ⟨e, ?_⟩
  dsimp only [e, Iso.trans_hom, asIso_hom]
  infer_instance

end Profinite
