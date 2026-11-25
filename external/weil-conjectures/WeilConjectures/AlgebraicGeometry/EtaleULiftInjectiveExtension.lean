/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Ulift

import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Sites.Limits

/-! Extension property for coefficient-lifted étale sheaves. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem small_group_in_image (G : AddCommGrpCat.{u + 1}) [Small.{u} G] :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.essImage G := by
  classical
  let : AddCommGroup (Shrink.{u} G) := (equivShrink G).symm.addCommGroup
  let e : Shrink.{u} G ≃+ G := (equivShrink G).symm.addEquiv
  refine ⟨AddCommGrpCat.of (Shrink.{u} G), ⟨?_⟩⟩
  exact (AddEquiv.ulift.trans e).toAddCommGrpIso

private theorem small_sheaf_in_image (X : Scheme.{u})
    (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hB : ∀ U : X.Etaleᵒᵖ, Small.{u} (B.obj.obj U)) :
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).essImage B := by
  classical
  let F := AddCommGrpCat.uliftFunctor.{u + 1, u}
  have h : ∀ U, F.essImage (B.obj.obj U) := fun U ↦ by
    let := hB U
    exact small_group_in_image (B.obj.obj U)
  let P := Functor.essImage.liftFunctor B.obj F h
  let e := Functor.essImage.liftFunctorCompIso B.obj F h
  have hP : Presheaf.IsSheaf X.smallEtaleTopology P := by
    apply Presheaf.isSheaf_of_isSheaf_comp X.smallEtaleTopology P F
    exact (Presheaf.isSheaf_of_iso_iff e).mpr B.property
  refine ⟨⟨P, hP⟩, ⟨?_⟩⟩
  exact (fullyFaithfulSheafToPresheaf _ _).preimageIso e

/-- Small-valued extension problems descend through coefficient lift.
Source: Stacks Project, Injectives, Lemma 19.7.3, Tag 01DO;
universe descent step of `lem-sc-etale-ulift-injective`.
(blueprint: lem-sc-etale-ulift-injective-extension)

Proof: Since f is mono, each component is an injective homomorphism. Thus A is
objectwise u-small whenever B is. Transport the groups on A and B along their
shrink equivalences, and transport the restrictions by conjugation. This gives
small-valued presheaves A0 and B0 and natural isomorphisms of their coefficient lifts
with A and B. Full faithfulness of ULift reflects the sheaf condition, so A0 and B0
are sheaves. Descend f and g through the fully faithful sheafCompose functor. The
descended f is mono, since a faithful functor reflects monomorphisms. Injectivity
of I extends the descended g across this descended f. Apply coefficient lift and
conjugate with the natural isomorphisms to get h and its factorization identity.
No arbitrary witness is used to define a public object. The empty site and zero
groups are included: shrink and transport work on them in exactly the same way. -/
theorem etale_ulift_injective_extension (X : Scheme.{u})
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hB : ∀ U : X.Etaleᵒᵖ, Small.{u} (B.obj.obj U))
    (f : A ⟶ B) [Mono f]
    (g : A ⟶ (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj I) :
    ∃ h : B ⟶ (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj I, f ≫ h = g := by
  classical
  let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  have hA : ∀ U : X.Etaleᵒᵖ, Small.{u} (A.obj.obj U) := fun U ↦ by
    let := hB U
    have : Mono (f.hom.app U) := by infer_instance
    exact small_of_injective ((AddCommGrpCat.mono_iff_injective (f.hom.app U)).mp inferInstance)
  obtain ⟨A0, ⟨a⟩⟩ := small_sheaf_in_image X A hA
  obtain ⟨B0, ⟨b⟩⟩ := small_sheaf_in_image X B hB
  let f0 : A0 ⟶ B0 := L.preimage (a.hom ≫ f ≫ b.inv)
  let g0 : A0 ⟶ I := L.preimage (a.hom ≫ g)
  have : Mono (L.map f0) := by
    dsimp [f0]
    rw [Functor.map_preimage]
    infer_instance
  have : Mono f0 := by exact Functor.mono_of_mono_map L (inferInstance : Mono (L.map f0))
  obtain ⟨h0, hh0⟩ := Injective.factors g0 f0
  refine ⟨b.inv ≫ L.map h0, ?_⟩
  apply (cancel_epi a.hom).mp
  calc
    a.hom ≫ f ≫ b.inv ≫ L.map h0 = L.map f0 ≫ L.map h0 := by
      simp [f0, Category.assoc]
    _ = L.map g0 := by rw [← L.map_comp, hh0]
    _ = a.hom ≫ g := by simp [g0]

end AlgebraicGeometry.Scheme
