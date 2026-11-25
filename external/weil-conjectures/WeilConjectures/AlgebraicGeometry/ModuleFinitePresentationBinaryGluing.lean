/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent

import WeilConjectures.AlgebraicGeometry.ModuleSubmoduleBinaryGluingProperties
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Gluing a finite presentation and its map across two opens

Source: Stacks Project, Properties, Lemma 01PI, gluing paragraph.
(blueprint: lem-weil-pbc-module-finite-presentation-binary-gluing).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Limits SheafOfModules

-- Keep the iterated-slice transport separate from the cover argument, and keep its
-- ring sheaf abstract so elaboration does not repeatedly unfold moduleRings.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_over_of_overMap
    (X : Scheme.{u}) (R : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u})
    {U A : X.Opens} (G : SheafOfModules.{u} (R.over U)) (hA : A ≤ U)
    (hf : ((overMap R (homOfLE hA)).obj G).IsFinitePresentation) :
    (G.over (Over.mk (homOfLE hA : A ⟶ U))).IsFinitePresentation := by
  let J := _root_.Opens.grothendieckTopology X
  have := hf
  let E := Over.iteratedSliceEquiv (Over.mk (homOfLE hA : A ⟶ U))
  have : E.inverse.IsDenseSubsite (J.over A)
      ((J.over U).over (Over.mk (homOfLE hA : A ⟶ U))) := by
    refine { functorPushforward_mem_iff := ?_ }
    intro T S
    simp only [E, GrothendieckTopology.mem_over_iff, Sieve.overEquiv,
      RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    dsimp [Over.iteratedSliceEquiv]
    rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
    rfl
  have : E.functor.IsContinuous
      ((J.over U).over (Over.mk (homOfLE hA : A ⟶ U))) (J.over A) := by
    infer_instance
  have : E.functor.IsCocontinuous
      ((J.over U).over (Over.mk (homOfLE hA : A ⟶ U))) (J.over A) := by
    infer_instance
  have (T : Over (Over.mk (homOfLE hA : A ⟶ U))) :
      (Over.post (X := T) E.functor).IsContinuous
        (((J.over U).over (Over.mk (homOfLE hA : A ⟶ U))).over T)
        ((J.over A).over (E.functor.obj T)) := by
    apply Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _) _
    exact (Functor.IsDenseSubsite.coverPreserving
      ((J.over U).over (Over.mk (homOfLE hA : A ⟶ U)))
      (J.over A) E.functor).overPost T
  let S := (R.over U).over (Over.mk (homOfLE hA : A ⟶ U))
  let φ : S ⟶ (E.functor.sheafPushforwardContinuous RingCat
      ((J.over U).over (Over.mk (homOfLE hA : A ⟶ U))) (J.over A)).obj
        (R.over A) := 𝟙 _
  let e : (SheafOfModules.pushforward φ).obj ((overMap R (homOfLE hA)).obj G) ≅
      G.over (Over.mk (homOfLE hA : A ⟶ U)) :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))
  have hfp := isFinitePresentation_pushforward_of_isLeftAdjoint E.functor φ
    (Iso.refl _) (M := (overMap R (homOfLE hA)).obj G)
  exact (isFinitePresentation S).prop_of_iso e hfp

-- Transport across the iterated slice identifies restriction by overMap with over.
-- Apply the existing finite-presentation locality theorem to the two-open cover.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_binary_local
    (X : Scheme.{u}) (W V : X.Opens)
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V)))
    (hW : ((overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).obj G).IsFinitePresentation)
    (hV : ((overMap (moduleRings X.toRingedSpace)
      (homOfLE (show V ≤ W ⊔ V from le_sup_right))).obj G).IsFinitePresentation) :
    G.IsFinitePresentation := by
  let R := moduleRings X.toRingedSpace
  let J := _root_.Opens.grothendieckTopology X
  let U : ULift.{u} Bool → Over (W ⊔ V) := fun b ↦
    if b.down then Over.mk (homOfLE (le_sup_left : W ≤ W ⊔ V))
    else Over.mk (homOfLE (le_sup_right : V ≤ W ⊔ V))
  have hc : (J.over (W ⊔ V)).CoversTop U := by
    intro T
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    have hxu : x ∈ W ⊔ V := T.hom.le hx
    rcases hxu with hxW | hxV
    · let A : Over (W ⊔ V) := Over.mk
        (homOfLE (inf_le_left.trans T.hom.le : T.left ⊓ W ≤ W ⊔ V))
      refine ⟨T.left ⊓ W, homOfLE inf_le_left, ?_, ⟨hx, hxW⟩⟩
      rw [Sieve.overEquiv_iff]
      change Sieve.ofObjects U T (Over.homMk (homOfLE inf_le_left) : A ⟶ T)
      exact ⟨⟨true⟩, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩
    · let A : Over (W ⊔ V) := Over.mk
        (homOfLE (inf_le_left.trans T.hom.le : T.left ⊓ V ≤ W ⊔ V))
      refine ⟨T.left ⊓ V, homOfLE inf_le_left, ?_, ⟨hx, hxV⟩⟩
      rw [Sieve.overEquiv_iff]
      change Sieve.ofObjects U T (Over.homMk (homOfLE inf_le_left) : A ⟶ T)
      exact ⟨⟨false⟩, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩
  have (b : ULift.{u} Bool) : (G.over (U b)).IsFinitePresentation := by
    rcases b with ⟨b⟩
    cases b
    · exact finitePresentation_over_of_overMap X R G le_sup_right hV
    · exact finitePresentation_over_of_overMap X R G le_sup_left hW
  exact IsFinitePresentation.of_coversTop G U hc

/-- Glue the old module on W to a finitely presented replacement on V using the
replacement map as the overlap identification. This constructs only a module on
W union V, with a map to the restriction of H.

Source: Stacks Project, Properties, Lemma 01PI, second paragraph of the proof
(https://stacks.math.columbia.edu/tag/01PI), and sheaf-module descent, Tag 00AK.
(blueprint: lem-weil-pbc-module-finite-presentation-binary-gluing).

Proof: Restrict the map j to W intersect V. It is an isomorphism by hypothesis.
Identify its target with the restriction of H on W by the canonical iterated
restriction isomorphisms. Glue H on W and E on V using this identification.
For the two-open cover, all cocycle equations reduce to the inverse identities
for the overlap isomorphism and identity maps. Sheaf-module descent produces G
on W union V with the prescribed local identifications. The identity map to H
on W and j on V agree on the overlap by the choice of identification, so glue
to a map phi. Finite presentation is local and invariant under isomorphism;
thus G is finitely presented. The restriction of phi to W is the prescribed
identification with H on W and therefore is an isomorphism. Empty opens and
identical opens cause no exception: the same two-open descent applies. This
step does not construct any affine replacement and needs no compactness,
quasi-separatedness, affineness, or quasi-coherence hypotheses. -/
theorem exists_finitePresentation_binary_gluing
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over W).IsFinitePresentation]
    (E : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    [E.IsFinitePresentation] (j : E ⟶ H.over V)
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map j)] :
    ∃ G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V)),
      G.IsFinitePresentation ∧ ∃ (φ : G ⟶ H.over (W ⊔ V)),
        IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map φ) := by
  let R := moduleRings X.toRingedSpace
  let G := binarySubmodule X W V H E j
  let φ := binarySubmoduleInclusion X W V H E j
  obtain ⟨hW, ⟨eV⟩⟩ := binarySubmodule_restrictions X W V H E j
  have := hW
  let eW : (overMap R (homOfLE (le_sup_left : W ≤ W ⊔ V))).obj G ≅ H.over W :=
    asIso ((overMap R (homOfLE (le_sup_left : W ≤ W ⊔ V))).map φ) ≪≫
      (overFunctorMap R (homOfLE (le_sup_left : W ≤ W ⊔ V))).app H
  have hWfp : ((overMap R (homOfLE (le_sup_left : W ≤ W ⊔ V))).obj G).IsFinitePresentation :=
    (isFinitePresentation (R.over W)).prop_of_iso eW.symm inferInstance
  have hVfp : ((overMap R (homOfLE (le_sup_right : V ≤ W ⊔ V))).obj G).IsFinitePresentation :=
    (isFinitePresentation (R.over V)).prop_of_iso eV.symm inferInstance
  exact ⟨G, finitePresentation_binary_local X W V G hWfp hVfp, φ, hW⟩

end AlgebraicGeometry.Scheme.Modules
