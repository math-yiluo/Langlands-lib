/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulQuotientComparison
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector

/-!
# Constant coefficient completion: KoszulReflector

The Koszul reflector identification `koszul_quotient_reflector`.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation

private theorem kernel_generating_list
    {R S : Sheaf J CommRingCat.{u}} (q : R ⟶ S) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (hker : ∀ U : C, RingHom.ker (q.hom.app (op U)).hom =
      Ideal.span (Set.range (fun i ↦ (a i).val (op U)))) :
    ∀ U : C, IsRingedIdealGeneratingList R (kernelIdeal q).module
      (kernelIdeal q).inclusion U r (fun i ↦ (a i).val (op U)) := by
  intro U
  let K := overIdeal (kernelIdeal q) U
  let bs (i : Fin r) : ((R.over U).obj ⋙ forget CommRingCat).sections :=
    ⟨fun V ↦ (a i).val (op V.unop.left), fun f ↦ (a i).property f.unop.left.op⟩
  have hs (V : Over U) : K.sections V =
      Ideal.span (Set.range (fun i ↦ (bs i).val (op V))) := by
    exact ((kernelIdeal_existsUnique q).exists.choose_spec V.left).trans (hker V.left)
  obtain ⟨σ, e, he⟩ := ideal_generated_global_sections (R.over U) K r bs hs
  exact ⟨σ, e, fun i ↦ congrArg
    (fun s ↦ s.val (op (Over.mk (𝟙 U)))) (he i)⟩

private theorem finite_kernel_span [IsNoetherianRing A] (b : Bool) (r : ℕ)
    (a : Fin r → A) (ha : Ideal.span (Set.range a) = I) (U : C) :
    RingHom.ker ((finiteMap J A I b 0).hom.app (op U)).hom =
      Ideal.span (Set.range (fun i ↦
        (algebraSection (baseMap J A I b) (a i)).val (op U))) := by
  let f : A →+* (coefficients J A I b).obj.obj (op U) :=
    ((baseMap J A I b).hom.app (op U)).hom.comp
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)).hom
  have hs := span_subtype_images f (I ^ (0 + 1)) a
    (by simpa only [Nat.zero_add, pow_one] using ha)
  cases b with
  | false =>
      exact (((flat_and_quotients J A I).2.2 0 U).2).trans hs
  | true =>
      exact (((flat_and_quotients J A I).2.1 0 U).2).trans hs

private theorem complete_of_iso {R S : Sheaf J CommRingCat.{u}} (q : R ⟶ S)
    {M N : D R} (e : M ≅ N) (hM : IsComplete q M) : IsComplete q N := by
  let := HasDerivedCategory.standard (Mod R)
  let (U : C) := HasDerivedCategory.standard (Mod (R.over U))
  intro U f hf
  let H := derivedInternalHom (J.over U) (R.over U)
  exact (hM U f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction R U).mapIso e))).symm

/-- Koszul and finite-quotient completion are canonically identified, preserving the units;
their common functor is the reflector for the local internal-Hom completeness condition.
Source: Stacks 099L, 099M, 0A0E
(auxiliary; not a blueprint node).
Proof: apply the ringed Koszul reflector to the global generators, including the empty
list. For constant coefficients the Noetherian Koszul augmentation has pro-zero cone.
Exact constant sheafification and tensor by a fixed K-flat model preserve this property.
The strict-tower derived-limit theorem inverts the augmentation and identifies its unit
with the quotient unit. For completed coefficients, restrict to constant coefficients:
the finite reductions, strict Koszul tensors and units agree, and restriction identifies
total derived limits by the flat exact adjunction on strict towers. Conservativity
of exact restriction detects the augmentation isomorphism over the completion as well.
Transport the reflector property and the unit-isomorphism criterion across this
unit-preserving natural isomorphism. -/
theorem koszul_quotient_reflector [IsNoetherianRing A] (b : Bool) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I) :
    ∃ K : KoszulPresentation J A I b r a,
      (∃ e : koszulCompletion J A I K ≅ completion J A I b,
        ∀ M : D (coefficients J A I b), koszulUnit J A I K M ≫ e.hom.app M =
          (completionUnit J A I b).app M) ∧
      (∀ M : D (coefficients J A I b),
        IsComplete (finiteMap J A I b 0) ((completion J A I b).obj M)) ∧
      (∀ (M L : D (coefficients J A I b)), IsComplete (finiteMap J A I b 0) L →
        Function.Bijective (fun f : (completion J A I b).obj M ⟶ L ↦
          (completionUnit J A I b).app M ≫ f)) ∧
      (∀ M : D (coefficients J A I b),
        IsIso ((completionUnit J A I b).app M) ↔ IsComplete (finiteMap J A I b 0) M) := by
  classical
  let O := coefficients J A I b
  let q := finiteMap J A I b 0
  let := HasDerivedCategory.standard (Mod O)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod O)
  let (U : C) := HasDerivedCategory.standard (Mod (O.over U))
  have : Mono (kernelIdeal q).inclusion := by
    constructor
    intro Z f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k ↦ k.val.app V z) h
  obtain ⟨K, hc, hb, hi, _⟩ := ringedKoszulCompletionReflector O r
    (fun i ↦ algebraSection (baseMap J A I b) (a i))
    (kernelIdeal q).module (kernelIdeal q).inclusion
    (kernel_generating_list J q r _ (finite_kernel_span J A I b r a ha))
  change ∀ M, IsComplete q ((koszulCompletion J A I K).obj M) at hc
  change ∀ M L, IsComplete q L →
    Function.Bijective (fun f : (koszulCompletion J A I K).obj M ⟶ L ↦
      koszulUnit J A I K M ≫ f) at hb
  change ∀ M, IsIso (koszulUnit J A I K M) ↔ IsComplete q M at hi
  obtain ⟨e, he⟩ := koszulQuotientComparison J A I b r a ha K
  refine ⟨K, ⟨e, he⟩, ?_, ?_, ?_⟩
  · intro M
    exact complete_of_iso J q (e.app M) (hc M)
  · intro M L hL
    constructor
    · intro f g h
      apply (cancel_epi (e.hom.app M)).1
      apply (hb M L hL).1
      change koszulUnit J A I K M ≫ (e.hom.app M ≫ f) =
        koszulUnit J A I K M ≫ (e.hom.app M ≫ g)
      simpa only [← Category.assoc, he M] using h
    · intro f
      obtain ⟨g, hg⟩ := (hb M L hL).2 f
      refine ⟨e.inv.app M ≫ g, ?_⟩
      rw [← he M]
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hg
  · intro M
    rw [← he M]
    exact ⟨fun h ↦ (hi M).1 (by
      have := h
      exact IsIso.of_isIso_comp_right _ (e.hom.app M)), fun h ↦ by
      have := (hi M).2 h
      infer_instance⟩

end CategoryTheory.ConstantCompletion
