/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompletionCoefficientTransportCore
import WeilConjectures.AlgebraicGeometry.Constant.ConstantPrincipalCompleteOrthogonality
import Mathlib.RingTheory.Noetherian.Basic

/-! # Scalar restriction on the full category of complete objects

Source: Stacks Tags 099I and 099L, and the diagonal trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem extension_eq_of_span
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (K : RingedSiteIdeal R) (L : RingedSiteIdeal B)
    (h : ∀ U, L.sections U =
      Ideal.span (Set.range (fun a : K.sections U ↦ φ.hom.app (op U) a))) :
    K.extension φ = L := by
  apply ((K.existsUnique_extension φ).unique ?_ ?_)
  · exact (K.existsUnique_extension φ).exists.choose_spec
  · intro U b
    constructor
    · intro hb
      refine ⟨⊤, J.top_mem _, ?_⟩
      intro V g _
      rw [← h V]
      exact L.restriction g b hb
    · rintro ⟨S, hS, hb⟩
      exact L.local_mem U b S hS (fun V g hg ↦ by rw [h V]; exact hb V g hg)

private theorem coefficientKernel_extension
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    (ConstantCompletion.kernelIdeal (ConstantCompletion.quotient J A I 0)).extension
        (ConstantCompletion.coefficientMap J A I) =
      ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0) := by
  let φ := ConstantCompletion.coefficientMap J A I
  let K := ConstantCompletion.kernelIdeal (ConstantCompletion.quotient J A I 0)
  let L := ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)
  apply extension_eq_of_span φ K L
  intro U
  have hK : K.sections U = RingHom.ker ((ConstantCompletion.quotient J A I 0).hom.app (op U)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique
      (ConstantCompletion.quotient J A I 0)).exists.choose_spec U
  have hL : L.sections U =
      RingHom.ker ((ConstantCompletion.projection J A I 0).hom.app (op U)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique
      (ConstantCompletion.projection J A I 0)).exists.choose_spec U
  rw [hL, ((ConstantCompletion.flat_and_quotients J A I).2.1 0 U).2]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Ideal.subset_span
    refine ⟨⟨(ConstantCompletion.constantSection (J := J) a.val).val (op U), ?_⟩, rfl⟩
    rw [hK, ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U).2]
    exact Ideal.subset_span ⟨a, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha : a.val ∈ Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (ConstantCompletion.constantSection (J := J) (b : A)).val (op U))) := by
      rw [← ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U).2, ← hK]
      exact a.property
    change φ.hom.app (op U) a.val ∈ _
    have hle : Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (ConstantCompletion.constantSection (J := J) (b : A)).val (op U))) ≤
        Ideal.comap (φ.hom.app (op U)).hom
          (Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
            (ConstantCompletion.algebraSection φ b).val (op U)))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Ideal.subset_span ⟨b, rfl⟩
    exact hle ha

attribute [local irreducible] ConstantCompletion.completed ConstantCompletion.kernelIdeal
  diagonalCompletedRestriction

universe a b va vb

private theorem orthogonal_equivalence_iff
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Preadditive A] [Preadditive B] (E : A ≌ B)
    [E.functor.Additive] [E.inverse.Additive] (n : ℕ) (N : A) :
    (∀ P : A, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ N)) ↔
      (∀ P : B, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ E.functor.obj N)) := by
  constructor
  · intro h P hp
    have : IsIso (n • 𝟙 (E.inverse.obj P)) := by
      have : IsIso (n • 𝟙 P) := hp
      have := Functor.map_isIso E.inverse (n • 𝟙 P)
      simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using this
    have hs := h (E.inverse.obj P) inferInstance
    refine ⟨fun f g ↦ ?_⟩
    apply (cancel_epi (E.counitIso.app P).hom).1
    exact E.fullyFaithfulFunctor.map_preimage
      ((E.counitIso.app P).hom ≫ f) |>.symm.trans
        ((congrArg E.functor.map (hs.elim
          (E.fullyFaithfulFunctor.preimage ((E.counitIso.app P).hom ≫ f))
          (E.fullyFaithfulFunctor.preimage ((E.counitIso.app P).hom ≫ g)))).trans
            (E.fullyFaithfulFunctor.map_preimage _))
  · intro h P hp
    have : IsIso (n • 𝟙 (E.functor.obj P)) := by
      have : IsIso (n • 𝟙 P) := hp
      have := Functor.map_isIso E.functor (n • 𝟙 P)
      simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using this
    exact ⟨fun f g ↦ E.functor.map_injective ((h _ inferInstance).elim _ _)⟩

private theorem constantComplete_restriction_iff
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ConstantCompletion.D (ConstantCompletion.completed J A I)) :
    ConstantCompletion.IsComplete (ConstantCompletion.quotient J A I 0)
        ((ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)).obj M) ↔
      ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0) M := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.constant J A))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.completed J A I))
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod
    ((ConstantCompletion.constant J A).over U))
  let (U : C) := HasDerivedCategory.standard (ConstantCompletion.Mod
    ((ConstantCompletion.completed J A I).over U))
  have h := siteDerivedRestrictScalars_locallyDerivedComplete_iff
    (ConstantCompletion.coefficientMap J A I)
    (ConstantCompletion.kernelIdeal (ConstantCompletion.quotient J A I 0)) M
  rw [coefficientKernel_extension J A I] at h
  exact h

/-- Restriction from the completed coefficient sheaf to constant coefficients is
fully faithful on objects with derived-complete underlying constant coefficients.
The completeness condition is right orthogonality to all l-invertible complexes.

Source: Stacks Tags 099I, 099L and 091Q; blueprint latest,
`sk-prop-diagonal-tower-trace.proof.md`, paragraph (1).
(blueprint: lem-sfb-diagonal-complete-scalar-restriction-core).

Proof: use the exact equivalence between module sheaves over the constant ring
sheaf and sheaves of modules over its coefficient ring. Replace the pro-etale site
by its equivalent small site and transport the actual constant-to-completed map.
The finite projections identify the transported completion with the limit of the
constant Z_l/l^(n+1) sheaves: Z_l/l^(n+1) is canonically Z/l^(n+1), compatibly with
all quotient transitions. Apply ConstantCompletion.equivalence to the Noetherian
ring ULift Z_l and its principal ideal (l). The flat restriction criterion reflects
local derived completeness. For a principal ideal, the local condition agrees
with right orthogonality to l-invertible objects (Stacks 091Q, 0999); exact
coefficient and site equivalences preserve this condition. Consequently the
preimage of the complete constant objects is precisely the complete completed
objects. The equivalence of full complete categories and their full inclusions
then give fullness and faithfulness for the indicated composite. These transports
retain the actual scalar restriction on morphisms, rather than merely giving an
abstract equivalence of the two complete categories. No scheme smoothness,
Noetherian hypothesis on the scheme, or invertibility of l on it is needed. -/
theorem diagonalCompleteScalarRestrictionCore (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod l S)]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l S)] :
    let F := diagonalCompletedUnderlying l S
    let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
      ∀ V : DerivedCategory (DiagonalMod l S),
        IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
    Nonempty (P.ι ⋙ F).FullyFaithful := by
  classical
  dsimp only
  let J := Scheme.proEtaleModelTopology S
  let A := ULift.{u + 1} ℤ_[l]
  let I : Ideal A := Ideal.span {(l : A)}
  let F := diagonalCompletedUnderlying l S
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l S),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  have : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv ℤ_[l] ULift.ringEquiv.symm
  have hl : (l : A) ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff]
    have hlp : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have hleft : ∀ x : A, (l : A) * x = 0 → x = 0 := by
      intro x hx
      apply ULift.ext
      exact (mul_eq_zero.mp (congrArg ULift.down hx)).resolve_left hlp
    exact ⟨hleft, fun x hx ↦ hleft x ((mul_comm _ _).trans hx)⟩
  obtain ⟨EB, ER, hER, hERi, ⟨α⟩⟩ := diagonalCompletionCoefficientTransportCore l S
  let := hER
  let := hERi
  let PB : ObjectProperty (ConstantCompletion.D (ConstantCompletion.completed J A I)) :=
    ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0)
  let PR : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant J A)) :=
    ConstantCompletion.IsComplete (ConstantCompletion.quotient J A I 0)
  have hP (M : P.FullSubcategory) : PB (EB.functor.obj M.obj) := by
    apply (constantComplete_restriction_iff J A I _).mp
    apply ConstantCompletion.constantPrincipalComplete_of_orthogonal J A l hl _
    have h := (orthogonal_equivalence_iff ER l (F.obj M.obj)).mp M.property
    intro V hV
    exact ⟨fun f g ↦ (cancel_mono (α.app M.obj).inv).mp
      ((h V hV).elim (f ≫ (α.app M.obj).inv) (g ≫ (α.app M.obj).inv))⟩
  let G : P.FullSubcategory ⥤ PB.FullSubcategory :=
    PB.lift (P.ι ⋙ EB.functor) hP
  have hG : G.FullyFaithful :=
    (P.fullyFaithfulι.comp EB.fullyFaithfulFunctor).ofCompFaithful (G := PB.ι)
  obtain ⟨e, ⟨β⟩⟩ := ConstantCompletion.equivalence J A I
  have hH : (G ⋙ e.functor ⋙ PR.ι).FullyFaithful :=
    hG.comp (e.fullyFaithfulFunctor.comp PR.fullyFaithfulι)
  let γ : G ⋙ e.functor ⋙ PR.ι ≅ (P.ι ⋙ F) ⋙ ER.functor :=
    Functor.isoWhiskerLeft G β ≪≫ Functor.isoWhiskerLeft P.ι α.symm
  exact ⟨(hH.ofIso γ).ofCompFaithful⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
