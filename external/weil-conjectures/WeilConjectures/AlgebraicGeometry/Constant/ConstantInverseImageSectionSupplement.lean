/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.ConstantInverseImageSection

/-! # Transporting global coefficient sections

Source: Stacks Project, Sites Tag 00YV and Modules on Sites Tag 03D2
(blueprint: lem-sp-constant-inverse-image-section).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

/-- Transport preserves the vanishing of a global section under a ring map.
Source: Stacks 00YV, 03D2 (blueprint: lem-sp-constant-inverse-image-section).
Proof: naturality of the underlying-ring comparison identifies the image with the
inverse image of the zero-valued composite. The ringZero graph identity makes it zero. -/
theorem inverseImageSection_zero
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)} [PreservesFiniteLimits L]
    (F : InverseImageData L) {R S : Sheaf JC CommRingCat.{u}} (q : R ⟶ S)
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U, q.hom.app U (a.val U) = 0) (U : Eᵒᵖ) :
    (F.rings.map q).hom.app U ((inverseImageSection F R a).val U) = 0 := by
  let T := Sheaf.terminal JC Types.isTerminalPUnit
  let T' := Sheaf.terminal JD Types.isTerminalPUnit
  let h := (Sheaf.isTerminalTerminal JC Types.isTerminalPUnit).isTerminalObj L T
  let x := (h.from T').hom.app U PUnit.unit
  have hz := (F.algebra S).ringZero T
    (sectionMap R a T ≫ (sheafCompose JC (forget CommRingCat)).map q)
    (fun V _ ↦ ha V) U x
  have hn := congrArg (fun f ↦ f.hom.app U ((L.map (sectionMap R a T)).hom.app U x))
    (F.ring_naturality q)
  change (F.algebra S).ringUnderlying.hom.hom.app U
      ((L.map ((sheafCompose JC (forget CommRingCat)).map q)).hom.app U
        ((L.map (sectionMap R a T)).hom.app U x)) =
    (F.rings.map q).hom.app U ((inverseImageSection F R a).val U) at hn
  rw [L.map_comp] at hz
  exact hn.symm.trans hz

/-- Transported ideal elements remain in the kernel of the constant quotient.
Source: Stacks 03D2, 093M (blueprint: lem-sp-constant-inverse-image-section).
Proof: the sheafification unit intertwines the quotient with the constant map
A → A/I. Thus a in I maps to zero. Apply inverseImageSection_zero and naturality
of F.constants for this quotient homomorphism. No rigidity of constants is needed. -/
theorem transportedConstantSection_quotient
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)} [PreservesFiniteLimits L]
    (F : InverseImageData L) (A : Type u) [CommRing A] (I : Ideal A)
    (a : A) (ha : a ∈ I) (U : Eᵒᵖ) :
    (quotient JD A I 0).hom.app U ((transportedConstantSection F A a).val U) = 0 := by
  have hq (V : Cᵒᵖ) : (quotient JC A I 0).hom.app V
      ((constantSection (J := JC) a).val V) = 0 := by
    have hn := congrArg (fun f ↦ (f.app V).hom a)
      (toSheafify_naturality (D := CommRingCat.{u}) JC ((Functor.const Cᵒᵖ).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
    change (toSheafify JC ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (A ⧸ I ^ (0 + 1))))).app V
          (Ideal.Quotient.mk (I ^ (0 + 1)) a) =
      (quotient JC A I 0).hom.app V ((constantSection (J := JC) a).val V) at hn
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using ha), map_zero] at hn
    exact hn.symm
  have hn := F.constants.hom.naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))
  have he := congrArg (fun f ↦ f.hom.app U
      ((inverseImageSection F (constant JC A) (constantSection (J := JC) a)).val U)) hn
  change (constantMap F (A ⧸ I ^ (0 + 1))).hom.app U
      ((F.rings.map (quotient JC A I 0)).hom.app U
        ((inverseImageSection F (constant JC A) (constantSection (J := JC) a)).val U)) =
    (quotient JD A I 0).hom.app U ((transportedConstantSection F A a).val U) at he
  rw [inverseImageSection_zero F _ _ hq, map_zero] at he
  exact he.symm

end CategoryTheory.ConstantCompletion
