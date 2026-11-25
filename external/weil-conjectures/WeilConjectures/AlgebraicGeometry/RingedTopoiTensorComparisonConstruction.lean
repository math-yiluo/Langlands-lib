/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiScalarTensorComparison
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Existence of the normalized ringed-topos tensor comparison -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

-- Elaborating the composite comparison checks several transported module structures.
/-- The normalized ordinary tensor comparison exists.
Source: Stacks Project, Modules on Sites, Tag 03EL, together with the inverse-image
adjunction for a morphism of topoi and extension of scalars
(auxiliary; not a blueprint node).

Proof: First apply the inverse-image adjunction to the universal property of module
bilinear maps. Finite-product preservation transports addition and scalar multiplication;
the compatibility axioms of I identify these transported operations with those on
I.modules. Thus inverse image takes the universal R-balanced pairing to the universal
RI-balanced pairing. Its representing isomorphism sends the inverse image of m tensor n
to the tensor of the inverse images of m and n, naturally in both modules.
Next extend scalars. The balanced maps
s tensor (m tensor n) mapped to (s tensor m) tensor (1 tensor n), and
(s tensor m) tensor (t tensor n) mapped to st tensor (m tensor n), are inverse.
They commute with restrictions and so descend through module sheafification; checking
on pure tensors proves inverse identities and naturality. Compose these two comparisons
and transport along hobj. The map q is the sheafification insertion m mapped to 1 tensor m,
followed by eqToHom (hobj M).symm. The displayed scalar-extension formulas give q_one.
The same formulas, applied to a generalized pair of sections over any sheaf Z, give pure.
Naturality of both representing isomorphisms and hmap gives naturality. This supplies
all five fields of CanonicalRingedTensorComparison. -/
theorem canonicalRingedTensorComparison_nonempty
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := by
  classical
  let := monoidalCategory R
  let := monoidalCategory RI
  let := monoidalCategory S
  obtain ⟨eI, hnI, hpI⟩ := RingedTensor.exists_inverseImageTensorComparison R RI uInv I
    uPush adj
  obtain ⟨eS, hnS, hpS⟩ := RingedTensor.exists_scalarTensorComparison c
  let T := RingedTensor.tensorFunctor c
  let ε : L ≅ I.modules ⋙ T := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M)) (by
      intro M N f
      change L.map f ≫ eqToHom (hobj N) =
        eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f)
      rw [hmap]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  let ei : tensor _ ⋙ I.modules ≅ I.modules.prod I.modules ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ eI MN.1 MN.2) (fun f ↦ hnI f.1 f.2)
  let es : tensor _ ⋙ T ≅ T.prod T ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ eS MN.1 MN.2) (fun f ↦ hnS f.1 f.2)
  let μ : tensor _ ⋙ L ≅ L.prod L ⋙ tensor _ :=
    Functor.isoWhiskerLeft (tensor _) ε ≪≫
      Functor.isoWhiskerRight ei T ≪≫
      Functor.isoWhiskerLeft (I.modules.prod I.modules) es ≪≫
      (Functor.isoWhiskerRight (NatIso.prod ε ε) (tensor _)).symm
  let q M := RingedTensor.tensorUnit c (I.modules.obj M) ≫
    (RingedTensor.underlying S).map (ε.inv.app M)
  refine ⟨{ q := q
            q_one := ?_
            mu := fun M N ↦ μ.app (M, N)
            naturality := by
              intro M M' N N' f g
              exact μ.hom.naturality (show (M, N) ⟶ (M', N') from (f, g))
            pure := ?_ }⟩
  · intro M W m
    change (ε.inv.app M).val.app W
      ((RingedTensor.tensorUnit c (I.modules.obj M)).hom.app W m) = _
    erw [tensorUnit_apply]
    rfl
  · intro M N Z x y z hz W t
    let a := ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
    let b := ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)
    let d := ((uInv.map z ≫ I.moduleUnderlying.inv.app (M ⊗ N)).hom.app W t)
    have hi : (eI M N).hom.val.app W d = RingedTensor.pure RI _ _ W a b :=
      hpI M N Z x y z hz W t
    have hu : (T.map (eI M N).hom).val.app W
        ((RingedTensor.tensorUnit c (I.modules.obj (M ⊗ N))).hom.app W d) =
        (RingedTensor.tensorUnit c (I.modules.obj M ⊗ I.modules.obj N)).hom.app W
          ((eI M N).hom.val.app W d) :=
      (congrArg (fun f ↦ f.val.app W d)
        ((SheafOfModules.tensorAdjunction c).unit.naturality (eI M N).hom)).symm
    have he (P : SheafOfModules.{u} (RingedTensor.ringSheaf R))
        (v : (T.obj (I.modules.obj P)).val.obj W) :
        (ε.hom.app P).val.app W ((ε.inv.app P).val.app W v) = v := by
      exact congrArg (fun f : T.obj (I.modules.obj P) ⟶ T.obj (I.modules.obj P) ↦
        f.val.app W v) (ε.inv_hom_id_app P)
    change (((T.map (eI M N).hom ≫ (eS (I.modules.obj M) (I.modules.obj N)).hom) ≫
      (ε.inv.app M ⊗ₘ ε.inv.app N)).val.app W)
      ((ε.hom.app (M ⊗ N)).val.app W
        ((ε.inv.app (M ⊗ N)).val.app W
          ((RingedTensor.tensorUnit c (I.modules.obj (M ⊗ N))).hom.app W d))) =
      RingedTensor.pure S _ _ W
        ((ε.inv.app M).val.app W ((RingedTensor.tensorUnit c (I.modules.obj M)).hom.app W a))
        ((ε.inv.app N).val.app W ((RingedTensor.tensorUnit c (I.modules.obj N)).hom.app W b))
    rw [he]
    change (ε.inv.app M ⊗ₘ ε.inv.app N).val.app W
      ((eS (I.modules.obj M) (I.modules.obj N)).hom.val.app W
        ((T.map (eI M N).hom).val.app W
          ((RingedTensor.tensorUnit c (I.modules.obj (M ⊗ N))).hom.app W d))) = _
    rw [hu, hi]
    exact (congrArg ((ε.inv.app M ⊗ₘ ε.inv.app N).val.app W)
      (hpS (I.modules.obj M) (I.modules.obj N) W a b)).trans
        (RingedTensor.pure_map S (ε.inv.app M) (ε.inv.app N) W _ _)

end SheafOfModules
