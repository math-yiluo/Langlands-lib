/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# The graph map from etale sum extension to compactified sheaf pushforward

Source: Stacks Project, Etale Cohomology, Tag 0F4L, graph extension, and
More on Etale Cohomology, Tag 0GKM.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Extend a sheet along its clopen graph in the compactification, then transpose
under inverse image/direct image for the proper projection.

Source: Stacks Project, Etale Cohomology, Tag 0F4L, graph extension.
(auxiliary; not a blueprint node).

The graph projection is constructed from the unit of inverse image/direct image for
the graph and the inverse of its open-extension-to-direct-image comparison. Thus the
map is specified by actual adjunctions and is not a choice of an unspecified witness. -/
noncomputable def etaleCompactificationGraphMap
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u]
    (c : Compactification u) :
    etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g := by
  let q : pullback c.g u ⟶ U := pullback.snd c.g u
  let v : pullback c.g u ⟶ c.Z := pullback.fst c.g u
  let s : U ⟶ pullback c.g u := pullback.lift c.i (𝟙 U) (by simpa using c.comm.symm)
  have hs₁ : s ≫ v = c.i := pullback.lift_fst _ _ _
  have hs₂ : s ≫ q = 𝟙 U := pullback.lift_snd _ _ _
  have : IsOpenImmersion (s ≫ v) := by rw [hs₁]; infer_instance
  have : IsOpenImmersion s := FormallyUnramified.isOpenImmersion_of_comp v s
  have : IsClosedImmersion (s ≫ q) := by rw [hs₂]; infer_instance
  have : IsClosedImmersion s := .of_comp s q
  have : IsIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) s) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range _ s
      s.isClosedEmbedding.isClosed_range
  let Q := upperStar (ModuleCat.{u + 1} A) q
  let S := openImmersionLowerShriek (ModuleCat.{u + 1} A) s
  let V := etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance
  let E := etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance
  let P := upperStar (ModuleCat.{u + 1} A) c.g
  let R := lowerStar (ModuleCat.{u + 1} A) c.g
  let e : Q ⋙ upperStar (ModuleCat.{u + 1} A) s ≅ 𝟭 _ :=
    (upperStarComp (ModuleCat.{u + 1} A) s q (𝟙 U) hs₂.symm).symm ≪≫ upperStarId _ U
  let π : Q ⟶ S :=
    (Functor.rightUnitor Q).inv ≫
      Functor.whiskerLeft Q (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).unit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight e.hom (lowerStar (ModuleCat.{u + 1} A) s) ≫
      (Functor.leftUnitor _).hom ≫
      (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) s)).inv
  let comp : S ⋙ V ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
    (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) s).comp
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)).ofNatIsoRight
        (upperStarComp (ModuleCat.{u + 1} A) s v c.i hs₁.symm).symm).leftAdjointUniq
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
  let δ : E ⋙ P ⟶ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
    (etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g u)).hom ≫
      Functor.whiskerRight π V ≫ comp.hom
  exact (Functor.rightUnitor E).inv ≫
    Functor.whiskerLeft E (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).unit ≫
    (Functor.associator E P R).inv ≫ Functor.whiskerRight δ R

end AlgebraicGeometry.Etale
