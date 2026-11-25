/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import all WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalFiniteProperMate
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-! # Invertibility of open comparison mates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

attribute [local instance 20000] strictEtaleSystemDerived strictEtaleLevelDerived
  exceptionalProSystemDerived exceptionalProLevelDerived

private theorem supportedInverseMate {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') [IsIso a.unit] [IsIso b.unit]
    {F : C ⥤ C'} {H : D ⥤ D'} (β : R ⋙ F ≅ H ⋙ R')
    (e : L ⋙ H ≅ F ⋙ L') :
    IsIso (((mateEquiv a b).symm (.mk _ _ _ _ β.hom))) := by
  let α := ((mateEquiv a b).symm (.mk _ _ _ _ β.hom))
  have hu := unit_mateEquiv_symm a b (.mk _ _ _ _ β.hom)
  have hi (M : C) : IsIso (R'.map (α.app M)) := by
    have hh := hu M
    change F.map (a.unit.app M) ≫ β.hom.app (L.obj M) =
      b.unit.app (F.obj M) ≫ R'.map (α.app M) at hh
    have : IsIso (b.unit.app (F.obj M) ≫ R'.map (α.app M)) := by
      rw [← hh]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp this
  have ff := b.fullyFaithfulLOfIsIsoUnit
  have : L'.Full := ff.full
  have : L'.Faithful := ff.faithful
  have hc (M : C) : IsIso (b.counit.app (H.obj (L.obj M))) :=
    b.isIso_counit_app_of_iso (e.app M)
  have hα (M : C) : IsIso (α.app M) := by
    have hh := b.counit.naturality (α.app M)
    change L'.map (R'.map (α.app M)) ≫ b.counit.app (H.obj (L.obj M)) =
      b.counit.app (L'.obj (F.obj M)) ≫ α.app M at hh
    have : IsIso (L'.map (R'.map (α.app M)) ≫ b.counit.app (H.obj (L.obj M))) := by
      infer_instance
    rw [hh] at this
    exact (isIso_comp_left_iff _ _).mp this
  exact NatIso.isIso_of_isIso_app α

private theorem unitIsoTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {l : C ⥤ D} {r : D ⥤ C}
    (a : L ⊣ R) (b : l ⊣ r) [IsIso b.unit]
    {F : A ⥤ C} {H : B ⥤ D} [F.IsEquivalence] [H.IsEquivalence]
    (e : R ⋙ F ≅ H ⋙ r) : IsIso a.unit := by
  let α := ((mateEquiv a b).symm e.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences a b e
  have hunit (X : A) : IsIso (a.unit.app X) := by
    have hh := unit_mateEquiv_symm a b e.hom X
    change F.map (a.unit.app X) ≫ e.hom.app (L.obj X) =
      b.unit.app (F.obj X) ≫ r.map (α.app X) at hh
    have : IsIso (F.map (a.unit.app X) ≫ e.hom.app (L.obj X)) := by
      rw [hh]
      infer_instance
    have : IsIso (F.map (a.unit.app X)) :=
      (isIso_comp_right_iff _ _).mp this
    exact isIso_of_reflects_iso _ F
  exact NatIso.isIso_of_isIso_app a.unit

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

/-- Inverse mates of the normalized ordinary open pullback squares are invertible.
Source: Zheng Construction 5.15 and Lemmas 4.10 and 5.22; Stacks 09AF.
(blueprint: lem-sf-exceptional-system-level-open-mate-invertibility).

Proof: Transport the finite coefficient module categories to sheaves of modules over
one fixed quotient ring. The open inverse-image adjunctions have invertible units,
and the canonical extension-by-zero comparison identifies the two left-adjoint paths.
The unit equation for the inverse mate proves its inverse-image image invertible.
The counit is invertible on the supported essential image, so its naturality implies
that the mate itself is invertible. Transport back through the fully faithful
coefficient equivalences. -/
theorem exceptionalSystemLevelOpenMate_isIso
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (_hX : ExceptionalSystemSiteEquivalence CX)
    (_hY : ExceptionalSystemSiteEquivalence CY)
    (_hZ : ExceptionalSystemSiteEquivalence CZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
    (R : ExceptionalSystemPullbackSquare c.i CX CZ
      S.openImage P.val.openImage S.openDerived P.val.openDerived) :
    ∀ n, IsIso (((mateEquiv (S.val.levelOpenAdjunction n)
      (P.val.levelOpenAdjunction n)).symm
      (.mk _ _ _ _ (R.level n).inv))) := by
  intro n
  let A := O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)
  let B := CommRingCat.of A
  let rEX := finiteConstantModule X.smallEtaleTopology B
  let rEZ := finiteConstantModule c.Z.smallEtaleTopology B
  let rPX := finiteConstantModule (Scheme.ProEt.topology X) B
  let rPZ := finiteConstantModule (Scheme.ProEt.topology c.Z) B
  have : rEX.IsEquivalence := finiteConstantEquivalence _ B
  have : rEZ.IsEquivalence := finiteConstantEquivalence _ B
  have : rPX.IsEquivalence := finiteConstantEquivalence _ B
  have : rPZ.IsEquivalence := finiteConstantEquivalence _ B
  let pEt := MorphismProperty.Over.pullback @Etale ⊤ c.i
  let pPro := MorphismProperty.Over.pullback @WeaklyEtale ⊤ c.i
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : pEt.IsContinuous c.Z.smallEtaleTopology X.smallEtaleTopology :=
    Etale.isContinuous_overPullback c.i
  obtain ⟨u⟩ := finiteConstantLeft pEt O ell S.openImage n
  obtain ⟨v⟩ := finiteConstantLeft pPro O ell P.val.openImage n
  obtain ⟨gx⟩ := finiteConstantLeft (Scheme.toProEt X) O ell CX.ordinary n
  obtain ⟨gz⟩ := finiteConstantLeft (Scheme.toProEt c.Z) O ell CZ.ordinary n
  let a := S.val.levelOpenAdjunction n
  let b := P.val.levelOpenAdjunction n
  let ae := Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
  let bp := ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
  have : IsIso a.unit := unitIsoTransport a ae u
  have : IsIso b.unit := unitIsoTransport b bp v
  let α := ((mateEquiv a ae).symm u.hom)
  let β := ((mateEquiv b bp).symm v.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences a ae u
  have : IsIso β := isIso_inverseMate_of_equivalences b bp v
  let je := (asIso α).symm
  let jp := (asIso β).symm
  let e : S.val.levelOpen n ⋙ (CZ.ordinary.lift n).modules ⋙ rPZ ≅
      (CX.ordinary.lift n).modules ⋙ P.val.levelOpen n ⋙ rPZ :=
    Functor.isoWhiskerLeft _ gz ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight je _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft rEX
        (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) c.i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight gx.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ jp.symm
  let ff := rPZ.asEquivalence.fullyFaithfulFunctor.whiskeringRight
    (strictEtaleLevel X O ell n)
  let e' : S.val.levelOpen n ⋙ (CZ.ordinary.lift n).modules ≅
      (CX.ordinary.lift n).modules ⋙ P.val.levelOpen n :=
    ff.preimageIso ((Functor.associator _ _ _) ≪≫ e ≪≫
      (Functor.associator _ _ _).symm)
  exact supportedInverseMate a b (R.level n).symm e'

end AlgebraicGeometry
