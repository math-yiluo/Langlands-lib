/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceNormalization
import WeilConjectures.AlgebraicGeometry.SfSupportedFirstExtraction
import WeilConjectures.AlgebraicGeometry.SfSupportedSecondExtraction
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-! # Compact-support coordinate contractions before inserting a diagonal

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the exchange and projection computations in both triangles.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SupportedTrace

variable (A : Type (u + 1)) [CommRing A] [Finite A]

section Normalization

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]

omit [UpperStarPreservesFlat C] in
open MonoidalCategory BraidedCategory in
private theorem swap_trace (Z : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (t : N ⟶ derivedTensorUnit C Z) :
    (((derivedTensorSymmetry C Z).app M).app N).hom ≫
        ((derivedTensor C Z).map t).app M ≫
        (derivedTensorUnitLeftUnitor C Z).hom.app M =
      ((derivedTensor C Z).obj M).map t ≫ (derivedTensorRightUnitor C Z M).hom := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Z.smallEtaleTopology C)
  change N ⟶ 𝟙_ _ at t
  change (β_ M N).hom ≫ t ▷ M ≫ (λ_ M).hom = M ◁ t ≫ (ρ_ M).hom
  rw [← braiding_naturality_right_assoc, braiding_leftUnitor]

open MonoidalCategory BraidedCategory in
private theorem shuffle_trace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (N K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (t : N ⟶ derivedTensorUnit C Y) :
    (extractionShuffle C f B N K).hom ≫
        ((derivedTensor C X).obj B).map
          ((upperStar C f).leftDerivedFunctor.map
            (((derivedTensor C Y).map t).app K ≫
              (derivedTensorUnitLeftUnitor C Y).hom.app K)) =
      ((derivedTensor C X).obj
        (((derivedTensor C X).obj B).obj ((upperStar C f).leftDerivedFunctor.obj K))).map
          ((upperStar C f).leftDerivedFunctor.map t ≫
            (leftDerivedUpperStarDerivedTensorUnitIso f).hom) ≫
        (derivedTensorRightUnitor C X
          (((derivedTensor C X).obj B).obj ((upperStar C f).leftDerivedFunctor.obj K))).hom := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology C)
  let P := (upperStar C f).leftDerivedFunctor
  have hn := congr_app ((leftDerivedUpperStarTensorComparison C f).naturality t) K
  have hu := leftDerivedUpperStarTensorComparison_leftUnitor_hom C f K
  change P.map (((derivedTensor C Y).map t).app K) ≫
      (leftDerivedUpperStarTensorIso C f (derivedTensorUnit C Y) K).hom =
    (leftDerivedUpperStarTensorIso C f N K).hom ≫
      ((derivedTensor C X).map (P.map t)).app (P.obj K) at hn
  change (leftDerivedUpperStarTensorIso C f (derivedTensorUnit C Y) K).hom ≫
      ((derivedTensor C X).map (leftDerivedUpperStarDerivedTensorUnitIso f).hom).app
        (P.obj K) ≫ (derivedTensorLeftUnitor C X (P.obj K)).hom =
    P.map ((derivedTensorUnitLeftUnitor C Y).hom.app K) at hu
  have hi : (leftDerivedUpperStarTensorIso C f N K).inv ≫
      P.map (((derivedTensor C Y).map t).app K) =
      ((derivedTensor C X).map (P.map t)).app (P.obj K) ≫
        (leftDerivedUpperStarTensorIso C f (derivedTensorUnit C Y) K).inv := by
    apply (cancel_mono (leftDerivedUpperStarTensorIso C f (derivedTensorUnit C Y) K).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using
      congrArg ((leftDerivedUpperStarTensorIso C f N K).inv ≫ ·) hn
  have he : (leftDerivedUpperStarTensorIso C f (derivedTensorUnit C Y) K).inv ≫
      P.map ((derivedTensorUnitLeftUnitor C Y).hom.app K) =
      ((derivedTensor C X).map (leftDerivedUpperStarDerivedTensorUnitIso f).hom).app
          (P.obj K) ≫ (derivedTensorLeftUnitor C X (P.obj K)).hom := by
    apply (cancel_epi (leftDerivedUpperStarTensorIso C f (derivedTensorUnit C Y) K).hom).1
    simpa only [Iso.hom_inv_id_assoc] using hu.symm
  let Q := (derivedTensor C X).obj (P.obj K)
  let t' := P.map t ≫ (leftDerivedUpperStarDerivedTensorUnitIso f).hom
  change P.obj N ⟶ 𝟙_ _ at t'
  have inner :
      (((derivedTensorSymmetry C X).app (P.obj K)).app (P.obj N)).hom ≫
          (leftDerivedUpperStarTensorIso C f N K).inv ≫
          P.map (((derivedTensor C Y).map t).app K ≫
            (derivedTensorUnitLeftUnitor C Y).hom.app K) =
        Q.map t' ≫ (derivedTensorRightUnitor C X (P.obj K)).hom := by
    calc
      _ = (((derivedTensorSymmetry C X).app (P.obj K)).app (P.obj N)).hom ≫
          ((derivedTensor C X).map (P.map t)).app (P.obj K) ≫
          (leftDerivedUpperStarTensorIso C f (derivedTensorUnit C Y) K).inv ≫
          P.map ((derivedTensorUnitLeftUnitor C Y).hom.app K) := by
            rw [P.map_comp, reassoc_of% hi]
      _ = (((derivedTensorSymmetry C X).app (P.obj K)).app (P.obj N)).hom ≫
          ((derivedTensor C X).map (P.map t)).app (P.obj K) ≫
          ((derivedTensor C X).map
            (leftDerivedUpperStarDerivedTensorUnitIso f).hom).app (P.obj K) ≫
          (derivedTensorLeftUnitor C X (P.obj K)).hom := by rw [he]
      _ = (((derivedTensorSymmetry C X).app (P.obj K)).app (P.obj N)).hom ≫
          ((derivedTensor C X).map t').app (P.obj K) ≫
          (derivedTensorUnitLeftUnitor C X).hom.app (P.obj K) := by
            simp only [t', Functor.map_comp, NatTrans.comp_app, Category.assoc]
            rfl
      _ = _ := swap_trace C X (P.obj K) (P.obj N) t'
  calc
    _ = (derivedTensorAssociator C X B (P.obj K) (P.obj N)).hom ≫
        ((derivedTensor C X).obj B).map
          ((((derivedTensorSymmetry C X).app (P.obj K)).app (P.obj N)).hom ≫
            (leftDerivedUpperStarTensorIso C f N K).inv ≫
            P.map (((derivedTensor C Y).map t).app K ≫
              (derivedTensorUnitLeftUnitor C Y).hom.app K)) := by
                simp only [P, extractionShuffle, Iso.trans_hom, Functor.mapIso_hom,
                  Iso.symm_hom, Functor.map_comp, Category.assoc]
    _ = (derivedTensorAssociator C X B (P.obj K) (P.obj N)).hom ≫
        ((derivedTensor C X).obj B).map
          (Q.map t' ≫ (derivedTensorRightUnitor C X (P.obj K)).hom) := by rw [inner]
    _ = _ := by
      change (α_ B (P.obj K) (P.obj N)).hom ≫
          B ◁ (P.obj K ◁ t' ≫ (ρ_ (P.obj K)).hom) =
        (B ⊗ P.obj K) ◁ t' ≫ (ρ_ (B ⊗ P.obj K)).hom
      rw [whiskerLeft_comp, ← associator_naturality_right_assoc, ← rightUnitor_tensor_hom]

end Normalization

section ProperNormalization

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]
  {FC : C → C → Type (u + 1)} {CC : C → Type (u + 1)}
  [∀ (P Q : C), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} C FC]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget C)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget C)]

private theorem proper_trace {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (t : N ⟶ derivedTensorUnit C Y)
    (hn : ((rightDerivedLowerStarProjectionMap C f).app M).app N ≫
      (lowerStar C f).rightDerivedFunctor.map
        (((derivedTensor C X).obj M).map
          ((upperStar C f).leftDerivedFunctor.map t ≫
            (leftDerivedUpperStarDerivedTensorUnitIso f).hom) ≫
          (derivedTensorRightUnitor C X M).hom) =
      ((derivedTensor C Y).obj ((lowerStar C f).rightDerivedFunctor.obj M)).map t ≫
        (derivedTensorRightUnitor C Y ((lowerStar C f).rightDerivedFunctor.obj M)).hom) :
    ((projectionMap C f).app M).app N ≫
      (rightDerivedLowerShriek C f).map
        (((derivedTensor C X).obj M).map
          ((upperStar C f).leftDerivedFunctor.map t ≫
            (leftDerivedUpperStarDerivedTensorUnitIso f).hom) ≫
          (derivedTensorRightUnitor C X M).hom) =
      ((derivedTensor C Y).obj ((rightDerivedLowerShriek C f).obj M)).map t ≫
        (derivedTensorRightUnitor C Y ((rightDerivedLowerShriek C f).obj M)).hom := by
  let S := rightDerivedLowerShriekIsoRightDerivedLowerStar C f
  let w := ((derivedTensor C X).obj M).map
      ((upperStar C f).leftDerivedFunctor.map t ≫
        (leftDerivedUpperStarDerivedTensorUnitIso f).hom) ≫
    (derivedTensorRightUnitor C X M).hom
  have hp := projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar C f M N
  have hs := S.hom.naturality w
  have ht := ((derivedTensor C Y).map (S.hom.app M)).naturality t
  have hu := (derivedTensorRightUnitorNatIso C Y).hom.naturality (S.hom.app M)
  change ((derivedTensor C Y).map (S.hom.app M)).app (derivedTensorUnit C Y) ≫
      (derivedTensorRightUnitor C Y ((lowerStar C f).rightDerivedFunctor.obj M)).hom =
    (derivedTensorRightUnitor C Y ((rightDerivedLowerShriek C f).obj M)).hom ≫ S.hom.app M at hu
  apply (cancel_mono (S.hom.app M)).1
  simp only [Category.assoc]
  change _ ≫ (rightDerivedLowerShriek C f).map w ≫ S.hom.app M = _
  rw [hs, ← Category.assoc, hp, Category.assoc, hn]
  rw [← Category.assoc, ← ht, Category.assoc, hu]

end ProperNormalization

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor derivedTensorSymmetry

attribute [local implicit_reducible] rightDerivedLowerShriek derivedTensorRight

private theorem projection_iso_hom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (M : DerivedCategoryModule A X) :
    (projectionIso A f M).hom = (projectionMap (ModuleCat.{u + 1} A) f).app M := by
  rw [projectionIso, asIso_hom]

omit [Finite A] in
private theorem ordinary_trace {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : DerivedCategoryModule A X)
    (N : DerivedCategoryModule A Y) (t : N ⟶ derivedTensorUnit (ModuleCat.{u + 1} A) Y) :
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app N ≫
        (CoordinateTrace.push A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              ((CoordinateTrace.pull A f).map t ≫
                (leftDerivedUpperStarDerivedTensorUnitIso f).hom) ≫
            (unitRightUnitor (ModuleCat.{u + 1} A) X M).hom) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
        ((CoordinateTrace.push A f).obj M)).map t ≫
        (unitRightUnitor (ModuleCat.{u + 1} A) Y ((CoordinateTrace.push A f).obj M)).hom := by
  exact CoordinateTrace.projectionTraceNormalization A f M N t

private theorem supported_projection_trace {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (M : DerivedCategoryModule A X)
    (N : DerivedCategoryModule A Y) (t : N ⟶ derivedTensorUnit (ModuleCat.{u + 1} A) Y) :
    (projectionIso A f M).hom.app N ≫
        (push A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              ((CoordinateTrace.pull A f).map t ≫
                (leftDerivedUpperStarDerivedTensorUnitIso f).hom) ≫
            (unitRightUnitor (ModuleCat.{u + 1} A) X M).hom) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((push A f).obj M)).map t ≫
        (unitRightUnitor (ModuleCat.{u + 1} A) Y ((push A f).obj M)).hom := by
  rw [projection_iso_hom]
  exact proper_trace (ModuleCat.{u + 1} A) f M N t (ordinary_trace A f M N t)

/-- Coordinate contractions for compact support, without using the diagonal class or its integrals.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the two exchange/projection
computations before inserting delta (auxiliary; not a blueprint node).

Proof: Apply firstExtraction, the coordinate Kunneth identity before a trace is chosen.
Postcompose with the trace and the left unitor. Naturality of symmetry moves the trace
past the final swap, and its compatibility with the unitors gives the right unitor.
ProjectionTraceNormalization transports through the proper forget-supports isomorphism:
projection compatibility, naturality of that isomorphism, tensor naturality and unitor
naturality prove supported_projection_trace. Cancel the invertible projection, combine
the two direct-image maps, and expand traceFirst. This gives the first equality without
using the line condition or e.
For the second equality apply secondExtraction with evenLineSelfSymmetry and e, then
postcompose with B tensor f* of trace tensor identity followed by the left unitor.
Naturality and left unitality of the tensor pullback comparison, symmetry naturality
and the right-unitor tensor identity prove shuffle_trace. This identifies the resulting
map with tensoring the identity by the pulled-back scalar trace, followed by the right
unitor. Combining that scalar trace with inverse coordinate comparison and inverse
exchange gives exactly traceSecond. On the other side the same factors form the given
counit inside the coefficient-first twisted pullback. Every map is the specified
canonical one; the diagonal class and its integral normalization never occur. -/
theorem contractions {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ) {B : DerivedCategoryModule A X}
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (d : TraceDiagonalDatum A f B) :
    (∀ M : DerivedCategoryModule A X,
      (push A f).map (comparison A f B M).hom ≫ (SfDiagonalKernel.counit A d).app ((push A f).obj
        M) =
        (directComparison A f).hom.app (kernel A f B M) ≫
          (push A f).map
            ((orderedProjection A (pullback.fst f f) M
                ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv ≫
              ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
                (SfDiagonalKernel.traceFirst A d) ≫
                (unitRightUnitor (ModuleCat.{u + 1} A) X M).hom)) ∧
    (∀ K : DerivedCategoryModule A Y,
      (comparison A f B ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj
        B).obj K)).hom ≫
          (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).map
            ((SfDiagonalKernel.counit A d).app K) =
        (push A (pullback.snd f f)).map
            (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
              (coordinateTwisted A f (CoordinateTrace.shiftedLine A J n) K e).hom).app
                ((CoordinateTrace.pull A (pullback.snd f f)).obj B)) ≫
          (orderedProjection A (pullback.snd f f) ((CoordinateTrace.pull A f ⋙ (derivedTensor
            (ModuleCat.{u + 1} A) X).obj B).obj K)
              ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv ≫
            ((derivedTensor (ModuleCat.{u + 1} A) X).obj
                ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
                  K)).map
              (SfDiagonalKernel.traceSecond A d (CoordinateTrace.shiftedLine A J n) e) ≫
              (unitRightUnitor (ModuleCat.{u + 1} A) X
                ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
                  K)).hom) := by
  constructor
  · intro M
    let T := (derivedTensor (ModuleCat.{u + 1} A) X).obj M
    let U := (derivedTensor (ModuleCat.{u + 1} A) Y).obj ((push A f).obj M)
    let a := (orderedProjection A (pullback.fst f f) M
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv ≫
      T.map ((SfDiagonalKernel.exchangeFirst A f).inv.app B)
    let w := T.map ((CoordinateTrace.pull A f).map d.trace ≫
        (leftDerivedUpperStarDerivedTensorUnitIso f).hom) ≫
      (unitRightUnitor (ModuleCat.{u + 1} A) X M).hom
    have hp : (projectionIso A f M).inv.app ((push A f).obj B) ≫
        U.map d.trace ≫
        (unitRightUnitor (ModuleCat.{u + 1} A) Y ((push A f).obj M)).hom =
        (push A f).map w := by
      apply (cancel_epi ((projectionIso A f M).hom.app ((push A f).obj B))).1
      simpa only [Iso.hom_inv_id_app_assoc] using
        (supported_projection_trace A f M ((push A f).obj B) d.trace).symm
    have hswap :
        (CoordinateTrace.swap A Y ((push A f).obj M) ((push A f).obj B)).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) Y).map d.trace).app ((push A f).obj M) ≫
          (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom.app ((push A f).obj M) =
        U.map d.trace ≫
          (unitRightUnitor (ModuleCat.{u + 1} A) Y ((push A f).obj M)).hom :=
      swap_trace (ModuleCat.{u + 1} A) Y ((push A f).obj M) ((push A f).obj B) d.trace
    calc
      _ = (push A f).map (comparison A f B M).hom ≫
          (projectionIso A f B).inv.app ((push A f).obj M) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) Y).map d.trace).app
            ((push A f).obj M) ≫
          (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom.app
            ((push A f).obj M) := by
              simp only [SfDiagonalKernel.counit, NatTrans.comp_app]
      _ = (directComparison A f).hom.app (kernel A f B M) ≫
          (push A f).map a ≫
          (projectionIso A f M).inv.app ((push A f).obj B) ≫
          (CoordinateTrace.swap A Y ((push A f).obj M) ((push A f).obj B)).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) Y).map d.trace).app
            ((push A f).obj M) ≫
          (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom.app
            ((push A f).obj M) := by
              rw [← Category.assoc, ← Category.assoc, firstExtraction]
              simp only [a, T, Category.assoc]
      _ = (directComparison A f).hom.app (kernel A f B M) ≫
          (push A f).map a ≫ (push A f).map w := by
              rw [hswap, hp]
      _ = _ := by
        rw [← (push A f).map_comp]
        simp only [a, w, SfDiagonalKernel.traceFirst, T, Functor.map_comp, Category.assoc]
  · intro K
    have hL := CoordinateTrace.evenLineSelfSymmetry A J hJ n
    have h := congrArg
      (fun z ↦ z ≫ ((derivedTensor (ModuleCat.{u + 1} A) X).obj B).map
        ((CoordinateTrace.pull A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) Y).map d.trace).app K ≫
            (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom.app K)))
      (secondExtraction A f (CoordinateTrace.shiftedLine A J n) hL e K)
    simp only [Category.assoc, shuffle_trace] at h
    simpa only [SfDiagonalKernel.counit, NatTrans.comp_app, Functor.comp_map, Functor.comp_obj,
      Functor.map_comp, SfDiagonalKernel.traceSecond, unitRightUnitor, Category.assoc] using h

end AlgebraicGeometry.Etale.SupportedTrace
