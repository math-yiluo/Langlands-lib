/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPushSquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientOrdinarySquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedSupportedCoefficientTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap

/-! # Normalized coefficient equivalences before transporting a diagonal class

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-completed-frame).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The fixed canonical right-derived condensed Z_l direct image.
Source: Stacks Tag 070G and the coefficient comparison.
(blueprint: lem-diagonal-completed-frame). -/
abbrev condensedDiagonalRightDerived (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :=
  canonicalDiagonalRightDerived
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)

/-- Coefficient equivalences, canonical direct-image squares, and supported-source
comparisons. This data contains no class, trace, or integration assertion.
Source: blueprint coefficient changes, paragraph (1).
(blueprint: lem-diagonal-completed-frame). -/
structure CompletedFrame (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (rootsY : IntegralRoots l (bottomField l) Y)
    (rootsP : IntegralRoots l (bottomField l) (ProjectiveLine Y))
    (rootsW : IntegralRoots l (bottomField l) (diagonalSurface Y))
    (tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y))
    (t₁ : DiagonalTrace.Result l (ULift.{u} (Padic l))
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (t₂ : DiagonalTrace.Result l (ULift.{u} (Padic l))
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (a₁ : DiagonalTrace.SupportedSource l Y
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₁.Rc)
    (a₂ : DiagonalTrace.SupportedSource l Y
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₂.Rc) where
  eY : CompletedRealization l Y
  eP : CompletedRealization l (ProjectiveLine Y)
  eW : CompletedRealization l (diagonalSurface Y)
  rootsY_eq : eY.roots = rootsY
  rootsP_eq : eP.roots = rootsP
  rootsW_eq : eW.roots = rootsW
  sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
    source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y
  source_normalization :
    HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ sourceIso.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom))
  support₁ : DiagonalTrace.NormalizedSource
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
      (condensedDiagonalRightDerived l
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)))
    (diagonalImmersion Y ≫
      pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) = 𝟙 _)
    (SupportNormalization (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y _)
  support₂ : DiagonalTrace.NormalizedSource
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
      (condensedDiagonalRightDerived l
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)))
    (diagonalImmersion Y ≫
      pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) = 𝟙 _)
    (SupportNormalization (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y _)
  q_ordinary : CompletedOrdinarySquare l (ProjectiveLine Y ↘ Y) eP eY
  p₁_ordinary : CompletedOrdinarySquare l
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) eW eP
  p₂_ordinary : CompletedOrdinarySquare l
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) eW eP
  source₁ : eP.F.mapDerivedCategory.map a₁.hom ≫
      (p₁_ordinary.derive (R := t₁.Rc) (R' := condensedDiagonalRightDerived l
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))).derived.iso.hom.app _ ≫
      (condensedDiagonalRightDerived l
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).R.map
        ((eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor
            (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y)) 0).map
              sourceIso.hom) = eP.singleUnit l (ProjectiveLine Y) ≫ support₁.hom
  source₂ : eP.F.mapDerivedCategory.map a₂.hom ≫
      (p₂_ordinary.derive (R := t₂.Rc) (R' := condensedDiagonalRightDerived l
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))).derived.iso.hom.app _ ≫
      (condensedDiagonalRightDerived l
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).R.map
        ((eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor
            (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y)) 0).map
              sourceIso.hom) = eP.singleUnit l (ProjectiveLine Y) ≫ support₂.hom

/-- Construct the normalized coefficient equivalences and their direct-image
squares, independently of any diagonal class or integration identity.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), initial coefficient
identification. (blueprint: lem-diagonal-completed-frame).

Proof: Identify the completed ring with the limit of finite constant rings and
then with the pulled-back condensed Z_l ring, using its specified projections.
The equivalence between internal module objects and sectionwise module sheaves
and transport along that ring isomorphism give eY, eP, eW. Their underlying
sheaves are unchanged. The regular and line comparisons are normalized by the
coefficient and root projections. Choose the canonical right derived functors
with their universal units. The ordinary direct-image squares are identity on
underlying sheaves; exact equivalences transport K-injective computations and
uniquely determine the derived squares on their full universal units. The
supported source is the direct image of the regular module along the diagonal.
Composition of direct images and the equation p_i Delta = id give its normalized
ordinary source isomorphism. This source is acyclic because the closed immersion
is exact and its composite with p_i is the identity. Naturality of the universal
unit on the single supported source gives source₁ and source₂. No class or trace
is chosen in this construction; they will be transported through this frame. -/
theorem diagonalCompleted_frame
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (rootsY : IntegralRoots l (bottomField l) Y)
    (rootsP : IntegralRoots l (bottomField l) (ProjectiveLine Y))
    (rootsW : IntegralRoots l (bottomField l) (diagonalSurface Y))
    (tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y))
    (t₁ : DiagonalTrace.Result l (ULift.{u} (Padic l))
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (t₂ : DiagonalTrace.Result l (ULift.{u} (Padic l))
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (a₁ : DiagonalTrace.SupportedSource l Y
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₁.Rc)
    (a₂ : DiagonalTrace.SupportedSource l Y
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₂.Rc) :
    Nonempty (CompletedFrame l Y rootsY rootsP rootsW tq t₁ t₂ a₁ a₂) := by
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using
      hP.map (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).appTop.hom
  obtain ⟨eY⟩ := completedCoefficientRealization_exists l Y hY
  obtain ⟨eP⟩ := completedCoefficientRealization_exists l (ProjectiveLine Y) hP
  obtain ⟨eW⟩ := completedCoefficientRealization_exists l (diagonalSurface Y) hW
  obtain ⟨sq⟩ := completedCoefficientOrdinarySquare_exists l (ProjectiveLine Y ↘ Y) eP eY
  obtain ⟨s₁⟩ := completedCoefficientOrdinarySquare_exists l
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) eW eP
  obtain ⟨s₂⟩ := completedCoefficientOrdinarySquare_exists l
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) eW eP
  obtain ⟨sΔ⟩ := completedCoefficientOrdinarySquare_exists l (diagonalImmersion Y) eP eW
  have hi := completedSupportedCoefficientIso_normalization l Y eP eW sΔ
  have hs := completedSupportedCoefficient_transport l Y eP eW sΔ
  obtain ⟨b₁, hb₁⟩ := hs _ t₁.Rc a₁ s₁
  obtain ⟨b₂, hb₂⟩ := hs _ t₂.Rc a₂ s₂
  exact ⟨{
    eY := eY
    eP := eP
    eW := eW
    rootsY_eq := diagonalIntegralRoots_unique l Y (bottomField l) eY.roots rootsY
    rootsP_eq := diagonalIntegralRoots_unique l (ProjectiveLine Y)
      (bottomField l) eP.roots rootsP
    rootsW_eq := diagonalIntegralRoots_unique l (diagonalSurface Y)
      (bottomField l) eW.roots rootsW
    sourceIso := completedSupportedCoefficientIso l Y eP eW sΔ
    source_normalization := hi
    support₁ := b₁
    support₂ := b₂
    q_ordinary := sq
    p₁_ordinary := s₁
    p₂_ordinary := s₂
    source₁ := hb₁
    source₂ := hb₂ }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
