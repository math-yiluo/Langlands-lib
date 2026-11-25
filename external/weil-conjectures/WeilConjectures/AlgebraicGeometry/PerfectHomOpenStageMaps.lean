/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedData
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section

/-- First move the shift to P, then use open adjunction, then commute restriction
with the source shift. Every factor is an explicitly constructed equivalence. -/
private def openShiftEquiv (Y : Scheme.{u}) (B : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toScheme.toRingedSpace))]
    (P E : schemeDerivedCategory Y) (n : ℤ) :
    (P ⟶ ((schemeMVDerivedRestriction Y B ⋙ schemeDerivedDirectImage B.ι).obj E)⟦n⟧) ≃
      (((schemeMVDerivedRestriction Y B).obj P)⟦-n⟧ ⟶
        (schemeMVDerivedRestriction Y B).obj E) :=
  ((shiftEquiv' (schemeDerivedCategory Y) (-n) n (neg_add_cancel n)).toAdjunction.homEquiv
    P ((schemeMVDerivedRestriction Y B ⋙ schemeDerivedDirectImage B.ι).obj E)).symm |>.trans
    ((schemeMVAdjunction Y B).homEquiv (P⟦-n⟧)
      ((schemeMVDerivedRestriction Y B).obj E)).symm |>.trans
    (((schemeMVDerivedRestriction Y B).commShiftIso (-n)).app P).homFromEquiv
/-- Both Hom adjunctions are natural in the target; the final source comparison
is fixed, so its precomposition commutes with target postcomposition. -/
private theorem openShiftEquiv_natural (Y : Scheme.{u}) (B : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toScheme.toRingedSpace))]
    (P E E' : schemeDerivedCategory Y) (n : ℤ)
    (g : E ⟶ E')
    (f : P ⟶ ((schemeMVDerivedRestriction Y B ⋙ schemeDerivedDirectImage B.ι).obj E)⟦n⟧) :
    openShiftEquiv Y B P E' n
      (f ≫ ((schemeMVDerivedRestriction Y B ⋙ schemeDerivedDirectImage B.ι).map g)⟦n⟧') =
      openShiftEquiv Y B P E n f ≫ (schemeMVDerivedRestriction Y B).map g := by
  simp only [openShiftEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_right_symm]
  exact (Category.assoc _ _ _).symm

/-- The Hom equivalences and their stage/apex compatibility after a chosen open
localization. Source: Stacks Project, perfect.tex Tags 09RE and 079W.
(blueprint: lem-pc-perfect-hom-open-stage-maps).
Proof: Put B = t inverse-image W and L = exact derived restriction to B.
Yoneda and derived adjunction identify F_j with Rpi_j* Lpi_j*Q;
evaluate stageNatural at identities to recover the representing isomorphism.
Apply the canonical open-restriction/direct-image comparison to this isomorphism.
The restricted projection is canonically the pullback projection for B.ι ≫ s.
Open adjunction and shift adjunction identify Hom(P,RB.ι* LF_j[n]) with
Hom(LP[-n],LF_j). Derived adjunction for the restricted projection and the
pullback-composition comparison give the displayed stage equivalences for
P' = LP[-n] and Q' = LQ. Repeat at the apex. Naturality of these comparisons,
with h.stageMap and h.limitMap, proves both displayed equations; the comparisons
are pinned by their derived units and counits, hence give exactly the specified
perfectStageMap and perfectLimitMap. The same constructions work on empty opens,
where all Hom sets are singletons, and for zero objects.

The implemented reduction first restricts the unshifted representing cocone using
perfect_hom_open_restricted_data. The completely proved openShiftEquiv is the
composite of (shiftEquiv' _ (-n) n (neg_add_cancel n)).toAdjunction.homEquiv.symm,
(schemeMVAdjunction Y B).homEquiv.symm, and precomposition with the inverse of
(L.commShiftIso (-n)).app P. Its target postcomposition identity is
openShiftEquiv_natural. Compose it with hB.stageEquiv j (LP[-n]) and hB.limitEquiv
(LP[-n]), respectively. Rewriting by this identity leaves precisely hB.stageMap
and hB.limitMap. Only the unshifted localization is left open in a separate module. -/
theorem perfect_hom_open_stage_maps
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u})
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (W : X.Opens)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (s : Y ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ B : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over B))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) (n : ℤ) :
    let B := t ⁻¹ᵁ W
    let s' := B.ι ≫ s
    let P' := ((schemeMVDerivedRestriction Y B).obj P)⟦-n⟧
    let Q' := (schemeMVDerivedRestriction Y B).obj Q
    let H := schemeMVDerivedRestriction Y B ⋙ schemeDerivedDirectImage B.ι
    ∃ (e : ∀ j : Set.Ici i, (P ⟶ (H.obj (F.obj j))⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj Q'))
      (b : (P ⟶ (H.obj d.pt)⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj Q')),
      (∀ (j l : Set.Ici i) (hjl : j ≤ l) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        e l (f ≫ (H.map (F.map (homOfLE hjl)))⟦n⟧') =
          perfectStageMap R s' j.property hjl (e j f)) ∧
      (∀ (j : Set.Ici i) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        b (f ≫ (H.map (d.ι.app j))⟦n⟧') =
          perfectLimitMap R c s' j.property (e j f)) := by
  classical
  let B := t ⁻¹ᵁ W
  let L := schemeMVDerivedRestriction Y B
  let P' := (L.obj P)⟦-n⟧
  obtain ⟨a⟩ := nonempty_derivedPullbackAdjunction B.ι
  obtain ⟨hB, _, _⟩ := perfect_hom_open_restricted_data R c s B a Q F d h
  let e (j : Set.Ici i) :=
    (openShiftEquiv Y B P (F.obj j) n).trans (hB.stageEquiv j P')
  let b := (openShiftEquiv Y B P d.pt n).trans (hB.limitEquiv P')
  refine ⟨e, b, ?_, ?_⟩
  · intro j l hjl f
    change hB.stageEquiv l P'
        (openShiftEquiv Y B P (F.obj l) n
          (f ≫ ((L ⋙ schemeDerivedDirectImage B.ι).map (F.map (homOfLE hjl)))⟦n⟧')) =
      perfectStageMap R (B.ι ≫ s) j.property hjl
        (hB.stageEquiv j P' (openShiftEquiv Y B P (F.obj j) n f))
    rw [openShiftEquiv_natural]
    exact hB.stageMap j l hjl P' (openShiftEquiv Y B P (F.obj j) n f)
  · intro j f
    change hB.limitEquiv P'
        (openShiftEquiv Y B P d.pt n
          (f ≫ ((L ⋙ schemeDerivedDirectImage B.ι).map (d.ι.app j))⟦n⟧')) =
      perfectLimitMap R c (B.ι ≫ s) j.property
        (hB.stageEquiv j P' (openShiftEquiv Y B P (F.obj j) n f))
    rw [openShiftEquiv_natural]
    exact hB.limitMap j P' (openShiftEquiv Y B P (F.obj j) n f)
end
end AlgebraicGeometry
