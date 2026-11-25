/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaQuasiIso

/-! # Descent of the coefficient augmentation to homology
Source: Stacks Project, Tags 03P2 and 01FD. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mapHomologyIso_inv_π
    {A B : Type*} [Category A] [Category B]
    [CategoryTheory.Limits.HasZeroMorphisms A] [CategoryTheory.Limits.HasZeroMorphisms B]
    (S : ShortComplex A) (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  let h := S.leftHomologyData
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  have hp : F.map h.π ≫ (h.map F).homologyIso.inv =
      (h.map F).cyclesIso.inv ≫ (S.map F).homologyπ := by
    simpa only [ShortComplex.LeftHomologyData.map_π] using
      (h.map F).π_comp_homologyIso_inv
  rw [← Category.assoc, ← F.map_comp, h.homologyπ_comp_homologyIso_hom,
    F.map_comp, Category.assoc, hp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Beta lifts cycles additively and descends to a bijective additive homology map.
Source: Stacks Project, Tag 03P2, Theorem 59.22.4, separated-case proof,
and Tag 01FD, Lemma 20.15.1, the coefficient augmentation.
(blueprint: lem-pbc-etale-additive-cech-beta-homology)

Proof: Forget module scalars in the ordinary unit Čech complex and apply ULift.
The structural-function coordinates restrictFunctorΓ identify each lifted
intersection section with the additive structure sheaf on that open subscheme.
Their naturality makes the coefficient augmentation into I⁰ commute with the
Čech differential. Its resolution differential is zero since I.ι is a chain
map from the single complex. Thus it is a chain map into the total, with
components given by additiveCechBeta after lifting. It takes cycles to cycles
and boundaries to boundaries; descend through the homology cokernel to obtain
b, with the stated representative formula. Each tuple intersection is affine,
so its positive étale quasi-coherent cohomology vanishes. The column
augmentations are quasi-isomorphisms, and the first-quadrant criterion applied
after flipping the double complex gives a quasi-isomorphism on totals. Exact
forgetting and ULift preserve homology; the finite-product coordinates and
identity scalar restriction identify the source homology with ordinary unit
cechOver homology. Thus b is bijective. The cycle map c is additive because
beta is additive and the inclusion of total cycles is injective. Degree zero
is the augmented kernel calculation. Empty intersections have zero sections;
an empty cover forces X empty, so all maps are between zero groups. -/
theorem exists_additiveCechBeta_homology
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    ∃ c : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n →+
      (additiveCechTotal U I).cycles n,
    ∃ b : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n →+
      (additiveCechTotal U I).homology n,
      Function.Bijective b ∧
      (∀ z, (additiveCechTotal U I).iCycles n (c z) = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)) ∧
      (∀ z, b ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z) =
        (additiveCechTotal U I).homologyπ n (c z)) := by
  let C := cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)
  let F := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let L := (F.mapHomologicalComplex (.up ℕ)).obj C
  obtain ⟨q, hqcomp, hq⟩ := exists_additiveCech_beta_quasiIso X U hU I
  let := hq
  let ez : L.cycles n ≅ F.obj (C.cycles n) := (C.sc n).mapCyclesIso F
  let eh : L.homology n ≅ F.obj (C.homology n) := (C.sc n).mapHomologyIso F
  let c : C.cycles n →+ (additiveCechTotal U I).cycles n :=
    (ez.inv ≫ HomologicalComplex.cyclesMap q n).hom.comp
      AddEquiv.ulift.symm.toAddMonoidHom
  let e : C.homology n ≃+ (additiveCechTotal U I).homology n :=
    AddEquiv.ulift.symm.trans
      ((eh.symm ≪≫ isoOfQuasiIsoAt q n).addCommGroupIsoToAddEquiv)
  have hi : ez.inv ≫ L.iCycles n = F.map (C.iCycles n) := by
    rw [← cancel_epi ez.hom, Iso.hom_inv_id_assoc]
    exact ((C.sc n).mapCyclesIso_hom_iCycles F).symm
  have hp : F.map (C.homologyπ n) ≫ eh.inv = ez.inv ≫ L.homologyπ n := by
    exact mapHomologyIso_inv_π (C.sc n) F
  refine ⟨c, e.toAddMonoidHom, e.bijective, ?_, ?_⟩
  · intro z
    have hz := congrArg (fun f ↦ f (ULift.up z)) hi
    change L.iCycles n (ez.inv (ULift.up z)) = ULift.up (C.iCycles n z) at hz
    change (additiveCechTotal U I).iCycles n
      ((HomologicalComplex.cyclesMap q n) (ez.inv (ULift.up z))) = _
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
    rw [ConcreteCategory.comp_apply]
    rw [hz]
    exact hqcomp n (C.iCycles n z)
  · intro z
    change (HomologicalComplex.homologyMap q n)
      (eh.inv (ULift.up (C.homologyπ n z))) =
        (additiveCechTotal U I).homologyπ n
          ((HomologicalComplex.cyclesMap q n) (ez.inv (ULift.up z)))
    have hz := congrArg (fun f ↦ f (ULift.up z)) hp
    change eh.inv (ULift.up (C.homologyπ n z)) =
      L.homologyπ n (ez.inv (ULift.up z)) at hz
    rw [hz, ← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality]
    rfl

end AlgebraicGeometry.Scheme.Modules
