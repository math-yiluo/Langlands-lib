/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.EtaleULiftInjectiveResolution
import WeilConjectures.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Positive object cohomology of the associated etale tensor-sections sheaf vanishes
on affine opens.
Source: Stacks Project, Etale Cohomology, Tag 03P2 (affine case), and Cohomology
on Sites, Tag 03F3. https://stacks.math.columbia.edu/tag/03P2
(blueprint: lem-sc-etale-tensor-positive-object-cohomology)

Proof: Fix an affine open U and put j = U.ι. Localization at the etale object j
identifies object cohomology with global cohomology on the small etale site of U.
Restriction of an injective resolution computes this comparison: restriction
along an open immersion preserves injectives because extension by zero is an exact
left adjoint. At v : V -> U, normalized tensor-pullback composition identifies
Gamma(V,(v composed with j)^*F) with Gamma(V,v^*(j^*F)); the unit-normalized
composition law makes these identifications commute with restriction maps.
Thus the restricted sheaf is the tensor-sections sheaf of F restricted to U,
which is quasi-coherent. Affine etale quasi-coherent acyclicity gives zero in
degree n+1. To use the large-coefficient localization comparison, lift the
injective resolution and its evaluation complexes; the coefficient-lift
resolution comparison commutes with evaluation and homology. The lift reflects
zero groups, giving vanishing in the original coefficient universe. The empty
open is affine and the same argument applies. No assertion is made on non-affine
opens: an affine cover gives local vanishing, not global cohomology vanishing. -/
theorem etaleTensorPositiveObjectCohomology
    (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    ∀ U : X.Opens, IsAffineOpen U → IsZero
      (Sheaf.H' (etaleTensorSectionsSheaf F) (n + 1)
        (Scheme.Etale.mk U.ι)) := by
  classical
  intro U hU
  let : IsAffine U.toScheme := hU
  let G := etaleTensorSectionsSheaf F
  let L := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let G' := (sheafCompose X.smallEtaleTopology L).obj G
  let R := injectiveResolution G
  obtain ⟨S, hS⟩ := Scheme.exists_etale_ulift_injectiveResolution X G R
  let T : U.toScheme.Etale := Scheme.Etale.mk (𝟙 U.toScheme)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let A := Etale.upperStar AddCommGrpCat.{u + 1} U.ι
  let ρ := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    U.ι inferInstance
  let : A.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} U.ι)
  let S' : InjectiveResolution (A.obj G') :=
    { cocomplex := (A.mapHomologicalComplex (.up ℕ)).obj S.cocomplex
      injective := fun k ↦ A.injective_obj (S.cocomplex.X k)
      ι := (HomologicalComplex.singleMapHomologicalComplex A (.up ℕ) 0).inv.app G' ≫
        (A.mapHomologicalComplex (.up ℕ)).map S.ι }
  let M := (restrictFunctor U.ι).obj F
  obtain ⟨eM, _⟩ := etaleTensorSectionsSheaf_openIdentification U.ι F
  let eL := (sheafCompose U.toScheme.smallEtaleTopology L).mapIso eM
  let eA : A.obj G' ≅
      (sheafCompose U.toScheme.smallEtaleTopology L).obj (etaleTensorSectionsSheaf M) :=
    ρ.app G' ≪≫ eL
  have hglobal : Subsingleton (Sheaf.H
      ((sheafCompose U.toScheme.smallEtaleTopology L).obj
        (etaleTensorSectionsSheaf M)) (n + 1)) :=
    Etale.etale_affine_qcoherent_ulift U.toScheme M (n + 1) (Nat.zero_lt_succ n)
  let hA := (Sheaf.functorH U.toScheme.smallEtaleTopology (n + 1)).mapIso eA
  have hzA : IsZero (AddCommGrpCat.of (Sheaf.H (A.obj G') (n + 1))) :=
    IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.mpr hglobal) hA
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op (Scheme.Etale.mk U.ι))
  let E' := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.mk U.ι))
  let EU := sheafToPresheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation U.toScheme.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op T)
  obtain ⟨eH⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    U.toScheme.smallEtaleTopology T hT (A.obj G') n
  have hzU : IsZero
      (((EU.mapHomologicalComplex (.up ℕ)).obj S'.cocomplex).homology (n + 1)) :=
    IsZero.of_iso hzA
      (eH.toAddCommGrpIso ≪≫ S'.isoRightDerivedObj EU (n + 1)).symm
  let eEval : ((E'.mapHomologicalComplex (.up ℕ)).obj S.cocomplex) ≅
      ((EU.mapHomologicalComplex (.up ℕ)).obj S'.cocomplex) := by
    have hobj : (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj T =
        Scheme.Etale.mk U.ι := by
      apply MorphismProperty.Comma.ext rfl rfl
      exact heq_of_eq (Category.id_comp U.ι)
    let c : A ⋙ EU ≅ E' :=
      (Functor.isoWhiskerRight ρ EU) ≪≫
        NatIso.ofComponents (fun B ↦ B.obj.mapIso (eqToIso hobj).op) (by
          intro B C f
          exact (f.hom.naturality (eqToHom hobj.symm).op).symm)
    exact ((Functor.mapHomologicalComplexCompIso c (.up ℕ)).app S.cocomplex).symm
  have hzE : IsZero
      (((E'.mapHomologicalComplex (.up ℕ)).obj S.cocomplex).homology (n + 1)) :=
    IsZero.of_iso hzU
      ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso eEval)
  obtain ⟨eS⟩ := hS (Scheme.Etale.mk U.ι)
  have hc := (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso eS
  let hm := ((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).sc (n + 1)
  have ei := (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ L))
    (.up ℕ)).app R.cocomplex
  have hj := (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso ei
  have hl : IsZero
      (L.obj (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))) :=
    IsZero.of_iso hzE (hc ≪≫ hj.symm ≪≫ hm.mapHomologyIso L).symm
  let : Subsingleton (ULift.{u + 1}
      (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hl
  have hsmall : Subsingleton
      (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1)) :=
    Function.Injective.subsingleton (f := fun x ↦
      (ULift.up x : L.obj
        (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))))
      ULift.up_injective
  obtain ⟨e⟩ := objectCohomologyPresheaf_resolution X.smallEtaleTopology G R (n + 1)
  let K := ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).obj R.cocomplex
  let W := (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj
    (op (Scheme.Etale.mk U.ι))
  let ec := (Functor.mapHomologicalComplexCompIso
    (Iso.refl (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙ W))
      (.up ℕ)).app R.cocomplex
  let eW := ((K.sc (n + 1)).mapHomologyIso W).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso ec
  have hobj : Subsingleton ((K.homology (n + 1)).obj (op (Scheme.Etale.mk U.ι))) :=
    @Function.Injective.subsingleton _ _ _ eW.addCommGroupIsoToAddEquiv.injective hsmall
  let he := (e.app (op (Scheme.Etale.mk U.ι))).addCommGroupIsoToAddEquiv
  have htarget : Subsingleton
      ((((K.homology (n + 1)) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (op (Scheme.Etale.mk U.ι)))) :=
    ⟨fun x y ↦ ULift.ext (hobj.elim x.down y.down)⟩
  have hcoh : Subsingleton (ULift.{u + 1}
      (Sheaf.H' G (n + 1) (Scheme.Etale.mk U.ι))) :=
    @Function.Injective.subsingleton _ _ _ he.injective htarget
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact @Function.Injective.subsingleton _ _ _ ULift.up_injective hcoh

end AlgebraicGeometry.Scheme.Modules
