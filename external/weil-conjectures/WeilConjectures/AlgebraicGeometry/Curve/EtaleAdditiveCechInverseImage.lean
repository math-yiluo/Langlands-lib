/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalizedExistence
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalizedScalar
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalizedInverseImage
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.CechInverseImageCochainMap

/-! # Étale additive cohomology in ordinary Čech coordinates

Source: Stacks Project, Tags 03P2 and 01FD.
(blueprint: lem-pbc-etale-additive-cech-inverse-image)
-/

@[expose] public section

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def additiveOrdinaryCechIso
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :
    ((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℕ)).obj (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)) ≅
      (TopCat.Sheaf.cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (SheafOfModules.unit X.ringCatSheaf)) :=
  TopCat.Presheaf.cechComplexFunctorIso U
    (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    (TopCat.Presheaf.cechComplex U).mapIso
      (presheafOverForgetIso X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf))

private noncomputable def additiveOrdinaryCyclesIso
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n) ≅
      ((TopCat.Sheaf.cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (SheafOfModules.unit X.ringCatSheaf))).cycles n :=
  (((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).sc n).mapCyclesIso
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})).symm ≪≫
    HomologicalComplex.cyclesMapIso (additiveOrdinaryCechIso X U) n

private lemma additiveOrdinaryCyclesIso_i
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
    (y : Fin (n + 1) → ι) :
    ((TopCat.Sheaf.cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (SheafOfModules.unit X.ringCatSheaf))).iCycles n
        ((additiveOrdinaryCyclesIso X U n).hom z) y =
      cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) := by
  let K := cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)
  let T := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}
  have hi : (((T.mapHomologicalComplex (.up ℕ)).obj K).iCycles n)
      ((((K.sc n).mapCyclesIso T).inv) z) = K.iCycles n z := by
    have h := (K.sc n).mapCyclesIso_hom_iCycles T
    have h' : ((K.sc n).mapCyclesIso T).inv ≫ ((K.sc n).map T).iCycles =
        T.map (K.iCycles n) := by
      rw [← h, Iso.inv_hom_id_assoc]
      rfl
    exact ConcreteCategory.congr_hom h' z
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (additiveOrdinaryCechIso X U).hom n)
    ((((K.sc n).mapCyclesIso T).inv) z)
  change _ = (additiveOrdinaryCechIso X U).hom.f n
    ((((T.mapHomologicalComplex (.up ℕ)).obj K).iCycles n
      ((((K.sc n).mapCyclesIso T).inv) z))) at h
  rw [hi] at h
  exact congr_fun h y

private lemma exists_additiveOrdinary_cycle_transfer
    {X Y : Scheme.{u}} (g : Y ⟶ X) {ι : Type u}
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l))) (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n) :
    ∃ z' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).cycles n,
      ∀ y : Fin (n + 1) → ι,
        cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
            ((cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') =
          (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
            (homOfLE (hinter n y)).op
            ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
              (op (⨅ l, U (y l)))
              (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z))) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj
    (SheafOfModules.unit X.ringCatSheaf)
  let G := (SheafOfModules.toSheaf Y.ringCatSheaf).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let φ := (SheafOfModules.toSheaf X.ringCatSheaf).map
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
  let A := cechInverseImageCochainMap g U V hinter F G φ.hom
  let w := (additiveOrdinaryCyclesIso X U n).hom z
  let w' := HomologicalComplex.cyclesMap A n w
  let z' := (additiveOrdinaryCyclesIso Y V n).inv w'
  have hz' : (additiveOrdinaryCyclesIso Y V n).hom z' = w' := by
    exact ConcreteCategory.congr_hom (Iso.inv_hom_id (additiveOrdinaryCyclesIso Y V n)) w'
  refine ⟨z', fun y ↦ ?_⟩
  rw [← additiveOrdinaryCyclesIso_i, hz']
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i A n) w
  change ((TopCat.Sheaf.cechComplexFunctor V).obj G).iCycles n w' =
    A.f n (((TopCat.Sheaf.cechComplexFunctor U).obj F).iCycles n w) at hi
  rw [hi]
  change G.obj.map (homOfLE (hinter n y)).op
    (φ.hom.app _ ((((TopCat.Sheaf.cechComplexFunctor U).obj F).iCycles n w) y)) = _
  rw [additiveOrdinaryCyclesIso_i]
  rfl

/-- Affine-intersection Čech coordinates compute lifted additive étale cohomology.
The coordinates respect multiplication and represent inverse-image classes by
matching structural-function cocycles. No ordinary Ext comparison occurs here.

Source: Stacks Project, Tag 03P2, separated-case proof of
etale-cohomology-theorem-zariski-fpqc-quasi-coherent; Tag 01FD,
cohomology-lemma-cech-functorial, augmented double-complex diagram.
(blueprint: lem-pbc-etale-additive-cech-inverse-image)

Proof: Regard the open covers as covers in the small étale sites. The unit module
has canonical structural-function sections, and the fixed additive sheaf is their
coefficient lift. Every tuple intersection is affine. Affine quasi-coherent étale
acyclicity, also with lifted coefficients, makes the coefficient augmentation of
the injective Čech double complex a quasi-isomorphism. The global-sections
augmentation is a quasi-isomorphism by injective Čech acyclicity. Their inverses
on cohomology identify Ext cohomology with the ordered section Čech homology.
Lower every lifted coordinate; structural-function restrictions identify this
complex with cechOver for the unit and the canonical map to Spec of global
functions. In each degree the tuple index is finite. Lowering commutes with these finite
products, kernels, images and alternating differentials.
Multiplication acts coordinatewise, so this identification carries the stipulated
endomorphism to scalar multiplication on homology. For g use the refined-cover
structural pullback map of section complexes. The adjunction unit defining its
étale coefficient map gives precisely structural pullback on each intersection.
Use exists_resolutionSection_canonical_comparison to normalize the resolution
section comparisons on cocycles. The augmented double-complex diagram of 01FD
and resolutionSection_canonical_transfer identify the inverse-image homology map
with exact étale inverse image. Compose with an augmentation-preserving resolution
lift of the adjoint coefficient map; the extMk cocycle formula identifies its
homology map with Sheaf.H.map of that coefficient map. These constructions fix
the edge maps; naturality is not inferred from an arbitrary Nonempty comparison.
Choose a
cycle representing the source class and take its image under this section chain
map as the target cycle. This gives both homology equalities and the displayed
coordinate matching. Degree zero is gluing of sections with structural pullback.
Empty intersections have zero sections; an empty covering index forces both
schemes empty. Neither flatness nor affineness of g is used. -/
theorem exists_etaleAdditive_cech_inverseImage
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    [CompactSpace X] [CompactSpace Y] [X.IsSeparated] [Y.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, V (y l)))
    (hcover : iSup U = ⊤) (hcover' : iSup V = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (μX : Γ(X, ⊤) → (X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf))
    (μY : Γ(Y, ⊤) → (Y.etaleAdditiveSheaf ⟶ Y.etaleAdditiveSheaf))
    (hμX : ∀ r (W : X.Etaleᵒᵖ) (x : X.etaleAdditiveSheaf.obj.obj W),
      (μX r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (hμY : ∀ r (W : Y.Etaleᵒᵖ) (x : Y.etaleAdditiveSheaf.obj.obj W),
      (μY r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (n : ℕ) :
    ∃ a : Sheaf.H X.etaleAdditiveSheaf n ≃+
        (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n,
    ∃ a' : Sheaf.H Y.etaleAdditiveSheaf n ≃+
        (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).homology n,
      (∀ r x, a (Sheaf.H.map (μX r) n x) = r • a x) ∧
      (∀ r x, a' (Sheaf.H.map (μY r) n x) = r • a' x) ∧
      ∀ x,
        ∃ z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n,
        ∃ z' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).cycles n,
          (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z =
            a x ∧
          (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).homologyπ n z' =
            a' (Sheaf.H.map
              (((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
                (Scheme.etaleAdditiveSheafToLowerStar g)) n
              (Etale.cohomologyMap g X.etaleAdditiveSheaf n x)) ∧
          ∀ y : Fin (n + 1) → ι,
            cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
                ((cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') =
              (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
                (homOfLE (hinter n y)).op
                ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
                  (op (⨅ l, U (y l)))
                  (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                    ((cechOver X.toSpecΓ U
                      (SheafOfModules.unit X.ringCatSheaf)).iCycles n z))) := by
  obtain ⟨a, ha⟩ := exists_etaleAdditiveCech_normalized X U hU hcover n
  obtain ⟨a', ha'⟩ := exists_etaleAdditiveCech_normalized Y V hV hcover' n
  refine ⟨a, a', etaleAdditiveCech_normalized_scalar X U hU hcover μX hμX n a ha,
    etaleAdditiveCech_normalized_scalar Y V hV hcover' μY hμY n a' ha', ?_⟩
  intro x
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n)).mp
      inferInstance (a x)
  obtain ⟨z', hcoords⟩ := exists_additiveOrdinary_cycle_transfer g U V hinter n z
  refine ⟨z, z', hz, ?_, hcoords⟩
  have h := etaleAdditiveCech_normalized_inverseImage g U V hU hV hcover hcover'
    hinter n a ha a' ha' z z' hcoords
  simpa only [hz, AddEquiv.symm_apply_apply] using h

end AlgebraicGeometry.Scheme.Modules
