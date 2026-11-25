/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedSupportTriangle

/-!
# Finite duality: comparison for a closed immersion

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph;
Stacks Project, Tags 04CA, 04JC and 014A.
(blueprint: lem-weil-finite-duality-closed-comparison)

The comparison below is formulated with the actual derived direct-image adjunctions.
The isomorphism `δ` is the canonical direct-image comparison of
`lem-weil-pbc-comparison-direct-image-canonical-mate`, transported from its bounded-below
mate along an explicit bounded-below lift by the named Plus/full compatibility isomorphisms.
The transpose formula is the definition of the comparison map `α`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The transpose `α` used in the closed comparison: the `Rₚ ⊣ Iₚ` transpose of
`δ⁻¹` followed by the etale counit.  This is a genuine construction from the two
adjunctions and the named direct-image comparison; no choice or postponed theorem is
used in the definition.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph
(blueprint: lem-weil-finite-duality-closed-comparison). -/
noncomputable def finiteDualityClosedComparisonAlpha
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T U : Scheme.{u}}
    (_i : Z ⟶ T) (_j : U ⟶ T)
    (Rₑ : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Iₑ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Rₚ : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A)))
    (Iₚ : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)))
    (F_T : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A)))
    (F_Z : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)))
    (adjₑ : Rₑ ⊣ Iₑ) (adjₚ : Rₚ ⊣ Iₚ)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (δ : F_T.obj (Rₑ.obj (Iₑ.obj M)) ≅ Rₚ.obj (F_Z.obj (Iₑ.obj M))) :
    F_Z.obj (Iₑ.obj M) ⟶ Iₚ.obj (F_T.obj M) :=
  (adjₚ.homEquiv (F_Z.obj (Iₑ.obj M)) (F_T.obj M))
    (δ.inv ≫ F_T.map (adjₑ.counit.app M))

/-- The canonical component `δ` of the direct-image comparison, transported from the
bounded-below mate `fixedComparisonDirectImageMatePlus`.  The input `e` is the chosen
bounded-below lift of the etale object.  All comparison isomorphisms are the named Plus/full
compatibility isomorphisms, so this is independent of an arbitrary choice of a natural
isomorphism.
Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first paragraph
(blueprint: lem-weil-finite-duality-closed-comparison). -/
noncomputable def finiteDualityClosedComparisonDelta
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    (X : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L) :
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory).obj
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).obj X) ⟶
    ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj X) :=
  let rE := (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility
  let rP := (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusCompatibility
  let fT :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusCompatibility
  let fZ :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlusCompatibility
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).map e.hom ≫ rE.inv.app L) ≫
    fT.inv.app ((Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus.obj L) ≫
    DerivedCategory.Plus.ι.map
      ((ProEtale.fixedComparisonDirectImageMatePlus A i).app L) ≫
    rP.hom.app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
      (fZ.hom.app L ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map e.inv)

set_option backward.isDefEq.respectTransparency false in
/-- The transported canonical closed-comparison component is invertible.

Source: the canonical direct-image mate argument in
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`, first
paragraph (blueprint: lem-weil-finite-duality-closed-comparison).

Proof plan: unfold the transported component and use the qcqs invertibility
of `ProEtale.fixedComparisonDirectImageMatePlus`; the named Plus/full
compatibility isomorphisms and the isomorphism `e` preserve `IsIso` under
composition and functorial mapping.
-/
theorem isIso_finiteDualityClosedComparisonDelta_proof
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [QuasiCompact i] [QuasiSeparated i]
    (X : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : X ≅ DerivedCategory.Plus.ι.obj L) :
    IsIso (finiteDualityClosedComparisonDelta i X L e) := by
  letI := ProEtale.isIso_fixedComparisonDirectImageMatePlus A i
  unfold finiteDualityClosedComparisonDelta
  dsimp -failIfUnchanged only [Etale.rightDerivedLowerStar]
  infer_instance

/- The postponed theorem is registered as an instance directly, so that `asIso` applies
to the canonical component; no further declaration or proof is added. -/
attribute [instance] isIso_finiteDualityClosedComparisonDelta_proof

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
open Etale in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
private theorem closedLowerStar_isLeftAdjoint
    (A : Type (u + 1)) [Ring A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint := by
  let C := ModuleCat.{u + 1} A
  let W : T.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hji : Disjoint (Set.range W.ι.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  let F := lowerStar C i
  let L := upperStar C i
  let J := upperStar C W.ι
  let adj := upperStarLowerStarAdjunction C W.ι
  have : (lowerStar C W.ι).Full :=
    (openImmersionRestrictionLowerStarAdjunction C W.ι).full_R_of_isSplitMono_counit_app
  have : (lowerStar C W.ι).Faithful :=
    (openImmersionRestrictionLowerStarAdjunction C W.ι).faithful_R_of_epi_counit_app
  -- Restriction kills the kernel of its unit.
  let K (N : Sheaf T.smallEtaleTopology C) := kernel (adj.unit.app N)
  have hK (N : Sheaf T.smallEtaleTopology C) : IsZero (J.obj (K N)) := by
    have : IsIso (J.map (adj.unit.app N)) := inferInstance
    exact (isZero_kernel_of_mono (J.map (adj.unit.app N))).of_iso
      (PreservesKernel.iso J (adj.unit.app N))
  let adjI := upperStarLowerStarAdjunction C i
  have hunit (N : Sheaf T.smallEtaleTopology C) : IsIso (adjI.unit.app (K N)) :=
    (adjI.isIso_unit_app_iff_mem_essImage).mpr
      (mem_essImage_lowerStar_of_isZero_upperStar i hij (hK N))
  -- Maps out of a closed pushforward vanish after restriction to the open part.
  have hz (M : Sheaf Z.smallEtaleTopology C) (N : Sheaf T.smallEtaleTopology C)
      (f : F.obj M ⟶ N) : f ≫ adj.unit.app N = 0 := by
    apply (adj.homEquiv (F.obj M) (J.obj N)).symm.injective
    exact (isZero_upperStar_lowerStar_of_disjoint_range C W.ι i hji M).eq_of_src _ _
  -- Factor through the kernel, identify it with a closed pushforward, then use fullness.
  let e (M : Sheaf Z.smallEtaleTopology C) (N : Sheaf T.smallEtaleTopology C) :
      (F.obj M ⟶ N) ≃ (M ⟶ L.obj (K N)) :=
    { toFun := fun f ↦ F.preimage
        (kernel.lift (adj.unit.app N) f (hz M N f) ≫ adjI.unit.app (K N))
      invFun := fun g ↦ F.map g ≫ inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N)
      left_inv := by
        intro f
        simp
      right_inv := by
        intro g
        apply F.map_injective
        simp only [Functor.map_preimage]
        rw [← cancel_mono (inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N))]
        simp }
  have he : ∀ M' M N f g, e M' N (F.map f ≫ g) = f ≫ e M N g := by
    intro M' M N f g
    apply F.map_injective
    simp only [Functor.map_comp]
    apply (cancel_mono (inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N))).1
    simp [e]
  exact (Adjunction.adjunctionOfEquivRight e he).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
private theorem closedRightAdjoint_boundedBelow
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.TStructure.t.plus M) :
    letI : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
    ∃ L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Nonempty ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint.obj M ≅
        DerivedCategory.Plus.ι.obj L) := by
  letI : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A i
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) i
  letI : F.IsLeftAdjoint := closedLowerStar_isLeftAdjoint A i
  let adj := Adjunction.ofIsLeftAdjoint F
  letI : F.rightAdjoint.Additive := adj.right_adjoint_additive
  let adjD := adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    F.rightDerivedFunctorIsoMapDerivedCategory.symm
  let e := (Adjunction.ofIsLeftAdjoint F.rightDerivedFunctor).rightAdjointUniq adjD
  let Mplus : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨M, hM⟩
  exact ⟨F.rightAdjoint.rightDerivedFunctorPlus.obj Mplus,
    ⟨e.app M ≪≫ (F.rightAdjoint.rightDerivedFunctorPlusCompatibility.app Mplus).symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
private theorem closedComparisonAlpha_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    [hRE : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint]
    [QuasiCompact i] [QuasiSeparated i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint.obj M ≅
      DerivedCategory.Plus.ι.obj L)
    [hδ : IsIso (finiteDualityClosedComparisonDelta i _ L e)] :
    IsIso (finiteDualityClosedComparisonAlpha i j
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i)
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).rightAdjoint
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor
      (ProEtale.closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctor
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
      (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i))
      (ProEtale.derivedLowerStarClosedUpperShriekAdjunction i j hij) M
      (asIso (finiteDualityClosedComparisonDelta i _ L e))) := by
  let C := ModuleCat.{u + 1} A
  let RE := Etale.rightDerivedLowerStar C i
  let RP := (ProEtale.lowerStar C i).rightDerivedFunctor
  let IP := (ProEtale.closedUpperShriek C i j).rightDerivedFunctor
  let FT := (ProEtale.comparisonUpperStar C T).mapDerivedCategory
  let adjE := Adjunction.ofIsLeftAdjoint RE
  let adjP := ProEtale.derivedLowerStarClosedUpperShriekAdjunction (R := A) i j hij
  let JP := (ProEtale.upperStar C j).mapDerivedCategory
  let GP := (ProEtale.lowerStar C j).rightDerivedFunctor
  let adjj := (ProEtale.upperStarLowerStarAdjunction C j
    ).mapDerivedCategoryRightDerivedAdjunction
  letI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  have hz (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C)) :
      IsZero (JP.obj (RP.obj P)) := by
    have hz' : IsZero (JP.obj ((ProEtale.lowerStar C i).mapDerivedCategory.obj P)) :=
      (Functor.isZero_mapDerivedCategory_obj (ProEtale.lowerStar C i ⋙
        ProEtale.upperStar C j) P
        (fun n ↦ ProEtale.isZero_upperStar_lowerStar_of_disjoint C i j hij.disjoint
          ((DerivedCategory.homologyFunctor _ n).obj P))).of_iso
          (((ProEtale.lowerStar C i).mapDerivedCategoryCompIso
            (ProEtale.upperStar C j)).app P)
    exact hz'.of_iso (JP.mapIso
      ((ProEtale.lowerStar C i).rightDerivedFunctorIsoMapDerivedCategory.app P))
  have hkill (N : DerivedCategory (Sheaf (Scheme.ProEt.topology U) C)) :
      IsZero (IP.obj (GP.obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (adjP.homEquiv _ _).symm.injective
    letI : Subsingleton (JP.obj (RP.obj (IP.obj (GP.obj N))) ⟶ N) :=
      ⟨fun f g ↦ (hz _).eq_of_src f g⟩
    haveI : Subsingleton (RP.obj (IP.obj (GP.obj N)) ⟶ GP.obj N) :=
      (adjj.homEquiv (RP.obj (IP.obj (GP.obj N))) N).symm.subsingleton
    exact Subsingleton.elim _ _
  let JE := (Etale.upperStar C j).mapDerivedCategory
  let GE := Etale.rightDerivedLowerStar C j
  let Mplus : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C) := ⟨M, hM⟩
  let Lopen := (Etale.upperStar C j).mapDerivedCategoryPlus.obj Mplus
  let eopen : JE.obj M ≅ DerivedCategory.Plus.ι.obj Lopen :=
    ((Etale.upperStar C j).mapDerivedCategoryPlusCompatibility.app Mplus).symm
  have hopen : IsZero (IP.obj (FT.obj (GE.obj (JE.obj M)))) :=
    (hkill _).of_iso (IP.mapIso
      (asIso (finiteDualityClosedComparisonDelta j (JE.obj M) Lopen eopen)))
  obtain ⟨w, hw⟩ := Etale.exists_etale_closedSupportTriangle A i j hij.eq_compl
  have hdist := IP.map_distinguished _ (FT.map_distinguished _ (hw M))
  have hc : IsIso (IP.map (FT.map (adjE.counit.app M))) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hdist).1 hopen
  unfold finiteDualityClosedComparisonAlpha
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  infer_instance

/-!
The closed finite-duality comparison.  The hypotheses on the structure morphisms record
the finite-type, separated finite-field setting of the source; the bounded-below lift is
the first clause of the conclusion, and `δ` is the named canonical direct-image comparison.
-/
end AlgebraicGeometry
