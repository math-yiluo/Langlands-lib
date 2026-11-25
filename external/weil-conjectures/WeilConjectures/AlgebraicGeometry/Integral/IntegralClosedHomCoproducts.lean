/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedCostalkCoproducts
import WeilConjectures.CategoryTheory.Integral.IntegralStratumProjectionInternalHom
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteEquivalenceHomTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedTensorProjection
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Closed support preserves bounded internal-Hom coproduct continuity

## References

* Bhatt--Scholze, Lemma 6.3.14(4)
* Stacks Tag 09BM
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

-- The unbounded derived comparisons require elaborating several functor structures.
set_option synthInstance.maxSize 4096 in
/-- Closed direct image carries a source whose internal Hom preserves colimits to a
source whose internal Hom preserves uniformly bounded-below sums. -/
theorem integralClosed_homPreservesCoproduct
    {T Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (i : Z ⟶ T) [IsClosedImmersion i]
    (P : DerivedCategory (pbcModules Z (pbcAdicCompletion Z d)))
    (hP : PreservesColimitsOfSize.{u + 1, u + 1}
      (RingedHomUniverses.hom.{u + 1, u, u + 1}
        (ProEt.topology Z) (pbcAdicCompletion Z d) P))
    (I : Type (u + 1))
    (N : I → DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (b : ℤ) (hN : ∀ s, (N s).IsGE b) :
    PreservesColimit (Discrete.functor N)
      (RingedHomUniverses.hom.{u + 1, u, u + 1}
        (ProEt.topology T) (pbcAdicCompletion T d) ((d.push i).obj P)) := by
  classical
  let R := pbcAdicCompletion T d
  let S := pbcAdicCompletion Z d
  let RZ := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let W : T.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let V := ProEt.mk W.ι
  have : IsOpenImmersion V.hom := inferInstanceAs (IsOpenImmersion W.ι)
  let : TopologicalSpace.NoetherianSpace V.left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (W : Set T))
  have : QuasiCompact V.hom :=
    ⟨fun B _ _ ↦ @TopologicalSpace.NoetherianSpace.isCompact V.left _
      (inferInstance : TopologicalSpace.NoetherianSpace V.left) (V.hom ⁻¹' B)⟩
  have hv : Set.range V.hom = (Set.range i)ᶜ := W.range_ι
  obtain ⟨ai, h1⟩ := proEtale_ringed_closed_kernel_adjoint i V hv R
  obtain ⟨aj, h2⟩ := h1
  obtain ⟨hai, h3⟩ := h2
  obtain ⟨haj, h4⟩ := h3
  obtain ⟨hqi, h5⟩ := h4
  obtain ⟨hqj, h6⟩ := h5
  obtain ⟨hli, h7⟩ := h6
  obtain ⟨hci, h8⟩ := h7
  obtain ⟨hlj, h9⟩ := h8
  obtain ⟨hcj, h10⟩ := h9
  obtain ⟨hlqi, h11⟩ := h10
  obtain ⟨hcqi, h12⟩ := h11
  obtain ⟨hH, h13⟩ := h12
  obtain ⟨a0, h14⟩ := h13
  obtain ⟨_, h15⟩ := h14
  obtain ⟨_, h16⟩ := h15
  obtain ⟨_, h17⟩ := h16
  obtain ⟨_, h18⟩ := h17
  obtain ⟨_, h19⟩ := h18
  obtain ⟨_, h20⟩ := h19
  obtain ⟨_, h21⟩ := h20
  obtain ⟨_, h22⟩ := h21
  obtain ⟨_, h23⟩ := h22
  obtain ⟨_, h24⟩ := h23
  obtain ⟨_, h25⟩ := h24
  obtain ⟨d0, h26⟩ := h25
  obtain ⟨di, h27⟩ := h26
  obtain ⟨_, h28⟩ := h27
  let := hai
  let := haj
  let := hqi
  let := hqj
  let := hli
  let := hci
  let := hlj
  let := hcj
  let := hlqi
  let := hcqi
  let := hH
  let G := (ringedClosedKernelShriek i V.hom R aj).rightDerivedFunctor
  let qi := proEtaleRingedDirectImage i R
  let pi := proEtaleModuleInverseImage i R
  let qiA := proEtaleRingModuleDirectImage i R RZ (Iso.refl _)
  let piA := proEtaleRingModulePullback i R RZ (Iso.refl _)
  have : PreservesFiniteLimits qiA := by
    dsimp only [qiA]
    rw [push_eq]
    infer_instance
  have : PreservesFiniteColimits qiA := by
    dsimp only [qiA]
    rw [push_eq]
    infer_instance
  let ep : qiA.rightDerivedFunctor ≅ qi.mapDerivedCategory :=
    qiA.rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso (eqToIso (push_eq i R))
  let ei : piA.mapDerivedCategory ≅ pi.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso (inverseIso i R)
  let ac : qiA.rightDerivedFunctor ⊣ G := d0.ofNatIsoLeft ep.symm
  let ap : piA.mapDerivedCategory ⊣ qiA.rightDerivedFunctor :=
    (di.ofNatIsoLeft ei.symm).ofNatIsoRight ep.symm
  let c := d.integralRingIso i
  let a := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let E := CategoryTheory.NativeRestriction.scalarEquivalence a
  have : E.functor.Additive :=
    inferInstanceAs (SheafOfModules.restrictScalars a.hom).Additive
  let Q := E.mapDerivedCategory
  obtain ⟨δ, hδ⟩ := CategoryTheory.NativeRestriction.scalarIso_internalHom.{
    u + 1, u, u + 1} S RZ c
  obtain ⟨γc⟩ := CategoryTheory.NativeRestriction.homComplex_transport.{
    u + 1, u + 1, u, u, u + 1} S RZ E.functor δ hδ
  obtain ⟨γ⟩ := CategoryTheory.NativeRestriction.derivedHom_transport.{
    u + 1, u + 1, u, u, u + 1, u + 2, u + 2} S RZ E γc
  let H := RingedHomUniverses.hom.{u + 1, u, u + 1} (ProEt.topology Z) S P
  let HZ := RingedHomUniverses.hom.{u + 1, u, u + 1}
    (ProEt.topology Z) RZ (Q.functor.obj P)
  let hq : H ⋙ Q.functor ≅ Q.functor ⋙ HZ :=
    NatIso.ofComponents (fun M ↦ γ.app (op P, M)) (by
      intro M M' f
      have hn := γ.hom.naturality ((𝟙 (op P), f) : (op P, M) ⟶ (op P, M'))
      change Q.functor.map
          ((derivedInternalHomOfUniverses.{u + 1, u, u + 1}
            (ProEt.topology Z) S).map (𝟙 (op P), f)) ≫ γ.hom.app (op P, M') =
        γ.hom.app (op P, M) ≫
          (derivedInternalHomOfUniverses.{u + 1, u, u + 1}
            (ProEt.topology Z) RZ).map
              ((Q.functor.op.map (𝟙 (op P)), Q.functor.map f) :
                (op (Q.functor.obj P), Q.functor.obj M) ⟶
                  (op (Q.functor.obj P), Q.functor.obj M')) at hn
      rw [Q.functor.op.map_id] at hn
      exact hn)
  let hr : HZ ≅ Q.inverse ⋙ H ⋙ Q.functor :=
    (Functor.leftUnitor HZ).symm ≪≫
      Functor.isoWhiskerRight Q.counitIso.symm HZ ≪≫
      Functor.isoWhiskerLeft Q.inverse hq.symm
  have : PreservesColimitsOfSize.{u + 1, u + 1} H := hP
  have : PreservesColimitsOfSize.{u + 1, u + 1} HZ :=
    preservesColimits_of_natIso hr.symm
  have : PreservesColimitsOfSize.{u + 1, u + 1} qi.mapDerivedCategory :=
    d0.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u + 1, u + 1} qiA.rightDerivedFunctor :=
    preservesColimits_of_natIso ep.symm
  have : PreservesColimit (Discrete.functor N) G :=
    proEtaleClosedCostalk_preservesCoproduct i R G d0 I N b hN
  obtain ⟨⟨m, tadj, ev⟩, hm, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} (ProEt.topology T) R
  dsimp only [CoefficientClosedStructure.monoidal] at hm
  subst m
  obtain ⟨⟨mz, zadj, zev⟩, hmz, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ
  dsimp only [CoefficientClosedStructure.monoidal] at hmz
  subst mz
  let CT : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology T) R) :=
    ⟨RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology T) R, tadj, ev⟩
  let CZ : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ) :=
    ⟨RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ, zadj, zev⟩
  obtain ⟨φ⟩ := proEtaleClosedTensorProjection i V.hom hv R
  obtain ⟨eh⟩ := internalHom_of_tensorProjection CT CZ
    (RingedDerivedNative.symmetric.{u + 1, u, 0, u + 2} (ProEt.topology T) R)
    (RingedDerivedNative.symmetric.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ)
    qiA.rightDerivedFunctor piA.mapDerivedCategory G qiA.rightDerivedFunctor ac ap
    φ.symm (Q.functor.obj P)
  let eh' : RingedHomUniverses.hom.{u + 1, u, u + 1} (ProEt.topology T) R
      (qiA.rightDerivedFunctor.obj (Q.functor.obj P)) ≅
        G ⋙ HZ ⋙ qiA.rightDerivedFunctor := eh
  have : PreservesColimit (Discrete.functor N) (G ⋙ HZ ⋙ qiA.rightDerivedFunctor) :=
    inferInstance
  have : PreservesColimit (Discrete.functor N)
      (RingedHomUniverses.hom.{u + 1, u, u + 1} (ProEt.topology T) R
        (qiA.rightDerivedFunctor.obj (Q.functor.obj P))) :=
    preservesColimit_of_natIso (Discrete.functor N) eh'.symm
  let F := proEtaleRingModuleDirectImage i R S c
  let ε : F ≅ E.functor ⋙ qi :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)))
      (by intro M M' f; ext X x; rfl)
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso ε.symm
  have : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso ε.symm
  let eP : (d.push i).obj P ≅ qiA.rightDerivedFunctor.obj (Q.functor.obj P) :=
    F.rightDerivedFunctorIsoMapDerivedCategory.app P ≪≫
      (Functor.mapDerivedCategoryNatIso ε).app P ≪≫
      (Functor.mapDerivedCategoryCompIso E.functor qi).symm.app P ≪≫
      ep.symm.app (Q.functor.obj P)
  exact preservesColimit_of_natIso (Discrete.functor N)
    ((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology T) R)).mapIso eP.op)

end AlgebraicGeometry.Scheme
