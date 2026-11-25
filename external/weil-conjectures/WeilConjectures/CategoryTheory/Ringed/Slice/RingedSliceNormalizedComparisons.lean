/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceTotalTensorComparison
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceHomComparisonExistence
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorKoszulExistence
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
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
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
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
import Mathlib.CategoryTheory.Localization.Prod

/-! # Existence of normalized slice comparisons

Source: Stacks Project, Tags 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-normalized-comparisons).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local irreducible] ringedSliceDerivedRestriction ringedSliceLocalizationIso
  coefficientTotalTensor CoefficientClosedStructure.tensor
  CochainComplex.IsKFlatIndependentCoefficients

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

/-- The generic preimage equation avoids unfolding a concrete comparison isomorphism. -/
private theorem whisker_preimageIso {B D E : Type*}
    [Category* B] [Category* D] [Category* E] (L : B ⥤ D)
    (FF : ((Functor.whiskeringLeft B D E).obj L).FullyFaithful)
    {G H : D ⥤ E} (e : L ⋙ G ≅ L ⋙ H) :
    Functor.isoWhiskerLeft L (FF.preimageIso e) = e := by
  apply Iso.ext
  exact FF.map_preimage e.hom

/-- Cancel the two changes of representatives in an abstract tensor square. -/
private theorem normalized_tensor_square {D E : Type*} [Category* D] [Category* E]
    (r : D ⥤ E) (F : E × E ⥤ E) {X Y : D} {U U' V V' : E}
    (t : X ≅ Y) (b : U ≅ U') (c : V ≅ V')
    (g : r.obj X ⟶ F.obj (U', V')) (q : r.obj Y ⟶ F.obj (U, V))
    (h : q = r.map t.inv ≫ g ≫ F.map (b.inv, c.inv)) :
    r.map t.hom ≫ q ≫ F.map (b.hom, c.hom) = g := by
  rw [h]
  simp only [← Category.assoc, ← r.map_comp, Iso.hom_inv_id,
    r.map_id, Category.id_comp]
  simp only [Category.assoc, ← F.map_comp, prod_comp, Iso.inv_hom_id,
    ← prod_id', F.map_id, Category.comp_id]

attribute [local irreducible] Localization.fullyFaithfulWhiskeringLeft
  Functor.FullyFaithful.preimageIso

private def comparisonData
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    (H : Dᵒᵖ × D ⥤ D) (HU : Eᵒᵖ × E ⥤ E) (r : D ⥤ E)
    (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
    (K : Prop) (hK : K)
    (ρ : S.tensor ⋙ r ≅ (r.prod r) ⋙ SU.tensor)
    (η : H ⋙ r ≅ (r.op.prod r) ⋙ HU)
    (σ : S.tensor ≅ (Prod.swap _ _) ⋙ S.tensor)
    (σU : SU.tensor ≅ (Prod.swap _ _) ⋙ SU.tensor) :
    RingedSliceEvaluationComparisons H HU r S SU K :=
  { rho := fun L N ↦ ρ.app (L, N)
    eta := fun L N ↦ η.app (op L, N)
    rho_naturality := fun L N L' N' f g ↦ ρ.hom.naturality
      (X := (L, N)) (Y := (L', N')) (f, g)
    eta_naturality := fun L N L' N' f g ↦ η.hom.naturality
      (X := (op L, N)) (Y := (op L', N')) (f.op, g)
    sigma := fun L N ↦ σ.app (L, N)
    sigma_naturality := fun L N L' N' f g ↦ σ.hom.naturality
      (X := (L, N)) (Y := (L', N')) (f, g)
    sigmaU := fun L N ↦ σU.app (L, N)
    sigmaU_naturality := fun L N L' N' f g ↦ σU.hom.naturality
      (X := (L, N)) (Y := (L', N')) (f, g)
    kflat := hK }

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The normalized tensor, Hom and Koszul comparisons for exact slice restriction exist.
Source: Stacks Project, Tags 07A4, 08JB, 03EL and the total-complex Koszul exchange
(blueprint: lem-weil-pbc-ringed-slice-normalized-comparisons).

Proof: restriction preserves K-flat complexes by 0E8K. Flatness restricts by the
local equational criterion. On a pair of such complexes, restrict each tensor summand using 03EL,
which sends x tensor y to x tensor y. Restriction commutes with sheafification and
coproducts, so these summand maps form a natural chain isomorphism of total complexes.
The K-flat presentation of the derived category descends it to rho and gives its
specified representative square. For Hom, use a K-injective representative I of the
target. Relocalization identifies the local families L^p to I^(p+n) on both sides;
the differentials d_I h - (-1)^n h d_L coincide. Restriction preserves K-injectivity,
so localization gives eta with its two-variable naturality. The augmentation to the
fixed K-injective replacement determines the isomorphisms kappa and kappa_U uniquely,
and naturality of augmentation gives the required Hom square. Finally exchange the
summands of total tensor with the sign (-1)^(pq). Its chain-map identity follows from
the total differential, and its inverse is the reverse signed exchange. Localizing
on K-flat representatives gives the two natural symmetry families, on the original
and the slice sites. Their model squares hold by construction. These four constructions
give all fields of the comparison datum and all four normalization predicates. -/
theorem ringedSlice_normalizedComparisons
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU) :
    Nonempty {d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U) // RingedSliceEvaluationNormalized.{c, v, u, w, w'} J A U S T SU TU d} := by
  let R := ringedSliceComplexRestriction.{c, v, u} J A U
  let r := ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U
  let α := ringedSliceLocalizationIso.{c, v, u, w, w'} J A U
  have hk (P : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J A) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P) :
      CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := A.over U)
        (R.obj P) :=
    (SheafOfModules.ringedSite_restriction_exact_kflat.{c, v, u} J A U).2.2 P hP
  have hflat : RingedSliceFlatRestriction.{c, v, u} J A U := by
    intro P hP fP
    refine ⟨hk P hP, ?_⟩
    intro n
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion
      (A.over U) ((P.X n).over U)).2
    intro V m a s hs
    obtain ⟨Z, hZ, h⟩ :=
      (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion A (P.X n)).1
        (fP n) V.left m a s hs
    refine ⟨(Sieve.overEquiv V).symm Z, ?_, ?_⟩
    · exact (J.mem_over_iff _).2 (by simpa using hZ)
    · intro W f hf
      exact h W.left f.left hf
  obtain ⟨γ, hγ⟩ := ringedSlice_totalTensorComparison_exists.{c, v, u} J A U
  let K := coefficientKFlatInclusion.{u, c, v} J A
  let KU := coefficientKFlatInclusion.{u, max c v, v} (J.over U) (A.over U)
  let F := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := J.over U) (R := A.over U)) (K ⋙ R) (fun P ↦ hk P.obj P.property)
  let L := K ⋙ DerivedCategory.Q.{w}
  let LU := KU ⋙ DerivedCategory.Q.{w'}
  let W := (HomologicalComplex.quasiIso (RingedDerivedNative.Modules.{c, v, u} J A)
    (.up ℤ)).inverseImage K
  have : L.IsLocalization W := RingedDerivedNative.kFlatLocalization.{c, v, u, w} J A
  let a : L ⋙ r ≅ F ⋙ LU := Functor.isoWhiskerLeft K α
  let e₀ : (L.prod L) ⋙ (S.tensor ⋙ r) ≅
      (L.prod L) ⋙ (r.prod r ⋙ SU.tensor) :=
    Functor.isoWhiskerRight T.comparison.symm r ≪≫
      Functor.isoWhiskerLeft ((K.prod K) ⋙ coefficientTotalTensor.{u, c, v} J A) α ≪≫
      Functor.isoWhiskerLeft (K.prod K) (Functor.isoWhiskerRight γ DerivedCategory.Q) ≪≫
      Functor.isoWhiskerLeft (F.prod F) TU.comparison ≪≫
      (Functor.isoWhiskerRight (NatIso.prod a a) SU.tensor).symm
  let FF := Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W)
    (DerivedCategory (RingedDerivedNative.Modules.{max c v, v, u} (J.over U) (A.over U)))
  let ρ : S.tensor ⋙ r ≅ r.prod r ⋙ SU.tensor :=
    FF.preimageIso (X := S.tensor ⋙ r) (Y := r.prod r ⋙ SU.tensor) e₀
  have hρ : Functor.isoWhiskerLeft (L.prod L) ρ = e₀ :=
    whisker_preimageIso (L.prod L) FF e₀
  obtain ⟨η, hη⟩ := ringedSlice_homComparison_exists.{c, v, u, w, w'} J A U
  obtain ⟨σ, hσ⟩ := ringedTensor_koszul_exists.{c, v, u, w} J A S T
  obtain ⟨σU, hσU⟩ := ringedTensor_koszul_exists.{max c v, v, u, w'}
    (J.over U) (A.over U) SU TU
  let d := comparisonData
    (derivedInternalHomOfUniverses.{c, v, u, w} J A)
    (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
    r S SU (RingedSliceFlatRestriction.{c, v, u} J A U) hflat ρ η σ σU
  refine ⟨⟨d, ?_⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ fP fQ
    refine ⟨γ.app (P, Q), hγ P Q, ?_⟩
    have he := congrArg (fun i ↦ i.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) hρ
    change ρ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      r.map (T.iso J A S P Q hP hQ).inv ≫
        α.hom.app ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≫
        DerivedCategory.Q.map (γ.hom.app (P, Q)) ≫
        (TU.iso (J.over U) (A.over U) SU (R.obj P) (R.obj Q)
          (hk P hP) (hk Q hQ)).hom ≫
        SU.tensor.map
          (X := (DerivedCategory.Q.{w'}.obj (R.obj P),
            DerivedCategory.Q.{w'}.obj (R.obj Q)))
          (Y := (r.obj (DerivedCategory.Q.{w}.obj P), r.obj (DerivedCategory.Q.{w}.obj Q)))
          (α.inv.app P, α.inv.app Q) at he
    change r.map (T.iso J A S P Q hP hQ).hom ≫
      ρ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SU.tensor.map
          (X := (r.obj (DerivedCategory.Q.{w}.obj P), r.obj (DerivedCategory.Q.{w}.obj Q)))
          (Y := (DerivedCategory.Q.{w'}.obj (R.obj P),
            DerivedCategory.Q.{w'}.obj (R.obj Q)))
          (α.hom.app P, α.hom.app Q) = _
    exact normalized_tensor_square r SU.tensor (T.iso J A S P Q hP hQ)
      (α.app P) (α.app Q)
      (α.hom.app ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≫
        DerivedCategory.Q.map (γ.hom.app (P, Q)) ≫
        (TU.iso (J.over U) (A.over U) SU (R.obj P) (R.obj Q)
          (hk P hP) (hk Q hQ)).hom)
      (ρ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
      (by simpa only [Category.assoc, Iso.app_inv, Functor.comp_obj, Functor.prod_obj]
        using he)
  · exact hη
  · exact hσ
  · exact hσU

end CategoryTheory
