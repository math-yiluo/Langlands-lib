/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Data.Matrix.Mul
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.SixFunctors.ConstructibleOpenClosedRefinement
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedDetection
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.Monoidal.EndTensorUnit
import WeilConjectures.CategoryTheory.Preadditive.FinitePowerPivot
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Direct finiteness of constructible condensed coefficient complexes

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence.
The finiteness argument is the agent-formulated ingredient recorded in the DAG.
(blueprint: lem-sf-condensed-constructible-direct-finiteness).

The ordinary derived category is taken of internal module objects over the pulled-back
coefficient ring; no completion condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem finiteFree_direct_finiteness
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [HasFiniteBiproducts C] (n : ℕ)
    (a b : (⨁ fun _ : Fin n ↦ 𝟙_ C) ⟶ ⨁ fun _ : Fin n ↦ 𝟙_ C)
    (hab : a ≫ b = 𝟙 _) : b ≫ a = 𝟙 _ := by
  classical
  have hm : biproductFinMatrix b * biproductFinMatrix a = 1 := by
    rw [← biproductFinMatrix_comp, hab, biproductFinMatrix_id]
  have hm' : biproductFinMatrix (b ≫ a) = biproductFinMatrix (𝟙 _) := by
    rw [biproductFinMatrix_comp, biproductFinMatrix_id]
    exact mul_eq_one_comm.mp hm
  apply biproduct_fin_hom_ext
  intro i j
  exact congrArg End.asHom (congrFun (congrFun hm' i) j)

private theorem isIso_of_iso_finiteFree
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [HasFiniteBiproducts C] {M : C} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ 𝟙_ C) (a b : M ⟶ M)
    (hab : a ≫ b = 𝟙 M) : IsIso a := by
  let c := e.inv ≫ a ≫ e.hom
  let d := e.inv ≫ b ≫ e.hom
  have hcd : c ≫ d = 𝟙 _ := by
    simp only [c, d, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc a b e.hom, hab]
    simp
  have hdc : d ≫ c = 𝟙 _ := finiteFree_direct_finiteness n c d hcd
  have hrev : b ≫ a = 𝟙 _ := by
    have h := congrArg (fun z ↦ e.hom ≫ z ≫ e.inv) hdc
    simpa only [c, d, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id] using h
  exact ⟨⟨b, hab, hrev⟩⟩

private theorem module_isIso_of_iso_finiteFree
    {C : Type*} [Category C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [BraidedCategory C]
    [∀ T : C, PreservesColimitsOfSize.{0, 0} (tensorLeft T)]
    [∀ T : C, PreservesColimitsOfSize.{0, 0} (tensorRight T)]
    (R : C) [MonObj R] [IsCommMonObj R] {M : Mod C R} {n : ℕ}
    (e : M ≅ Mod.finiteFree R n) (a b : M ⟶ M) (hab : a ≫ b = 𝟙 M) : IsIso a := by
  exact isIso_of_iso_finiteFree e a b hab

private theorem underlying_pullback_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) [IsIso ((CondensedRing.upperStar Λ g).map f)] :
    IsIso ((upperStar Ab.{u + 1} g).map f.hom) := by
  let e := Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} g).mapMod
    (condensedRingObj Λ X)) (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g))
  have hf : IsIso ((CondensedRing.upperStar Λ g).map f) := inferInstance
  change IsIso ((((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ X)) ⋙
    Mod.extendScalars (condensedPullbackHom Λ g)).map f) at hf
  have h : IsIso ((((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ X)) ⋙
      Mod.comap (inv (condensedPullbackHom Λ g))).map f) :=
    (NatIso.isIso_map_iff e f).mp hf
  exact inferInstanceAs (IsIso ((Mod.forget _).map
    ((((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ X)) ⋙
      Mod.comap (inv (condensedPullbackHom Λ g))).map f)))

private theorem cover_direct_finiteness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h𝒲 : ∀ i : 𝒲.I₀, ∃ n : ℕ, Nonempty
      ((CondensedRing.upperStar Λ (𝒲.f i)).obj M ≅
        Mod.finiteFree (condensedRingObj Λ (𝒲.X i)) n))
    (a b : M ⟶ M) (hab : a ≫ b = 𝟙 M) : IsIso a := by
  classical
  have (i : 𝒲.I₀) : WeaklyEtale (𝒲.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒲.mem₀ (.mk i)
  suffices IsIso ((Mod.forget _).map a) from isIso_of_reflects_iso a (Mod.forget _)
  change IsIso a.hom
  refine isIso_of_isIso_localizationRestriction Ab.{u + 1} a.hom 𝒲.f 𝒲.mem₀ ?_
  intro i
  obtain ⟨n, ⟨e⟩⟩ := h𝒲 i
  let F := CondensedRing.upperStar Λ (𝒲.f i)
  have : IsIso (F.map a) := module_isIso_of_iso_finiteFree _ e (F.map a) (F.map b)
    (by rw [← F.map_comp, hab, F.map_id])
  have : IsIso ((upperStar Ab.{u + 1} (𝒲.f i)).map a.hom) :=
    underlying_pullback_isIso Λ (𝒲.f i) a
  exact (NatIso.isIso_map_iff
    (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒲.f i) inferInstance) a.hom).mp this

private theorem locallyFiniteFree_direct_finiteness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒲.I₀,
      ∃ n : ℕ, Nonempty ((CondensedRing.upperStar Λ (𝒲.f i)).obj M ≅
        Mod.finiteFree (condensedRingObj Λ (𝒲.X i)) n))
    (a b : M ⟶ M) (hab : a ≫ b = 𝟙 M) : IsIso a := by
  obtain ⟨𝒲, h𝒲⟩ := hM
  exact cover_direct_finiteness Λ X M 𝒲 h𝒲 a b hab

attribute [local irreducible] Profinite.padicAlgClCondensedRing

private theorem lfp_direct_finiteness (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
    (hM : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) M)
    (a b : M ⟶ M) (hab : a ≫ b = 𝟙 M) : IsIso a := by
  exact locallyFiniteFree_direct_finiteness (Profinite.padicAlgClRingObj.{u} ℓ) X M
    (condensedQbar_lfp_locally_free ℓ X M hM) a b hab

private theorem localModel_direct_finiteness (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
    (hM : HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj.{u} ℓ) X M)
    (a b : M ⟶ M) (hab : a ≫ b = 𝟙 M) : IsIso a := by
  exact lfp_direct_finiteness ℓ X M
    (HasFiniteConstantLocalModel.isLocallyFinitelyPresented
      (Profinite.padicAlgClRingObj.{u} ℓ) M hM) a b hab

private theorem stratified_direct_finiteness (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X M)
    (a b : M ⟶ M) (hab : a ≫ b = 𝟙 M) : IsIso a := by
  classical
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  have : IsNoetherian X := ⟨⟩
  have hM' : IsFiniteConstantStratified Λ X M := by
    simpa only [IsConstantModelConstructible, ite_eq_left
      (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩)]
      using hM
  obtain ⟨S, hS⟩ := hM'
  have (i : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain i) :=
    (S.immersion i).isEmbedding.isInducing.noetherianSpace
  have (i : Fin S.n) : QuasiCompact (S.immersion i) := inferInstance
  have hcover : ∀ x : X, ∃ i, x ∈ Set.range (S.immersion i) := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨i, (S.range_immersion i).symm ▸ hi⟩
  have hiso (i : Fin S.n) : IsIso ((upperStar Ab.{u + 1} (S.immersion i)).map a.hom) := by
    let F := CondensedRing.upperStar Λ (S.immersion i)
    have : IsIso (F.map a) := localModel_direct_finiteness ℓ (S.domain i) (F.obj M)
      (hS i) (F.map a) (F.map b) (by rw [← F.map_comp, hab, F.map_id])
    exact underlying_pullback_isIso Λ (S.immersion i) a
  have detect (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (hF : ∀ i, IsZero ((upperStar Ab.{u + 1} (S.immersion i)).obj F)) : IsZero F := by
    rw [IsZero.iff_id_eq_zero]
    apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion hcover
    intro i
    rw [CategoryTheory.Functor.map_id]
    exact (hF i).eq_of_src _ _
  have hker : IsZero (kernel a.hom) := detect _ (fun i ↦
    (isZero_kernel_of_mono ((upperStar Ab.{u + 1} (S.immersion i)).map a.hom)).of_iso
      (PreservesKernel.iso (upperStar Ab.{u + 1} (S.immersion i)) a.hom))
  have hcoker : IsZero (cokernel a.hom) := detect _ (fun i ↦
    (isZero_cokernel_of_epi ((upperStar Ab.{u + 1} (S.immersion i)).map a.hom)).of_iso
      (PreservesCokernel.iso (upperStar Ab.{u + 1} (S.immersion i)) a.hom))
  have : Mono a.hom := Preadditive.mono_of_isZero_kernel _ hker
  have : Epi a.hom := Preadditive.epi_of_isZero_cokernel _ hcoker
  have : IsIso ((Mod.forget _).map a) := by
    change IsIso a.hom
    exact isIso_of_mono_of_epi _
  exact isIso_of_reflects_iso a (Mod.forget _)

/-- A left inverse of an endomorphism of a bounded finite-constant-model constructible
complex over the condensed algebraic closure is also a right inverse.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
agent-formulated finiteness ingredient of native cone detection.
(blueprint: lem-sf-condensed-constructible-direct-finiteness).

Proof (the six steps of the DAG):
1. For each integer q apply the homology functor: u = H^q(a), v = H^q(b) satisfy u ≫ v = 1
on M = H^q(K). The constructibility part of `hK` gives `IsConstantModelConstructible`
for M; X is Noetherian and quasi-separated
(`lem-weil-pbc-locally-noetherian-quasi-separated`), so `definition-constructible-sheaves` gives
a finite stratification by immersions with Noetherian, quasi-compactly immersed strata.
2. On each stratum `HasFiniteConstantLocalModel.isLocallyFinitelyPresented`
(`definition-constructible-sheaves--1`) and `condensedQbar_lfp_locally_free`
(`lem-weil-pbc-condensed-qbar-lfp-local-triviality`) give a pro-etale cover on which the
pulled-back module is isomorphic to a finite biproduct of the unit (regular) module.
3. Conjugated by such an isomorphism, the endomorphisms are square matrices over the
commutative endomorphism ring of the tensor unit (`biproductFinMatrix`); commutative
square-matrix direct finiteness (`lem-sf-commutative-square-matrix-direct-finiteness`)
gives the reverse identity, so the restricted endomorphism is invertible (rank 0 included).
4. Extension of scalars along the invertible coefficient map is restriction along its
inverse (`Mod.extendScalarsIsoComapInv`), so the underlying abelian inverse image is
invertible on every covering member; inverse image to a covering object is restriction
(`upperStarIsoLocalizationRestriction`), and `isIso_of_isIso_localizationRestriction`
descends invertibility to the stratum.
5. Abelian inverse image is exact, so kernel and cokernel of the underlying map of u have
zero inverse image on every stratum; finite quasi-compact jointly surjective detection
(`eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp`) makes them zero, so u is monic and
epic, hence invertible; the forgetful module functor reflects isomorphisms.
6. Every H^q(a) is invertible, so a is invertible (`DerivedCategory.isIso_iff`,
`lem-weil-pbc-unbounded-derived-iso-cohomology`); cancelling the epimorphism a from
a ≫ b ≫ a = a gives b ≫ a = 1. -/
theorem condensed_constructible_direct_finiteness (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)))
    (hK : constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X K)
    (a b : K ⟶ K) (hba : a ≫ b = 𝟙 K) : b ≫ a = 𝟙 K := by
  have ha : IsIso a := (DerivedCategory.isIso_iff _ a).mpr fun n ↦ by
    let H := DerivedCategory.homologyFunctor
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)) n
    exact stratified_direct_finiteness ℓ X (H.obj K) (hK.2 n)
      (H.map a) (H.map b) (by rw [← H.map_comp, hba, H.map_id])
  apply (cancel_epi a).mp
  simp only [← Category.assoc, hba, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.ProEtale
