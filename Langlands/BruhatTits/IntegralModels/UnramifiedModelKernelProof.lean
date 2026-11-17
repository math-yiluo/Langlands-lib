import Langlands.BruhatTits.IntegralModels.TorusRootKernelOpenChart
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction
import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRationalReduction
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotient
import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellTheorem
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.BruhatTits.IntegralModels.RootDepthKernel
import Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationProof
import Langlands.BruhatTits.IntegralModels.TorusRootKernelCell
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus

/-! # Smooth connected unipotent kernels over the maximal unramified integers

The kernel assertion of Kaletha–Prasad Proposition 8.4.15, assembled from the
ordered integral open cell, ordered fixer factorization, root-depth kernels
and the torus reduction. All statement premises of these reductions are
discharged by published theorems. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

universe u

open Langlands Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable
open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.IntegralModels

private instance kernelProofBaseChangedAffine {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

private theorem commonOrderedRootData (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : MaximalUnramified.BuildingData F G) :
    ∃ (ν : cocharacterLattice C.S) (nneg npos : ℕ)
      (aneg : Fin nneg → relativeRoots C.i) (apos : Fin npos → relativeRoots C.i),
      IsGenericCocharacter C.i ν ∧
      Function.Injective aneg ∧
      Set.range (fun j => (aneg j : characterLattice C.S)) =
        RelativeRoot.indivisiblePositiveRoots C.i (-ν) ∧
      Function.Injective apos ∧
      Set.range (fun j => (apos j : characterLattice C.S)) =
        RelativeRoot.indivisiblePositiveRoots C.i ν := by
  classical
  let : Smooth G.X.hom := C.isConnectedReductive.smooth
  have hfin := C.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots C.i
  have hex (ν : cocharacterLattice C.S) :
      ∃ (n : ℕ) (a : Fin n → relativeRoots C.i),
        Function.Injective a ∧
        Set.range (fun j => (a j : characterLattice C.S)) =
          RelativeRoot.indivisiblePositiveRoots C.i ν := by
    obtain ⟨n, a, ha, hrange⟩ :=
      RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots C.i ν hfin
    have hamem (j : Fin n) : a j ∈ RelativeRoot.indivisiblePositiveRoots C.i ν := by
      rw [← hrange]
      exact Set.mem_range_self j
    let b (j : Fin n) : relativeRoots C.i := ⟨a j, (hamem j).1.1⟩
    refine ⟨n, b, ?_, hrange⟩
    intro j k h
    exact ha (congrArg Subtype.val h)
  obtain ⟨ν, hν⟩ := C.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter C.i
  obtain ⟨nneg, aneg, hneg, hrneg⟩ := hex (-ν)
  obtain ⟨npos, apos, hpos, hrpos⟩ := hex ν
  exact ⟨ν, nneg, npos, aneg, apos, hν, hneg, hrneg, hpos, hrpos⟩

/-- **KP Proposition 8.4.15**, kernel assertion over the maximal unramified
integers, for the arbitrary smooth model presentations and common translates
of apartment subsets in the published statement. -/
theorem unramifiedModelKernel : UnramifiedModelKernelStatement.{u} := by
  apply unramifiedModelKernel_of_smoothConnected
    (unramifiedQuasiSplit_of_henselianDiscrete
      (henselianDiscreteQuasiSplitReduction
        (quasiSplitRegularClassRationalReduction quasiSplitSteinbergQuotient)))
    unramifiedZeroPointsIndependence
  intro F _ _ _ _ G _ C E hE Ω Ω' hne hbdd' hcl N N' hN hN' hpts hpts' ψ
  have hne' := C.apartment.nonempty_of_nonempty_subset_affineClosure hne hcl
  have hbdd : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω) := fun f =>
    C.apartment.bddAbove_affineImage_of_subset_affineClosure f (hbdd' f) hcl
  let x : C.Apartment := hne.choose
  obtain ⟨ν, nneg, npos, aneg, apos, hν, hinjNeg, hrangeNeg, hinjPos, hrangePos⟩ :=
    commonOrderedRootData F (baseChanged F (inertiaFixedField F) G) C
  obtain ⟨A, hA⟩ := unramifiedOrderedIntegralOpenCell F _ C E hE x Ω hne hbdd N hN hpts
  obtain ⟨B, hB⟩ :=
    unramifiedOrderedIntegralOpenCell F _ C E hE x Ω' hne' hbdd' N' hN' hpts'
  let e := TorusRootModelFamilyData.orderedIntegralIndex aneg apos
  let : IsOpenImmersion (RelativeRoot.orderedMultiplication
      (fun i => (A.modelMap (e i)).hom)).left :=
    hA ν hν nneg npos aneg apos hinjNeg hrangeNeg hinjPos hrangePos
  let : IsOpenImmersion (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom)).left :=
    hB ν hν nneg npos aneg apos hinjNeg hrangeNeg hinjPos hrangePos
  let : Mono (RelativeRoot.orderedMultiplication
      (fun i => (A.modelMap (e i)).hom)) := Over.mono_of_mono_left _
  have hfac := unramifiedOrderedFixerFactorization F _ C E hE ν hν nneg npos
    aneg apos hinjNeg hrangeNeg hinjPos hrangePos Ω Ω' hne' hbdd'
  have hrange := A.closedPoint_mem_range_orderedChart B e ψ
    hne hbdd hne' hbdd' hpts'.le hfac
  have hext := IntegralModel.fixedField_hasSmoothHomExtension
    IntegralModel.smoothHomExtension F
  have hdepth : ∀ a : relativeRoots C.i,
      C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω' :=
    TorusRootModelFamilyData.rootDepth_le_of_subset_affineClosure hne hbdd' hcl
  exact A.smooth_connected_kernel_of_orderedOpenCharts B e ψ hext hdepth
    unramifiedRootDepthKernel hN' hrange

end Langlands.BruhatTits.IntegralModels
