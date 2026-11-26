import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement
import Langlands.Global.AdelicCompactProfileProjection
import Langlands.Global.AdelicHarishChandraRankZero
import Langlands.Global.AdelicInducedHarishChandraStatement
import Langlands.Global.AdelicLeviFibreConvolution
import Langlands.Global.AdelicLocalizedFiniteConvolutionModel
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicParabolicConvolution
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The uniform convolution equation from a fixed parabolic center ideal -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
open Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P U M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine M.X.left]
  {p : P ⟶ G} (iU : U ⟶ P) (l : M ⟶ P)
  {d e : ℕ} (hsG : SmoothOfRelativeDimension d G.X.hom) (hcG : AdelicDifferentialCommutator F G hsG)
  (hsM : SmoothOfRelativeDimension e M.X.hom) (hcM : AdelicDifferentialCommutator F M hsM)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "M∞" => InfiniteAdelicGroupPoints F M
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "Z" => AdelicEnvelopingCenter F G hsG
local notation "DG" => plotSmoothCenterAction F G hsG hcG
local notation "DM" => plotSmoothEnvelopingAction F M hsM hcM
local notation "R∞" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "Γ" => parabolicQuotientSubgroup F p iU l

/-- Each ambient central operator restricts to one Levi enveloping operator on all
infinite Levi fibres of a smooth function on the parabolic quotient. -/
def HasUniformLeviCenterTransfer : Prop :=
  ∀ z : Z, ∃ y : AdelicEnvelopingAlgebra F M hsM,
    ∀ (f : A → ℂ), IsLeftInvariantUnder F G Γ f →
      ∀ (hf : ∀ b, functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G)
        (x : A) (m : M∞),
        (DM y (subgroupFibreSmoothSlice (l ≫ p) f hf x)).val m =
          (DG z ⟨functionInfiniteSlice F G f (finite F G x), hf _⟩).val
            (M.affinePointsTarget (l ≫ p) R∞ m * infinite F G x)

/-- Finite-dimensional compact coefficient profiles imply finite-dimensional right
compact translates. Evaluation at each compact point defines an element of the dual
of the coefficient space. -/
theorem HasAdelicCompactProfiles.isInfiniteSubgroupFiniteFunction
    {Kinf : Subgroup G∞} {E : Submodule ℂ (Kinf → ℂ)} [FiniteDimensional ℂ E]
    {f : A → ℂ} (hf : HasAdelicCompactProfiles Kinf E f) : IsInfiniteSubgroupFiniteFunction F G Kinf f := by
  let profile (x : A) : E := ⟨fun k => f (x * ofInfinite F G k.val), hf x⟩
  let ev : Module.Dual ℂ E →ₗ[ℂ] (A → ℂ) := {
    toFun evaluation x := evaluation (profile x)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hle : Submodule.span ℂ (Set.range fun k : Kinf =>
      fun g => f (g * ofInfinite F G k)) ≤ LinearMap.range ev := by
    apply Submodule.span_le.2
    rintro _ ⟨k, rfl⟩
    exact ⟨(LinearMap.proj k).comp E.subtype, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

variable [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
variable {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- A uniform Levi transfer of central operators implies that localized transported
convolution preserves the same ambient center annihilator at every twist. -/
theorem IsIwasawaCompact.twistedConvolutionEnd_annihilatedByCenter
    (htransfer : HasUniformLeviCenterTransfer (p := p) iU l hsG hcG hsM hcM)
    (hU : IsUnipotent U) (hH : hK.HasSmoothHeightPairings hsG)
    (L : Subgroup Af) {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (hL : HasFiniteProjectionSupport L h)
    (lam : ComplexCharacterParameter F P) (f : C(A, ℂ)) (hinv : IsLeftInvariantUnder F G Γ f)
    (hf : ∀ b, functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G)
    (hfL : ∀ b ∈ L, ∀ x, f (x * ofFinite F G b) = f x)
    (z : Z) (hAnn : ∀ b, DG z ⟨functionInfiniteSlice F G f b, hf b⟩ = 0) :
    ∀ (b : Af) (hv : functionInfiniteSlice F G (hK.twistedConvolutionEnd hsG hh lam f) b ∈
      InfinitePlotSmoothFunctions F G),
      DG z ⟨functionInfiniteSlice F G (hK.twistedConvolutionEnd hsG hh lam f) b, hv⟩ = 0 := by
  obtain ⟨y, hy⟩ := htransfer z
  let g := hK.twistedConvolutionEnd hsG hh lam f
  have hg := hK.twistedConvolutionEnd_smoothSlice hsG hH hh lam f
  have hginv := hK.isLeftInvariantUnder_twistedConvolutionEnd iU l hU hsG hh lam hinv
  intro b hv
  apply Subtype.ext
  funext a
  let x := pair F G a b
  have hcompare := hy g hginv hg x 1
  simp only [map_one, one_mul, x, infinite_pair, finite_pair] at hcompare
  change (DG z ⟨functionInfiniteSlice F G g b, hv⟩).val a = 0
  rw [← hcompare, hK.twistedConvolutionEnd_fibreEnveloping hsG hsM hcM l hH L hh hL lam f hf hfL]
  have hzero (t : A) : (DM y (subgroupFibreSmoothSlice (l ≫ p) f hf (x * t))).val 1 = 0 := by
    rw [hy f hinv hf, hAnn]
    rfl
  trans ∫ _ : A, (0 : ℂ) ∂(Measure.haar : Measure A)
  · apply integral_congr_ae
    filter_upwards with t
    exact mul_eq_zero_of_right _ (hzero t)
  · exact integral_zero _ _

local notation "K∞" => Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K

/-- General parabolic Harish-Chandra finiteness and the uniform Levi center transfer
provide a common model on the original inducing quotient and at the original compact. -/
theorem IsIwasawaCompact.hasConvolutionEquationAt_of_parabolicCenter [IsAffineHom G.X.hom]
    (hFiniteness : ParabolicHarishChandraFinitenessStatement.{u})
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hu : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l iU)) (hmax : IsMaximalCompactSubgroup F G K)
    (hH : hK.HasSmoothHeightPairings hsG)
    (htransfer : HasUniformLeviCenterTransfer (p := p) iU l hsG hcG hsM hcM)
    {N n : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hρ : IsClosedSubgroup rho)
    (coord : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ)
    (f : C(A, ℂ)) (hf : IsAutomorphicFunctionOn F G hsG hcG Γ K∞ rho f) :
    HasConvolutionEquationAt K∞ (fun s => hK.parameterTwist f (coord s)) s₀ := by
  let : CompactSpace K∞ := isCompact_iff_compactSpace.mp hmax.isMaximalCompact_comap_ofInfinite.1
  let : MeasurableSpace K∞ := borel K∞
  let : BorelSpace K∞ := ⟨rfl⟩
  let measure : Measure K∞ := Measure.haar
  have hKi (k : K∞) : ofInfinite F G k.val ∈ K := k.property
  obtain ⟨E, hEfinite, hE, hleft, hfE⟩ := exists_finite_adelicCompactProfiles K∞ f hf.2.2.1
  let : FiniteDimensional ℂ E := hEfinite
  obtain ⟨J, hJ, hfJ⟩ := hf.2.2.2.1
  obtain ⟨L₀, hL₀, hfL₀⟩ := hf.2.1.2.2
  let L : Subgroup Af := L₀ ⊓ K.map (finite F G).toMonoidHom
  have hL : IsOpen (L : Set Af) := hL₀.inter (IsMaximalCompactSubgroup.isOpen_finite F G K hmax)
  have hLK : L ≤ K.comap (ofFinite F G).toMonoidHom := by
    intro b hb
    obtain ⟨x, hx, hxb⟩ := hb.2
    exact hxb ▸ ((hmax.mem_iff x).mp hx).2
  let W : Set (A → ℂ) := {g | IsAutomorphicFunctionOn F G hsG hcG Γ K∞ rho g ∧
    (∀ b ∈ L, ∀ x : A, g (x * ofFinite F G b) = g x) ∧
    (∀ z ∈ J, ∀ b : Af, ∀ hg : functionInfiniteSlice F G g b ∈ InfinitePlotSmoothFunctions F G,
      DG z ⟨functionInfiniteSlice F G g b, hg⟩ = 0) ∧ HasAdelicCompactProfiles K∞ E g}
  let V : Set C(A, ℂ) := {v | (v : A → ℂ) ∈ W}
  let S := Submodule.span ℂ V
  have hfS : f ∈ S := Submodule.subset_span ⟨hf, fun b hb => hfL₀ b hb.1, hfJ, hfE⟩
  let coe := (ContinuousMap.coeFnLinearMap ℂ : C(A, ℂ) →ₗ[ℂ] (A → ℂ))
  have hcoe : Function.Injective coe := fun _ _ he => ContinuousMap.ext (congrFun he)
  have hSW : S.map coe ≤ Submodule.span ℂ W := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨v, hv, rfl⟩
    exact hv
  let : FiniteDimensional ℂ (Submodule.span ℂ W) := hFiniteness F G P M U p iU l hG hp hu hl hmul
    K hmax hK rho hsG hcG hρ J hJ L hL E hEfinite
  let : FiniteDimensional ℂ (S.map coe) := Submodule.finiteDimensional_of_le hSW
  let : FiniteDimensional ℂ S := FiniteDimensional.of_injective
    (Submodule.equivMapOfInjective coe hcoe S).toLinearMap (Submodule.equivMapOfInjective coe hcoe S).injective
  have hprofiles (v : C(A, ℂ)) (hv : v ∈ S) : HasAdelicCompactProfiles K∞ E v := by
    refine Submodule.span_induction (s := V) (p := fun g _ => HasAdelicCompactProfiles K∞ E g)
      (fun g hg => (show (g : A → ℂ) ∈ W from hg).2.2.2) (fun _ => E.zero_mem)
      (fun _ _ _ _ hg hw x => E.add_mem (hg x) (hw x))
      (fun c _ _ hg x => E.smul_mem c (hg x)) hv
  obtain ⟨a, b, haFinite, hbFinite, ha, hb, hproject⟩ :=
    exists_reproducing_adelicCompactProfileWeights (F := F) (G := G) K∞ measure E hE hleft
  have htwist (v : S) : HasAdelicCompactProfiles K∞ E (hK.parameterTwist (v : C(A, ℂ)) (coord s₀)) :=
    (hK.hasAdelicCompactProfiles_parameterTwist_iff K∞ hKi E (coord s₀) v).2 (hprofiles v v.property)
  apply hK.hasConvolutionEquationAt_of_localized_averaged_stability hsG measure coord s₀ f S hfS
    a b haFinite hbFinite (fun v => ha _ (htwist v)) (fun v => hb _ (htwist v)) L hL
  intro h hh hsup s
  let hright := isAdelicTestFunction_rightCompactKernelAverage measure hsG b hh
  let hfilter := isAdelicTestFunction_leftCompactKernelAverage measure hsG a hright
  let D := hK.twistedConvolutionEnd hsG hfilter (coord s)
  have hsup' := hasFiniteProjectionSupport_averaged measure hsup a b
  have hstable : S ≤ S.comap D := by
    apply Submodule.span_le.2
    intro v hv
    have hv' : (v : A → ℂ) ∈ W := hv
    obtain ⟨⟨hvinv, hvsmooth, _, _, hvgrowth⟩, hvL, hvJ, _⟩ := hv'
    have hinv := hK.isLeftInvariantUnder_twistedConvolutionEnd iU l hu.1.isUnipotent hsG hfilter
      (coord s) hvinv
    have hrightLevel := hK.twistedConvolutionEnd_rightInvariant hsG L hLK hfilter hsup' (coord s) hvL
    have hsmooth := hK.twistedConvolutionEnd_smoothSlice hsG hH hfilter (coord s) v
    have hcenter (z : Z) (hz : z ∈ J) := hK.twistedConvolutionEnd_annihilatedByCenter
      iU l hsG hcG hsM hcM htransfer hu.1.isUnipotent hH L hfilter hsup' (coord s) v hvinv
      hvsmooth.2.1 hvL z (fun b => hvJ z hz b (hvsmooth.2.1 b))
    have hprofile := hK.hasAdelicCompactProfiles_twistedConvolutionEnd_leftCompactKernelAverage K∞ measure
      hKi hsG E a hproject hright (coord s) v
    have hmoderate := (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr
      (hK.hasHeightGrowth_twistedConvolutionEnd rho hN hsG hfilter (coord s)
        ((hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mp hvgrowth))
    refine Submodule.subset_span ?_
    exact ⟨⟨hinv, ⟨(D v).continuous, hsmooth, L, hL, hrightLevel⟩,
      hprofile.isInfiniteSubgroupFiniteFunction, ⟨J, hJ, hcenter⟩, hmoderate⟩,
      hrightLevel, hcenter, hprofile⟩
  exact fun v hv => hstable hv

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

/-- Uniform restriction of central operators to the infinite Levi fibres of
inducing functions for connected reductive groups. -/
def UniformParabolicLeviCenterTransferStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P U M : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [IsAffine M.X.left]
    (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P),
    IsConnectedReductive G → IsParabolicSubgroup p →
    LeviSubgroup.IsGeometricUnipotentRadical iU → IsRationalLeviSubgroup l →
    IsIso (subgroupMultiplication l iU) →
    ∀ {d e : ℕ} (hsG : SmoothOfRelativeDimension d G.X.hom)
      (hcG : AdelicDifferentialCommutator F G hsG)
      (hsM : SmoothOfRelativeDimension e M.X.hom) (hcM : AdelicDifferentialCommutator F M hsM),
      HasUniformLeviCenterTransfer (p := p) iU l hsG hcG hsM hcM

/-- The original Harish-Chandra equation for all twists follows from parabolic
Harish-Chandra finiteness, smooth Iwasawa height and uniform Levi center transfer. -/
theorem inducedHarishChandraEquations_of_parabolicCenter
    (hFiniteness : ParabolicHarishChandraFinitenessStatement.{u})
    (hHeight : IwasawaSmoothHeightPairingsStatement.{u})
    (hLevi : UniformParabolicLeviCenterTransferStatement.{u}) :
    InducedHarishChandraEquationsStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ _ _ hG hU K hK N d
    rho hsG hcG f hmax hρ hf n coord s₀
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact harishChandraRankZero F G rho hρ hsG (K.comap (ofInfinite F G).toMonoidHom)
      (fun s => hK.parameterTwist f (coord s)) s₀
  let : Smooth G.X.hom := hG.smooth
  have hp := r.isCompatible.parabolic
  have hl := r.isCompatible.levi
  have hmul := r.isIso_subgroupMultiplication_of_radical hU
  let : IsAffine M.X.left := hl.isConnectedReductive.affineScheme
  let hsM := hl.isConnectedReductive.smoothDimension_spec
  let hcM := adelicDifferentialCommutator_of_smooth F M hsM
  let g : C(AdelicGroupPoints F G, ℂ) := ⟨f, hf.2.1.1⟩
  exact hK.hasConvolutionEquationAt_of_parabolicCenter iU l hsG hcG hsM hcM hFiniteness
    hG hp hU hl hmul hmax (hHeight F G P p K hK hsG hG hp hmax)
    (hLevi F G P U M p iU l hG hp hU hl hmul hsG hcG hsM hcM) rho hN hρ
    coord.toLinearMap s₀ g hf

end Langlands.Global
