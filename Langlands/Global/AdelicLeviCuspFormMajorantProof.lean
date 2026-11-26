import Langlands.Global.AdelicLeviCuspFormMajorantStatement
import Langlands.Global.AdelicRelativeCuspidalRapidDecay
import Langlands.Global.AdelicUniformDirectionalGrowth
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicSiegelSetupExistenceProof
import Langlands.Global.AdelicRationalHeightReduction
import Langlands.Global.AdelicStandardTopAutomorphy
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthProof
import Langlands.Automorphic.GroupSchemeRationalAutomorphicRealization
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding
import Langlands.Automorphic.GroupSchemeManifoldSmooth

/-! # Weighted majorants of cusp forms on standard Levi subgroups: proof

This file proves `LeviCuspFormPairingMajorantStatement` (Mœglin–Waldspurger I.2.12 and
I.2.18). The majorant is a constant function on the norm-one quotient `M_J(F) \ M_J(𝔸)¹`,
which has finite volume. Every class has a representative in a weak Siegel product of `M_J`
times a finite set. On these representatives a cusp form decays faster than every power of the
height, by the relative cuspidal rapid decay for the canonical standard parabolic family of
`M_J`. The growth weight `‖ι(x) g‖^R` is at most a constant times a power of the height of `x`.

* `exists_rationalRepresentatives_cuspForm_rapidDecay`: for a connected reductive group `H`,
  a cusp form on `H(F) \ H(𝔸)` is rapidly decreasing on a set of representatives of the
  norm-one quotient.
* `exists_closed_weight_bound`: the growth weight of a closed matrix embedding, read along a
  homomorphism `j : H → G`, is bounded by a power of the height of a positive-size closed
  matrix embedding of `H`.
* `leviCuspFormPairingMajorant`: the statement.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal Pointwise Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors RepresentationGrowth

section RapidDecay

variable {F : Type u} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- A cusp form on `H(F) \ H(𝔸)` is rapidly decreasing on a set of representatives of the
norm-one quotient: there is a set `S` meeting the `H(F)`-orbit of every norm-one point such that
`‖ψ(y)‖ ‖y‖^m` is bounded on `S` for every `m`, where `‖·‖` is the height of `rho`. The set is a
weak Siegel product times a finite set of norm-one points. -/
theorem exists_rationalRepresentatives_cuspForm_rapidDecay
    (hH : IsConnectedReductive H) {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d H.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F H))
    (hKinf : CompactIwasawa.IsMaximalCompact Kinf)
    (rho : MatrixRepresentation H (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (ψ : AdelicGroupPoints F H → ℂ)
    (hψ : IsAutomorphicFunctionOn F H hsmooth (adelicDifferentialCommutator_of_smooth F H hsmooth)
      (rationalSubgroup F H) Kinf rho ψ)
    (hcusp : ∀ (P' U' : GroupScheme (Spec (CommRingCat.of F))) (p' : P' ⟶ H) (r : U' ⟶ P')
      [IsAffine U'.X.left] [IsClosedImmersion (r ≫ p').hom.hom.left],
      IsParabolicSubgroup p' → LeviSubgroup.IsGeometricUnipotentRadical r →
        SubgroupFunctor.range p' ≠ ⊤ → subgroupConstantTerm F (r ≫ p') ψ = 0) :
    ∃ S : Set (AdelicGroupPoints F H),
      (∀ x : normOneSubgroup F H, ∃ q : RationalGroupPoints F H,
        rational F H q * (x : AdelicGroupPoints F H) ∈ S) ∧
      ∀ m : ℕ, ∃ C : ℝ, ∀ y ∈ S, ‖ψ y‖ * adelicHeight F H rho y ^ m ≤ C := by
  classical
  let hcalc := adelicDifferentialCommutator_of_smooth F H hsmooth
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence F H hH
  obtain ⟨K, H₁, W, hKc, -, -, -, -, hW, hW1, hcov⟩ :=
    exists_compact_openSubgroup_finite_cover F H hH T i ν T₀ j hS
  obtain ⟨C, t, rfl, hcover⟩ :=
    exists_rational_mul_mem_weakSiegelProduct_mul F H hH T i ν T₀ j hS K hKc W hW hW1 hcov
  refine ⟨weakSiegelProduct F H T i ν (canonicalStandardFactors F H T i ν) C T₀ j t * W,
    hcover, ?_⟩
  intro m
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨-, -, -, -, -, -, -, ⟨_, _, _, -, ht₀, -⟩, -⟩ := hS
    exact ht₀.1.1
  let 𝓕H : StandardParabolicFamily F H :=
    StandardParabolicFamily.ofMaximalSplitTorus hH i hS.1 ν hS.2.1
  have hspan : Langlands.LinearAlgebra.RationalSpan.ratSpan
      (((fun α : characterLattice 𝓕H.T => (j : T₀ ⟶ 𝓕H.T) ≫ α) ''
        simpleRelativeRoots 𝓕H.i 𝓕H.ν) ∪ ∅) = ⊤ := by
    rw [Set.union_empty]
    exact ratSpan_restrict_simpleRelativeRoots_eq_top relativeRootNegation
      relativeCharacterRootComplement hH hS
  -- uniform growth of all derivative words
  obtain ⟨f, hf, hfψ⟩ := rationalAutomorphicRealization rho hsmooth hcalc Kinf ψ hψ
  obtain ⟨e, he⟩ := (hasAdelicUniformModerateGrowth_iff F H rho hsmooth hcalc hN f).mp
    (adelicAutomorphicUniformGrowth F H Kinf rho hsmooth hH hrho hKinf hN f hf)
  have hgrowth : ∀ s : List (InfiniteAdelicGroupPoints.smoothModel F d), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (_ : Unit) x, ‖adelicIteratedDirectionalValue hsmooth s ψ x‖ ≤
        C * adelicHeight F H rho x ^ (e : ℝ) * 1 := by
    intro s
    obtain ⟨C, hC, hb⟩ := he (adelicDirectionalWordEnveloping hsmooth s)
    refine ⟨C, hC, fun _ x => ?_⟩
    have h := hb x
    rw [evaluate_adelicDirectionalWordEnveloping hsmooth hcalc s f, hfψ] at h
    rwa [Real.rpow_natCast, mul_one]
  obtain ⟨hinv, ⟨hcont, hslices, L, hLo, hlevel⟩, -, -, -⟩ := hψ
  -- the unipotent radical of the full standard parabolic acts trivially
  have hunip : ∀ (u : AdelicGroupPoints F (𝓕H.U 𝓕H.top)) (x : AdelicGroupPoints F H),
      ψ (map F (𝓕H.U 𝓕H.top) H (𝓕H.iU 𝓕H.top ≫ 𝓕H.p 𝓕H.top) u * x) = ψ x := by
    intro u x
    have hmem : map F (𝓕H.U 𝓕H.top) H (𝓕H.iU 𝓕H.top ≫ 𝓕H.p 𝓕H.top) u ∈
        rationalSubgroup F H := by
      rw [← 𝓕H.parabolicQuotientSubgroup_top]
      exact Subgroup.mem_sup_left ⟨u, rfl⟩
    exact hinv _ hmem x
  -- cuspidality along every proper standard parabolic
  have hcuspTop : 𝓕H.IsCuspidalAlong 𝓕H.top ψ := by
    intro Q hQ
    refine hcusp _ _ (𝓕H.p Q) (𝓕H.iU Q) (𝓕H.isCompatible Q).parabolic
      (𝓕H.isUnipotentRadical Q) fun htop => hQ.not_ge ?_
    rw [𝓕H.le_iff_range_le, htop]
    exact SubgroupFunctor.le_def.mpr fun _ => le_top
  -- the compact data of the Siegel representatives
  let D := canonicalStandardFactors F H T i ν
  let Ω : Set (AdelicGroupPoints F H) := compactPrefix F H T i ν D C
  have hΩc : IsCompact Ω := isCompact_compactPrefix F H T i ν D C
  let Kset : Set (AdelicGroupPoints F H) := (C.compactSubgroup : Set (AdelicGroupPoints F H)) * W
  have hKsetc : IsCompact Kset := C.compact_compactSubgroup.mul hW.isCompact
  let Yf : Set (FiniteAdelicGroupPoints F H) := finite F H '' Ω * finite F H '' Kset
  have hYf : IsCompact Yf :=
    (hΩc.image (finite F H).continuous).mul (hKsetc.image (finite F H).continuous)
  have hΩP : Ω ⊆ ((map F (Standard.parabolicScheme i ν ∅) H
      (Standard.parabolicHom i ν ∅)).toMonoidHom.range : Set (AdelicGroupPoints F H)) := by
    rintro _ ⟨_, ⟨n, -, rfl⟩, _, ⟨mm, -, rfl⟩, rfl⟩
    refine Subgroup.mul_mem _
      ⟨map F _ _ (Standard.unipotentToParabolic i ν ∅) n, ?_⟩
      ⟨map F _ _ (Standard.leviToParabolic i ν ∅) mm.val, ?_⟩
    · change _ = map F _ H (Standard.unipotentHom i ν ∅) n
      rw [← Standard.unipotentToParabolic_comp]
      exact (map_comp_apply_of_hom (p := Standard.parabolicHom i ν ∅)
        (Standard.unipotentToParabolic i ν ∅) n).symm
    · change _ = map F _ H (Standard.leviHom i ν ∅) mm.val
      rw [← Standard.leviToParabolic_comp]
      exact (map_comp_apply_of_hom (p := Standard.parabolicHom i ν ∅)
        (Standard.leviToParabolic i ν ∅) mm.val).symm
  obtain ⟨C', -, hbound⟩ := StandardParabolicFamily.adelicRelativeCuspidalRapidDecay.{u, 0}
    𝓕H j hsmooth rho hT₀ hN 𝓕H.top ∅ hspan t 0 le_rfl Ω Kset hΩc hKsetc hΩP Yf hYf L hLo
    Unit (fun _ => ψ) (fun _ => 1) (fun _ => zero_le_one) (fun _ => hcont)
    (fun _ c => (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F H hsmooth _).mp
      (hslices c))
    (fun _ r hr x => hinv r (rationalImage_le_rationalSubgroup _ hr) x)
    (fun _ u x => hunip u x) (fun _ l hl x => hlevel l hl x) (fun _ => hcuspTop)
    (e : ℝ) (Nat.cast_nonneg e) hgrowth m
  refine ⟨C', ?_⟩
  rintro y ⟨s, hs, w, hw, rfl⟩
  obtain ⟨n, hn, mm, hmm, a, ha, k, hk, rfl⟩ :=
    (mem_productSet_iff F H T i ν D C T₀ j _ s).mp hs
  set p := map F D.unipotent H D.unipotentInclusion n * map F D.levi H D.leviInclusion mm
  have hp : p ∈ Ω := ⟨_, ⟨n, hn, rfl⟩, _, ⟨mm, hmm, rfl⟩, rfl⟩
  have hkw : k * w ∈ Kset := ⟨k, hk, w, hw, rfl⟩
  have hfin : finite F H (p * positiveMap F H T i T₀ j a * (k * w)) ∈ Yf := by
    refine ⟨_, ⟨p, hp, rfl⟩, _, ⟨k * w, hkw, rfl⟩, ?_⟩
    simp only [map_mul, finite_positiveMap F H T i T₀ j hT₀ a, mul_one]
  have hb := hbound () p hp a ha (fun χ hχ => absurd hχ (Set.notMem_empty χ))
    (fun α hα => absurd hα.1 hα.2) (k * w) hkw hfin
  rw [mul_one] at hb
  show ‖ψ (p * positiveMap F H T i T₀ j a * k * w)‖ *
    adelicHeight F H rho (p * positiveMap F H T i T₀ j a * k * w) ^ m ≤ C'
  rw [mul_assoc (p * positiveMap F H T i T₀ j a) k w]
  exact hb

end RapidDecay

section Weight

variable {F : Type u} [Field F] [NumberField F]

/-- The adelic height of a matrix representation, read along a homomorphism, is the height of
the composite representation. -/
theorem adelicHeight_map_eq_adelicHeight_comp {H G : GroupScheme (Spec (CommRingCat.of F))}
    (j : H ⟶ G) {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (x : AdelicGroupPoints F H) :
    adelicHeight F G rho (map F H G j x) = adelicHeight F H (j ≫ rho) x := by
  have h : G.affinePointsTarget rho
      (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))
      (map F H G j x) =
      H.affinePointsTarget (j ≫ rho)
        (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) x := by
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]
  show AdelicMatrixHeight.height F N (GeneralLinearGroupPoints.adelicHomeomorph F N
      (G.affinePointsTarget rho _ (map F H G j x))) =
    AdelicMatrixHeight.height F N (GeneralLinearGroupPoints.adelicHomeomorph F N
      (H.affinePointsTarget (j ≫ rho) _ x))
  rw [h]

/-- The growth weight `x ↦ ‖j(x) g‖^R` of a closed matrix embedding of `G` is bounded by a
constant times a natural power of the height of a positive-size closed matrix embedding of `H`,
for which the automorphic functions of the restricted embedding stay automorphic. -/
theorem exists_closed_weight_bound {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d H.X.hom)
    (j : H ⟶ G) (rho : MatrixRepresentation G (Fin N)) (rhoH : MatrixRepresentation H (Fin N))
    (hrhoH : IsClosedSubgroup rhoH)
    (hheight : ∀ x, adelicHeight F G rho (map F H G j x) = adelicHeight F H rhoH x)
    (g : AdelicGroupPoints F G) (R : ℝ) :
    ∃ (N' : ℕ) (rho' : MatrixRepresentation H (Fin N')), 0 < N' ∧ IsClosedSubgroup rho' ∧
      (∀ (Γ : Subgroup (AdelicGroupPoints F H)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F H))
        (φ : AdelicGroupPoints F H → ℂ),
        IsAutomorphicFunctionOn F H hsmooth (adelicDifferentialCommutator_of_smooth F H hsmooth)
            Γ Kinf rhoH φ →
          IsAutomorphicFunctionOn F H hsmooth (adelicDifferentialCommutator_of_smooth F H hsmooth)
            Γ Kinf rho' φ) ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ e : ℕ, ∀ x : AdelicGroupPoints F H,
        adelicSourceNorm F G rho (map F H G j x * g) ^ R ≤ c * adelicHeight F H rho' x ^ e := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨N', rho', hN', hrho', hiff⟩ := exists_positiveMatrixEmbedding_of_isClosedSubgroup
      rhoH hrhoH hsmooth (adelicDifferentialCommutator_of_smooth F H hsmooth)
    have hconst : ∀ y, adelicSourceNorm F G rho y = adelicSourceNorm F G rho 1 := by
      intro y
      unfold adelicSourceNorm
      congr 1
      exact Units.ext (Matrix.ext fun a _ => a.elim0)
    have hnonneg : 0 ≤ adelicSourceNorm F G rho 1 :=
      mul_nonneg (Finset.prod_nonneg fun v _ =>
          pow_nonneg (MatrixInverseHeight.localMaximum_nonneg _ _) _)
        (finprod_nonneg fun v => MatrixInverseHeight.localMaximum_nonneg _ _)
    refine ⟨N', rho', hN', hrho', fun Γ Kinf φ hφ => (hiff Γ Kinf φ).mp hφ,
      adelicSourceNorm F G rho 1 ^ R, Real.rpow_nonneg hnonneg R, 0, fun x => ?_⟩
    rw [hconst, pow_zero, mul_one]
  · refine ⟨N, rhoH, hN, hrhoH, fun _ _ _ h => h, ?_⟩
    let K : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hK : 1 ≤ K := one_le_pow₀ (by exact_mod_cast hN)
    have hK0 : 0 < K := zero_lt_one.trans_le hK
    have hscale (y : AdelicGroupPoints F G) :
        adelicHeight F G rho y = K * adelicSourceNorm F G rho y :=
      adelicHeight_eq_scalar_mul_sourceNorm F G rho y
    have hSpos (y : AdelicGroupPoints F G) : 0 < adelicSourceNorm F G rho y :=
      adelicSourceNorm_pos F G rho hN y
    rcases le_or_gt 0 R with hR | hR
    · have hg1 : 1 ≤ adelicHeight F G rho g := one_le_adelicHeight F G rho hN g
      refine ⟨adelicHeight F G rho g ^ R, Real.rpow_nonneg (zero_le_one.trans hg1) R,
        ⌈R⌉₊, fun x => ?_⟩
      have hx1 : 1 ≤ adelicHeight F H rhoH x := one_le_adelicHeight F H rhoH hN x
      have h1 : adelicSourceNorm F G rho (map F H G j x * g) ≤
          adelicHeight F H rhoH x * adelicHeight F G rho g := by
        calc adelicSourceNorm F G rho (map F H G j x * g)
            ≤ adelicHeight F G rho (map F H G j x * g) := by
              rw [hscale]
              exact le_mul_of_one_le_left (hSpos _).le hK
          _ ≤ adelicHeight F G rho (map F H G j x) * adelicHeight F G rho g :=
              adelicHeight_mul_le F G rho hN _ _
          _ = adelicHeight F H rhoH x * adelicHeight F G rho g := by rw [hheight]
      calc adelicSourceNorm F G rho (map F H G j x * g) ^ R
          ≤ (adelicHeight F H rhoH x * adelicHeight F G rho g) ^ R :=
            Real.rpow_le_rpow (hSpos _).le h1 hR
        _ = adelicHeight F H rhoH x ^ R * adelicHeight F G rho g ^ R :=
            Real.mul_rpow (zero_le_one.trans hx1) (zero_le_one.trans hg1)
        _ ≤ adelicHeight F H rhoH x ^ (⌈R⌉₊ : ℝ) * adelicHeight F G rho g ^ R :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil R))
              (Real.rpow_nonneg (zero_le_one.trans hg1) R)
        _ = adelicHeight F G rho g ^ R * adelicHeight F H rhoH x ^ ⌈R⌉₊ := by
            rw [Real.rpow_natCast, mul_comm]
    · refine ⟨K⁻¹ ^ R, Real.rpow_nonneg (inv_nonneg.mpr hK0.le) R, 0, fun x => ?_⟩
      have hlow : K⁻¹ ≤ adelicSourceNorm F G rho (map F H G j x * g) := by
        have h1 := one_le_adelicHeight F G rho hN (map F H G j x * g)
        rw [hscale] at h1
        calc K⁻¹ = K⁻¹ * 1 := (mul_one _).symm
          _ ≤ K⁻¹ * (K * adelicSourceNorm F G rho (map F H G j x * g)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hK0.le)
          _ = adelicSourceNorm F G rho (map F H G j x * g) := inv_mul_cancel_left₀ hK0.ne' _
      rw [pow_zero, mul_one]
      exact Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hK0) hlow hR.le

end Weight

section Main

/-- **Weighted majorants of cusp forms on standard Levi subgroups** (Mœglin–Waldspurger
I.2.12 and I.2.18). For every cusp form `ψ` on a standard Levi subgroup `M_J`, every `g` and every
real `R`, a constant function is an integrable majorant of `‖ι(x) g‖^R ‖ψ(x)‖` on
`M_J(F) \ M_J(𝔸)¹`, evaluated at representatives in a Siegel set. -/
theorem leviCuspFormPairingMajorant : LeviCuspFormPairingMajorantStatement.{u} := by
  intro F _ _ G _ _ _ 𝓕 K _ _ hKM N rho hrho J ψ hψ g R
  have hM : IsConnectedReductive (𝓕.M J) := (𝓕.isCompatible J).levi.isConnectedReductive
  have : IsAffineHom (𝓕.M J).X.hom := hM.isAffineHom
  have hrhoM : IsClosedSubgroup (𝓕.l J ≫ 𝓕.p J ≫ rho) := by
    have h1 : IsClosedImmersion (𝓕.l J).hom.hom.left := (𝓕.isCompatible J).levi.isClosedSubgroup
    have h2 : IsClosedImmersion (𝓕.p J).hom.hom.left :=
      (𝓕.isCompatible J).parabolic.isClosedSubgroup
    have h3 : IsClosedImmersion rho.hom.hom.left := hrho
    change IsClosedImmersion (𝓕.l J ≫ 𝓕.p J ≫ rho).hom.hom.left
    simp only [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  have hheight (x : AdelicGroupPoints F (𝓕.M J)) :
      adelicHeight F G rho (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) x) =
        adelicHeight F (𝓕.M J) (𝓕.l J ≫ 𝓕.p J ≫ rho) x := by
    rw [adelicHeight_map_eq_adelicHeight_comp, Category.assoc]
  obtain ⟨N', rho', hN', hrho', htransfer, c, hc, e, hweight⟩ :=
    exists_closed_weight_bound (𝓕.leviSmooth J) (𝓕.l J ≫ 𝓕.p J) rho
      (𝓕.l J ≫ 𝓕.p J ≫ rho) hrhoM hheight g R
  have hKinf : CompactIwasawa.IsMaximalCompact
      (𝓕.leviInfiniteCompact (K.comap (ofInfinite F G).toMonoidHom) J) := by
    have h := (hKM J).isMaximalCompact_comap_ofInfinite
    convert h using 1
    ext x
    change ofInfinite F G ((𝓕.M J).affinePointsTarget (𝓕.l J ≫ 𝓕.p J)
        (CommAlgCat.of F (NumberField.InfiniteAdeleRing F)) x) ∈ K ↔
      map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) (ofInfinite F (𝓕.M J) x) ∈ K
    rw [map_ofInfinite]
  obtain ⟨S, hSrep, hSdec⟩ := exists_rationalRepresentatives_cuspForm_rapidDecay hM
    (𝓕.leviSmooth J) _ hKinf rho' hN' hrho' ψ (htransfer _ _ _ hψ.1) hψ.2
  obtain ⟨C, hC⟩ := hSdec e
  have := isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F (𝓕.M J) hM
  refine ⟨fun _ => c * C, integrable_const _, Filter.Eventually.of_forall fun q => ?_⟩
  obtain ⟨x₀, rfl⟩ := LeftCosetSpace.mk_surjective _ q
  obtain ⟨r₀, hr₀⟩ := hSrep x₀
  refine ⟨rationalNormOne F (𝓕.M J) r₀ * x₀,
    LeftCosetSpace.mk_subgroup_mul (rationalNormOneSubgroup F (𝓕.M J))
      ⟨rationalNormOne F (𝓕.M J) r₀, ⟨r₀, rfl⟩⟩ x₀, ?_⟩
  have hval : ((rationalNormOne F (𝓕.M J) r₀ * x₀ : normOneSubgroup F (𝓕.M J)) :
      AdelicGroupPoints F (𝓕.M J)) = rational F (𝓕.M J) r₀ * x₀ := by
    rw [Subgroup.coe_mul, rationalNormOne_val]
  rw [hval]
  calc adelicSourceNorm F G rho
          (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) (rational F (𝓕.M J) r₀ * x₀) * g) ^ R *
        ‖ψ (rational F (𝓕.M J) r₀ * x₀)‖
      ≤ (c * adelicHeight F (𝓕.M J) rho' (rational F (𝓕.M J) r₀ * x₀) ^ e) *
          ‖ψ (rational F (𝓕.M J) r₀ * x₀)‖ :=
        mul_le_mul_of_nonneg_right (hweight _) (norm_nonneg _)
    _ = c * (‖ψ (rational F (𝓕.M J) r₀ * x₀)‖ *
          adelicHeight F (𝓕.M J) rho' (rational F (𝓕.M J) r₀ * x₀) ^ e) := by ring
    _ ≤ c * C := mul_le_mul_of_nonneg_left (hC _ hr₀) hc

end Main

end Langlands.Global
