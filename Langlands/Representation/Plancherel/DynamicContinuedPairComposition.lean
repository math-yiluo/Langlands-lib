import Langlands.Representation.Plancherel.DynamicCommonLeviGalleryComposite
import Langlands.Representation.Plancherel.DynamicOppositeGalleryComparison
import Langlands.Representation.Plancherel.ActualCommonLeviRationalTensor

/-! # Distance-additive composition of actual continued compact operators -/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviComposition DynamicCommonLeviContinuation
open ActualCommonLeviTensor UnramifiedOperatorFamily

private theorem comp_smul_of_conjugate
    {U₀ U₁ U₂ V₀ V₁ V₂ : Type*}
    [AddCommGroup U₀] [Module ℂ U₀] [AddCommGroup U₁] [Module ℂ U₁]
    [AddCommGroup U₂] [Module ℂ U₂] [AddCommGroup V₀] [Module ℂ V₀]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (E₀ : U₀ ≃ₗ[ℂ] V₀) (E₁ : U₁ ≃ₗ[ℂ] V₁) (E₂ : U₂ ≃ₗ[ℂ] V₂)
    (p : U₀ →ₗ[ℂ] U₁) (q : U₁ →ₗ[ℂ] U₂) (r : U₀ →ₗ[ℂ] U₂)
    (P : V₀ →ₗ[ℂ] V₁) (Q : V₁ →ₗ[ℂ] V₂) (R : V₀ →ₗ[ℂ] V₂)
    (a b c s t : ℂ) (hscalar : b * a * s = t * c)
    (hp : ∀ v, E₁ (p v) = a • P (E₀ v)) (hq : ∀ v, E₂ (q v) = b • Q (E₁ v))
    (hr : ∀ v, E₂ (r v) = c • R (E₀ v))
    (hcomp : ∀ v, Q (P v) = s • R v) :
    q.comp p = t • r := by
  ext v
  apply E₂.injective
  change E₂ (q (p v)) = E₂ (t • r v)
  rw [hq, hp, map_smul, hcomp, map_smul, hr, ← mul_smul, ← mul_smul, ← mul_smul, hscalar]

section RationalExtension

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [TopologicalSpace (rationalPoints H)]
  (hprojection : Continuous (rationalValuationImageProjection H)) (hH : IsConnectedReductive H)
  {U₀ U₁ U₂ : Type*} [AddCommGroup U₀] [Module ℂ U₀] [AddCommGroup U₁] [Module ℂ U₁]
  [AddCommGroup U₂] [Module ℂ U₂]

local notation "X" => unramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul)

include hprojection hH in
private theorem continuedComposition_eq_of_eqOn
    {Ω₀ Ω₁ Ω₂ : Set X} {A₀ : Ω₀ → U₀ →ₗ[ℂ] U₁} {A₁ : Ω₁ → U₁ →ₗ[ℂ] U₂}
    {A₂ : Ω₂ → U₀ →ₗ[ℂ] U₂}
    (p : RationalOperatorContinuationData Ω₀ A₀) (q : RationalOperatorContinuationData Ω₁ A₁)
    (r : RationalOperatorContinuationData Ω₂ A₂) (c : ℂ)
    {D : Set X} (hD : IsOpen D) (hne : D.Nonempty)
    (hsub : D ⊆ (p.regularRegion ∩ q.regularRegion) ∩ r.regularRegion)
    (he : ∀ z (hz : z ∈ D),
      (q.continuedOperator ⟨z, (hsub hz).1.2⟩).comp (p.continuedOperator ⟨z, (hsub hz).1.1⟩) =
        c • r.continuedOperator ⟨z, (hsub hz).2⟩) :
    ∀ z : ↥((p.regularRegion ∩ q.regularRegion) ∩ r.regularRegion),
      (q.continuedOperator ⟨z.val, z.property.1.2⟩).comp
          (p.continuedOperator ⟨z.val, z.property.1.1⟩) =
        c • r.continuedOperator ⟨z.val, z.property.2⟩ := by
  let R := (p.regularRegion ∩ q.regularRegion) ∩ r.regularRegion
  let B₀ : R → U₀ →ₗ[ℂ] U₂ := fun z =>
    (q.continuedOperator ⟨z.val, z.property.1.2⟩).comp
      (p.continuedOperator ⟨z.val, z.property.1.1⟩)
  let B₁ : R → U₀ →ₗ[ℂ] U₂ := fun z => c • r.continuedOperator ⟨z.val, z.property.2⟩
  have hp := p.continuedOperator_rational.restrict (show R ⊆ p.regularRegion from fun _ hz => hz.1.1)
  have hq := q.continuedOperator_rational.restrict (show R ⊆ q.regularRegion from fun _ hz => hz.1.2)
  have hB₁ : IsRationalOperatorOn R B₁ := by
    obtain ⟨den, hden, hpoly⟩ := r.continuedOperator_rational.restrict
      (show R ⊆ r.regularRegion from Set.inter_subset_right)
    refine ⟨den, hden, fun v => ?_⟩
    convert (hpoly v).linearMap (c • LinearMap.id : U₂ →ₗ[ℂ] U₂) using 1
    funext z
    exact smul_comm (den.val z.val) c _
  exact rationalUnramifiedOperator_eq_of_eqOn_isOpen H hprojection hH hD hne hsub
    B₀ B₁ (hq.comp hp) hB₁ he

include hprojection hH in
/-- The denominator of a continuation over a nonempty set gives a dense regular region. -/
theorem continuation_regularRegion_dense [IsAffine H.X.left]
    {Ω : Set X} {A : Ω → U₀ →ₗ[ℂ] U₁} (p : RationalOperatorContinuationData Ω A)
    (hne : Ω.Nonempty) : Dense p.regularRegion := by
  apply rationalUnramifiedRegular_dense_nonzero H hprojection hH p.denominator
  obtain ⟨z, hz⟩ := hne
  intro h
  exact p.denominator_nonzero ⟨z, hz⟩ (by rw [h]; rfl)

end RationalExtension

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (x y w : GalleryVertex χ)

set_option hygiene false in
local notation "Iwasawa[" x "]" => ∀ g : rationalPoints G, ∃ q : parabolic (x : GalleryVertex χ).val,
  ∃ k : K, g = (q : rationalPoints G) * (k : rationalPoints G)

variable (hxK : Iwasawa[x]) (hyK : Iwasawa[y]) (hwK : Iwasawa[w])
  (p : ContinuedPair χ hG K hK x.val x.property hxK y.val y.property hyK A)
  (q : ContinuedPair χ hG K hK y.val y.property hyK w.val w.property hwK A)
  (r : ContinuedPair χ hG K hK x.val x.property hxK w.val w.property hwK A)

set_option hygiene false in
local notation "H" => parameterScheme χ
set_option hygiene false in
local notation "hH" => parameterScheme_isConnectedReductive χ hG
set_option hygiene false in
local notation "d" => galleryVertexData hG ha
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "σ" => SmoothRep.pullback (parameterHomeomorph χ) A
set_option hygiene false in
local notation "σz" => fun z : X => SmoothRep.pullback (parameterHomeomorph χ) (twistObject χ z A)
set_option hygiene false in
local notation "J" => galleryIntegralOperator hG ha K hK
set_option hygiene false in
local notation "E" => compactRepresentedGalleryEquiv hG ha K hK A
set_option hygiene false in
local notation "Reg" => ((p.regularRegion ∩ q.regularRegion) ∩ r.regularRegion : Set X)
set_option hygiene false in
local notation "U₀" => CompactInductionPicture (commonDecomposition χ x.val x.property) K A
set_option hygiene false in
local notation "U₁" => CompactInductionPicture (commonDecomposition χ w.val w.property) K A

include ha in
set_option backward.isDefEq.respectTransparency.types false in
/-- On their common regular region, the two continued operators of a
distance-additive composition agree with the direct operator up to a
fixed positive factor determined by the original quotient Haar measures. -/
theorem exists_continuedPair_comp_smul
    (hd : IsDistanceAdditive x.val y.val w.val) (hirr : A.IsIrreducible)
    (hadm : A.IsAdmissible) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ z : Reg,
      (q.presentation.continuedOperator ⟨z.val, z.property.1.2⟩).comp
          (p.presentation.continuedOperator ⟨z.val, z.property.1.1⟩) =
        (c : ℂ) • r.presentation.continuedOperator ⟨z.val, z.property.2⟩ := by
  classical
  obtain ⟨s, hs, hcomp⟩ := exists_galleryIntegralOperator_comp_smul hG ha K hK x y w hd
  let sp := continuedPairGalleryScale hG ha K hK x y hxK hyK A p
  let sq := continuedPairGalleryScale hG ha K hK y w hyK hwK A q
  let sr := continuedPairGalleryScale hG ha K hK x w hxK hwK A r
  let c := (sq.val * sp.val * s) / sr.val
  have hc : 0 < c := div_pos (mul_pos (mul_pos sq.property.1 sp.property.1) hs) sr.property.1
  have hCoeff : (sq.val : ℂ) * (sp.val : ℂ) * (s : ℂ) = (c : ℂ) * (sr.val : ℂ) := by
    have he : sq.val * sp.val * s = c * sr.val :=
      (div_mul_cancel₀ _ sr.property.1.ne').symm
    exact_mod_cast he
  have hirr' : (σ).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation (parameterHomeomorph χ)).mpr hirr
  have hadm' : (σ).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (parameterHomeomorph χ) hadm
  let vertices : Finset (GalleryVertex χ) := {x, y, w}
  obtain ⟨b, hb, hpq⟩ := exists_generic_galleryRegular hG ha vertices σ hirr' hadm'
  let O := rationalUnramifiedPrincipalOpen H hH b
  have hOo : IsOpen O := isOpen_rationalUnramifiedPrincipalOpen H hH b
  have hOd : Dense O := dense_rationalUnramifiedPrincipalOpen H hH b hb
  have hReg : IsOpen Reg :=
    (p.presentation.regularRegion_isOpen.inter q.presentation.regularRegion_isOpen).inter
      r.presentation.regularRegion_isOpen
  have hpDense := continuation_regularRegion_dense H (parameterProjection_continuous χ) hH
    p.presentation p.nonempty_region
  have hqDense := continuation_regularRegion_dense H (parameterProjection_continuous χ) hH
    q.presentation q.nonempty_region
  have hrDense := continuation_regularRegion_dense H (parameterProjection_continuous χ) hH
    r.presentation r.nonempty_region
  have hRegDense : Dense Reg := (hpDense.inter_of_isOpen_right hqDense
    q.presentation.regularRegion_isOpen).inter_of_isOpen_right hrDense r.presentation.regularRegion_isOpen
  refine ⟨c, hc, continuedComposition_eq_of_eqOn H (parameterProjection_continuous χ) hH
    p.presentation q.presentation r.presentation (c : ℂ) (hReg.inter hOo)
    (hRegDense.inter_of_isOpen_right hOd hOo).nonempty Set.inter_subset_left ?_⟩
  intro z hz
  let zp : p.regularRegion := ⟨z, hz.1.1.1⟩
  let zq : q.regularRegion := ⟨z, hz.1.1.2⟩
  let zr : r.regularRegion := ⟨z, hz.1.2⟩
  have hPQ : ∀ j ∈ vertices, ∀ k ∈ vertices, representedIsPQRegular hG (d j) (d k) (σz z) :=
    (intrinsicGalleryCoefficient_twist χ A z).symm ▸ hpq z hz.2
  have hx : x ∈ vertices := by simp [vertices]
  have hy : y ∈ vertices := by simp [vertices]
  have hw : w ∈ vertices := by simp [vertices]
  have hpq₀ := hPQ x hx y hy
  have hpq₁ := hPQ y hy w hw
  have hpq₂ := hPQ x hx w hw
  have he₀ (v : U₀) :=
    (representedContinuedPairOperator_compact_apply hG ha K hK A x y hxK hyK p zp v).symm.trans
      (DFunLike.congr_fun (sp.property.2 zp hpq₀) (E x hxK z v))
  have he₁ (v : CompactInductionPicture (commonDecomposition χ y.val y.property) K A) :=
    (representedContinuedPairOperator_compact_apply hG ha K hK A y w hyK hwK q zq v).symm.trans
      (DFunLike.congr_fun (sq.property.2 zq hpq₁) (E y hyK z v))
  have he₂ (v : U₀) :=
    (representedContinuedPairOperator_compact_apply hG ha K hK A x w hxK hwK r zr v).symm.trans
      (DFunLike.congr_fun (sr.property.2 zr hpq₂) (E x hxK z v))
  exact comp_smul_of_conjugate (E x hxK z) (E y hyK z) (E w hwK z)
    (p.presentation.continuedOperator zp) (q.presentation.continuedOperator zq)
    (r.presentation.continuedOperator zr) (J (σz z) x y).toLinearMap
    (J (σz z) y w).toLinearMap (J (σz z) x w).toLinearMap
    _ _ _ _ _ hCoeff he₀ he₁ he₂ (DFunLike.congr_fun (hcomp (σz z) hpq₀ hpq₁ hpq₂))

end Langlands.Plancherel.DynamicCommonLeviPresentations
