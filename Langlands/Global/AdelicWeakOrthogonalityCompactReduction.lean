import Langlands.Global.AdelicFiniteCompactOrthogonality
import Langlands.Global.AdelicFiniteCompactPairingComparisonProof
import Langlands.Global.AdelicFiniteCompactWavePacket
import Langlands.Global.AdelicLeviPairingCompactTranslation
import Langlands.Global.AdelicSingleFormRelativeWavePacketTest
import Langlands.Global.AdelicStandardWavePacketCompactTranslation
import Langlands.Global.AdelicWeakConstantTermDirectness
import Langlands.Global.AdelicWeakConstantTermRightTranslation
import Langlands.Global.AdelicWavePacketSiegelDecayReduction

/-! # Reduction of weak constant-term orthogonality to a reference compact -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ContDiff

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic

/-- Weak constant-term orthogonality tested only by single-form standard packets,
for one reference compact for each compatible standard parabolic family. -/
def WavePacketWeakConstantTermReferenceCompactStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G),
  ∃ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p fam.bot) K),
    IsMaximalCompactSubgroup F G K ∧
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho → ∀ Φ : AdelicGroupPoints F G → ℂ,
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    (∀ Θ : AdelicGroupPoints F G → ℂ, fam.IsSingleFormWavePacket K rho hsmooth hcalc Θ →
      ∫ y, Φ y.out * starRingEnd ℂ (Θ y.out) ∂(rationalQuotientHaarMeasure F G) = 0) →
    ∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F G → ℂ),
      fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
      fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc J ψ

/-- The conclusion for all maximal Iwasawa compacts follows from the reference case
and imaginary-axis continuation of the cut inducing forms. -/
def WavePacketWeakConstantTermCompactReductionStatement : Prop :=
  WavePacketWeakConstantTermReferenceCompactStatement →
  EisensteinImaginaryContinuationStatement →
  WavePacketWeakConstantTermOrthogonalityStatement

/-- Conjugate the reference compact at infinity and compare with the given compact.
Haar-invariant right translation moves the inverse translate to the tested form. -/
theorem wavePacketWeakConstantTerm_of_referenceCompact :
    WavePacketWeakConstantTermCompactReductionStatement := by
  intro href hcont F _ _ G _ _ _ hG K N d rho hsmooth hcalc hmax hclosed fam hK μG Φ hΦ htest
  obtain ⟨K₀, hK₀, hmax₀, hRef⟩ := href F G fam
  obtain ⟨a, ha⟩ := InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy F G
    (K₀.comap (ofInfinite F G).toMonoidHom) (K.comap (ofInfinite F G).toMonoidHom) hG
    hmax₀.isMaximalCompact_comap_ofInfinite hmax.isMaximalCompact_comap_ofInfinite
  let t := ofInfinite F G a
  let L := K₀.map (MulAut.conj t).toMonoidHom
  let hL : IsIwasawaCompact (fam.p fam.bot) L := by
    simpa only [L, inv_inv] using hK₀.conjInv t⁻¹
  have hmaxL := hmax₀.map_conj t
  have hinf : L.map (infinite F G).toMonoidHom = K.map (infinite F G).toMonoidHom := by
    change (K₀.map (MulAut.conj (ofInfinite F G a)).toMonoidHom).map (infinite F G).toMonoidHom = _
    rw [map_infinite_map_conj_ofInfinite, ← hmax₀.comap_ofInfinite_eq_map_infinite,
      ha, hmax.comap_ofInfinite_eq_map_infinite]
  have hcomap : L.comap (ofInfinite F G).toMonoidHom = K.comap (ofInfinite F G).toMonoidHom := by
    rw [hmaxL.comap_ofInfinite_eq_map_infinite, hmax.comap_ofInfinite_eq_map_infinite, hinf]
  have hBack : L.map (MulAut.conj (ofInfinite F G a⁻¹)).toMonoidHom = K₀ := by
    change (K₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (ofInfinite F G a⁻¹)).toMonoidHom = K₀
    rw [map_inv, Subgroup.map_map]
    have he : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro g
      change t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g
      group
    change K₀.map ((MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom) = K₀
    rw [he, Subgroup.map_id]
  let Φ₀ (g : AdelicGroupPoints F G) := Φ (g * ofInfinite F G a⁻¹)
  have hΦL : IsLogSquareIntegrableAutomorphicForm F G L rho hsmooth hcalc Φ :=
    ⟨hcomap.symm ▸ hΦ.1, hΦ.2⟩
  have htranslated := adelicWeakConstantTermRightTranslation F G hG fam L rho hsmooth hcalc a⁻¹ Φ hΦL
  have hΦ₀ : IsLogSquareIntegrableAutomorphicForm F G K₀ rho hsmooth hcalc Φ₀ :=
    hBack ▸ htranslated.1
  have htest₀ (Θ : AdelicGroupPoints F G → ℂ) (hΘ : fam.IsSingleFormWavePacket K₀ rho hsmooth hcalc Θ) :
      ∫ y, Φ₀ y.out * starRingEnd ℂ (Θ y.out) ∂(rationalQuotientHaarMeasure F G) = 0 := by
    obtain ⟨J, close, hK₀J, r, mono, finite, mono', hA, hT, φ, n, e, c, E, D,
      hφ, hc, hcpt, hDimag, hE, hreg, hΘeq⟩ := hΘ
    let : IsClosedImmersion (fam.p J).hom.hom.left := close
    let : Mono r.data.i.hom.hom.left := mono
    let : Fintype (relativeWeylGroup r.data.i) := finite
    let : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := mono'
    let hLJ := fam.isIwasawaCompact_of_bot hL J
    let hKJ := fam.isIwasawaCompact_of_bot hK J
    obtain ⟨hφ', c', E', hc', hcpt', hE', hreg', heq⟩ :=
      fam.standardWavePacketCompactTranslation J r hA hT hK₀J a hLJ
        hφ e c E D hc hcpt hE hreg
    have hΘK : IsWavePacket F G K rho hsmooth hcalc (fun g => Θ (g * t)) := by
      have hpacket := finiteCompactStandardWavePacketTransfer finiteCompactPairingComparison hcont F G fam J r hA hT
        L K hLJ hKJ hmaxL hmax hinf rho hsmooth hcalc _ hclosed hφ' E' D hDimag hE' hreg' e c' hc' hcpt'
      have heq' : (fun g => Θ (g * t)) =
          (fun g => ∫ z, c' z * E' (imaginaryParameter F (fam.P J) (e z)) g ∂(spectralMeasure n)) := by
        rw [hΘeq]
        funext g
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => (heq z g).symm)
      exact heq'.symm ▸ hpacket
    let Γ := rationalSubgroup F G
    let Q := RationalQuotient F G
    let f (y : Q) := Φ y.out * starRingEnd ℂ (Θ (y.out * t))
    let q := LeftCosetSpace.rightTranslateHomeomorph Γ (ofInfinite F G a⁻¹)
    let := adelicHaarUnimodularity.2 F G hG
    have hInv : IsLeftInvariantUnder F G Γ (fun g => Θ (g * t)) := hΘK.leftRationalInvariant hG
    have hq : MeasurePreserving q (rationalQuotientHaarMeasure F G) (rationalQuotientHaarMeasure F G) :=
      measurePreserving_rightTranslate_rationalQuotientHaarMeasure F G (ofInfinite F G a⁻¹)
    have hf (y : Q) : f (q y) = Φ₀ y.out * starRingEnd ℂ (Θ y.out) := by
      change f (LeftCosetSpace.rightTranslate Γ (ofInfinite F G a⁻¹) y) = _
      rw [rationalQuotient_rightTranslate_eq_mk_out_mul]
      unfold f
      rw [leftInvariant_mk_out hΦ.1.1,
        show Θ ((LeftCosetSpace.mk Γ (y.out * ofInfinite F G a⁻¹)).out * t) =
          Θ ((y.out * ofInfinite F G a⁻¹) * t) from
            leftInvariant_mk_out hInv _]
      simp only [Φ₀, map_inv, t, inv_mul_cancel_right]
    calc
      _ = ∫ y, f (q y) ∂(rationalQuotientHaarMeasure F G) :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => (hf y).symm)
      _ = ∫ y, f y ∂(rationalQuotientHaarMeasure F G) := hq.integral_comp q.measurableEmbedding f
      _ = 0 := htest _ hΘK
  intro J ψ hψ
  let : IsClosedImmersion (fam.p J).hom.hom.left := fam.isClosedImmersion_p J
  let hKJ := fam.isIwasawaCompact_of_bot hK J
  let hLJ := fam.isIwasawaCompact_of_bot hL J
  let ψ₀ (g : AdelicGroupPoints F G) := ψ (g * ofInfinite F G a⁻¹)
  have hψL : fam.IsWeakConstantTerm hsmooth (L.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ :=
    hcomap.symm ▸ hψ
  have hψ₀ : fam.IsWeakConstantTerm hsmooth (K₀.comap (ofInfinite F G).toMonoidHom) rho J Φ₀ ψ₀ :=
    hBack ▸ htranslated.2 J ψ hψL
  have hO₀ := hRef rho hsmooth hcalc hclosed Φ₀ hΦ₀ htest₀ J ψ₀ hψ₀
  have hO' (K' : Subgroup (AdelicGroupPoints F G)) (hK' : IsCompact (K' : Set (AdelicGroupPoints F G)))
      (he : K' = K₀) : fam.IsSquareIntegrableOrthogonal K' hK' rho hsmooth hcalc J ψ₀ := by
    subst K'
    exact hO₀
  have hLtransfer := StandardParabolicFamily.leviPairingCompactTranslation F G fam J L hLJ a⁻¹
    rho hsmooth hcalc hmaxL
  have hO := hLtransfer.2 ψ hψL.isAutomorphicOn.1
    (hO' _ (hmaxL.map_conj (ofInfinite F G a⁻¹)).1 hBack)
  exact (finiteCompactLeviOrthogonalityTransfer finiteCompactPairingComparison F G fam J K L
    hKJ hLJ hmax hmaxL hinf.symm rho hsmooth hcalc ψ hψ.isAutomorphicOn.2.1.1
    hψ.isAutomorphicOn.1).mpr hO

end Langlands.Global
