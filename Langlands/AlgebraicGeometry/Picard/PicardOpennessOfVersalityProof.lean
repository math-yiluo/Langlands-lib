import Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Necessity
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartFrames
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Presentation
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.AffineChart
import Langlands.AlgebraicGeometry.Picard.PointFiberArtinianLifting

/-! # Openness of versality for actual Picard families: proof -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation PicardGroupoid OpennessOfVersality
open RelativeAffineSections

/-- A field point of an affine chart lies in the basic open of `g` exactly when `g` does not
vanish at it. -/
lemma affineBaseMap_mem_basicOpen {R A K : Type u} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] (χ : A →ₐ[R] K) (g : A) (z : (ArtinianTest.residueBase R K).left) :
    (affineBaseMap χ).left z ∈ PrimeSpectrum.basicOpen g ↔ χ g ≠ 0 := by
  change g ∉ (PrimeSpectrum.comap χ.toRingHom z).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.eq_bot_of_prime (z : PrimeSpectrum K).asIdeal, Ideal.mem_bot]
  rfl

/-- **Openness of versality** for actual Picard families of proper flat schemes over
noetherian rings. -/
theorem picardOpennessOfVersality : PicardOpennessOfVersalityStatement.{u} := by
  intro R _ _ X hprop hflat U hU L u₀ K _ _ p e hp hpft hv
  haveI : IsProper X.hom := hprop
  haveI : Flat X.hom := hflat
  haveI : LocallyOfFiniteType U.hom := hU
  haveI : LocallyOfFiniteType p.left := hpft
  haveI : SurjectiveOnStalks p.left := by
    rw [hp]
    infer_instance
  -- an affine chart through the point with a surjective residue map
  obtain ⟨A₀, _, _, ι, χ₀, hι, hft, hχ₀, hp₀⟩ := exists_affineChart U p
  haveI := hι
  haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R A₀
  set L₀ := restrictBundle X.hom L ι with hL₀
  have hv₀ : ArtinianChartVersality.IsFormallyVersalAt X.hom L₀
      (affineBaseMap χ₀ : ArtinianTest.residueBase R K ⟶ affineBase R A₀) :=
    PointFiberArtinianLifting.isFormallyVersalAt_restrictBundle X.hom L ι _ (by rw [hp₀]; exact hv)
  -- a presentation and the chart data
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  haveI : CompactSpace (relSpace X.hom (Presentation.Pres s)) := by
    have := isProper_relProj X.hom (Presentation.Pres s)
    exact QuasiCompact.compactSpace_of_compactSpace (relProj X.hom (Presentation.Pres s))
  have hπ := Presentation.presMap_surjective hs
  obtain ⟨Kc, fr, hfr, g, hge, hg⟩ := exists_chartFrames X.hom hπ
    (Presentation.ker_isNilpotent s) L₀
  letI := Presentation.qModule hs
  haveI := Presentation.qModule_isScalarTower hs
  haveI := Presentation.qModule_finite hs
  let jQ : RingHom.ker (algebraMap (Presentation.Pres s) A₀) →ₗ[Presentation.Pres s]
    Presentation.Pres s := (RingHom.ker (algebraMap (Presentation.Pres s) A₀)).subtype
  have hjQ : ∀ a, a ∈ RingHom.ker (algebraMap (Presentation.Pres s) A₀) ↔ ∃ x, jQ x = a :=
    fun a => ⟨fun h => ⟨⟨a, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  have hjQsq : ∀ x y, jQ x * jQ y = 0 := fun x y =>
    Presentation.ker_mul_eq_zero s _ x.2 _ y.2
  have hPlift : ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (q : A →ₐ[R] B), Function.Surjective q →
        (∀ a ∈ RingHom.ker q.toRingHom, ∀ b ∈ RingHom.ker q.toRingHom, a * b = 0) →
          ∀ χ : A₀ →ₐ[R] B, ∃ ρ : Presentation.Pres s →ₐ[R] A,
            q.comp ρ = χ.comp (IsScalarTower.toAlgHom R (Presentation.Pres s) A₀) :=
    fun q hq hsq χ => Presentation.exists_lift s q hq hsq χ
  -- necessity at the point and openness of the obstruction condition
  have hk := hOneVanishes_of_isFormallyVersalAt X.hom Kc g hπ jQ Subtype.val_injective hjQ
    hg (Presentation.presDer s) (fun M _ _ _ _ _ _ δ => Presentation.exists_presDer_factor s δ)
    fr hfr hge χ₀ hχ₀ hv₀
  letI : Algebra A₀ K := χ₀.toRingHom.toAlgebra
  obtain ⟨g₀, hg₀, hvers⟩ := exists_versal_basicOpen X.hom Kc g hπ jQ Subtype.val_injective hjQ
    hjQsq hg (Presentation.presDer s) fr hfr hge hPlift hk
  -- the open neighbourhood
  let pt : (ArtinianTest.residueBase R K).left := (default : PrimeSpectrum K)
  have hpt : p.left pt = u₀ := by
    rw [hp]
    exact Scheme.fromSpecResidueField_apply u₀ ((Spec.map e.hom) pt)
  refine ⟨ι.left ''ᵁ PrimeSpectrum.basicOpen g₀, ?_, ?_⟩
  · rw [← hpt, ← hp₀]
    exact ⟨(affineBaseMap χ₀).left pt, (affineBaseMap_mem_basicOpen χ₀ g₀ pt).mpr hg₀, rfl⟩
  · intro K' _ _ p' _ hrange
    have hrange' : Set.range p'.left ⊆ Set.range ι.left := fun _ hx => by
      obtain ⟨y, -, hy⟩ := hrange hx
      exact ⟨y, hy⟩
    obtain ⟨χ', hχ'⟩ := exists_affineBaseMap_eq (R := R) (A := A₀) (B := K')
      (pointLift ι p' hrange')
    have hcomp : affineBaseMap χ' ≫ ι = p' := by
      rw [hχ']
      exact pointLift_comp ι p' hrange'
    have hne : χ' g₀ ≠ 0 := by
      let pt' : (ArtinianTest.residueBase R K').left := (default : PrimeSpectrum K')
      obtain ⟨y, hy, hyeq⟩ := hrange ⟨pt', rfl⟩
      have hinj := ι.left.isOpenEmbedding.injective
      have h1 := congrArg (fun φ : ArtinianTest.residueBase R K' ⟶ U => φ.left pt') hcomp
      have : y = (affineBaseMap χ').left pt' := hinj (hyeq.trans h1.symm)
      rw [this] at hy
      exact (affineBaseMap_mem_basicOpen χ' g₀ pt').mp hy
    have h : ArtinianChartVersality.IsFormallyVersalAt X.hom L
        ((affineBaseMap χ' : ArtinianTest.residueBase R K' ⟶ affineBase R A₀) ≫ ι) :=
      ArtinianChartTestReduction.isFormallyVersalAt_of_restrictBundle X.hom L ι _
        (by exact hvers K' χ' hne)
    rw [← hcomp]
    exact @h

end Langlands.AlgebraicGeometry.Picard
