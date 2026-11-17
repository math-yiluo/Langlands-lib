import Langlands.Geometry.Analytic.AffinoidPointwiseBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat

/-! # The open pointwise étale locus of a finite affinoid map -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.Analytic

open Set

namespace AlgebraicEtaleLocus

open Algebra

private theorem isEtaleAt_of_flat_localization
    {R : Type v} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [Algebra.IsUnramifiedAt R q]
    (hflat : Module.Flat R (Localization.AtPrime q)) : Algebra.IsEtaleAt R q := by
  let p := q.under R
  have : q.LiesOver p := inferInstance
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
    (M := algebraMapSubmonoid S p.primeCompl) (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq
        ⟨algebraMap _ _ x, by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
      (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : Module.Flat Rp Sq :=
    (Module.flat_iff_of_isLocalization (S := Rp) (p := p.primeCompl) Sq).mpr hflat
  have : Algebra.FormallyUnramified Rp Sq :=
    Algebra.FormallyUnramified.localization_base p.primeCompl
  have : Algebra.EssFiniteType R Sq := .comp _ S _
  have : Algebra.EssFiniteType Rp Sq := .of_comp R _ _
  have : Algebra.FormallyUnramified (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) := inferInstance
  have : Algebra.EssFiniteType (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) := inferInstance
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid Sp q.primeCompl)
  have : Algebra.FormallyEtale Rp Sq :=
    ⟨inferInstance, inferInstance⟩
  exact Algebra.FormallyEtale.comp R Rp Sq

private theorem flat_localization_of_isEtaleAt
    {R : Type v} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [Algebra.IsEtaleAt R q] : Module.Flat R (Localization.AtPrime q) := by
  obtain ⟨r, hr, hret⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) q
  let Sr := Localization.Away r
  let Sq := Localization.AtPrime q
  have : Algebra.Etale R Sr := hret
  have hle : Submonoid.powers r ≤ q.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact q.primeCompl.pow_mem hr n
  let e : Sr →ₐ[S] Sq := IsLocalization.liftAlgHom
    (M := Submonoid.powers r) (f := Algebra.ofId _ _) (by
      intro x
      exact IsLocalization.map_units (M := q.primeCompl) Sq ⟨x.val, hle x.property⟩)
  algebraize [e.toRingHom]
  have : IsScalarTower R Sr Sq := .to₁₃₄ _ S _ _
  have : IsLocalization (algebraMapSubmonoid Sr q.primeCompl) Sq :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers r) q.primeCompl hle
  have : Module.Flat Sr Sq := IsLocalization.flat _ (algebraMapSubmonoid Sr q.primeCompl)
  exact Module.Flat.trans R Sr Sq

end AlgebraicEtaleLocus

namespace BanachSpectrum

variable {S : Type w} [NormedCommRing S]

/-- The prime kernel of an ordinary bounded multiplicative spectrum point. -/
def primePoint (x : BanachSpectrum S) : PrimeSpectrum S :=
  ⟨x.kernel, inferInstance⟩

/-- Kernel primes depend continuously on ordinary spectrum points. -/
theorem continuous_primePoint : Continuous (primePoint (S := S)) := by
  apply continuous_iff_isClosed.mpr
  intro Z hZ
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  have he : primePoint ⁻¹' PrimeSpectrum.zeroLocus I =
      ⋂ a ∈ I, {x : BanachSpectrum S | x a = 0} := by
    ext x
    simp only [mem_preimage, PrimeSpectrum.mem_zeroLocus, mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_eq (evaluation a).continuous continuous_const

end BanachSpectrum

namespace BoundedAlgHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B)

/-- The ordinary pointwise étale locus of the actual bounded affinoid map. -/
def pointwiseEtaleLocus : Set (BanachSpectrum B) :=
  {x | f.IsEtaleAtPoint x}

/-- For finite-type affinoid maps, pointwise flatness and unramifiedness are
equivalent to membership in the algebraic étale locus of the kernel prime. -/
theorem pointwiseEtaleLocus_eq_prime_preimage
    (hf : f.toAlgHom.toRingHom.FiniteType) :
    f.pointwiseEtaleLocus =
      (letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
       BanachSpectrum.primePoint ⁻¹' Algebra.etaleLocus A B) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  have : Algebra.FiniteType A B := hf
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp hf
  ext x
  change f.IsEtaleAtPoint x ↔ Algebra.IsEtaleAt A x.kernel
  constructor
  · intro hx
    have : Algebra.IsUnramifiedAt A x.kernel :=
      (f.isUnramifiedAtPoint_iff_isUnramifiedAt hf x).mp hx.2
    exact AlgebraicEtaleLocus.isEtaleAt_of_flat_localization x.kernel
      ((f.isFlatAtPoint_iff_flat_atPrime x).mp hx.1)
  · intro hx
    have : Algebra.IsEtaleAt A x.kernel := hx
    exact ⟨(f.isFlatAtPoint_iff_flat_atPrime x).mpr
      (AlgebraicEtaleLocus.flat_localization_of_isEtaleAt x.kernel),
      (f.isUnramifiedAtPoint_iff_isUnramifiedAt hf x).mpr inferInstance⟩

/-- Finite-type actual affinoid maps have an open pointwise étale locus. -/
theorem isOpen_pointwiseEtaleLocus (hf : f.toAlgHom.toRingHom.FiniteType) :
    IsOpen f.pointwiseEtaleLocus := by
  rw [f.pointwiseEtaleLocus_eq_prime_preimage hf]
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  have : Algebra.FiniteType A B := hf
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp hf
  exact Algebra.isOpen_etaleLocus.preimage BanachSpectrum.continuous_primePoint

end BoundedAlgHom

end Langlands.Analytic
