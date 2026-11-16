import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Langlands.Geometry.Analytic.TensorStalkBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Statement

/-! # Pointwise conditions and ordinary tensor comparison -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w}
  [NormedField K] [NormedCommRing R] [NormedCommRing S]
  [Algebra K R] [Algebra K S]

/-- Pointwise flatness can be tested over the unlocalized source. -/
theorem isFlatAtPoint_iff_flat_atPrime (f : BoundedAlgHom K R S)
    (y : BanachSpectrum S) :
    f.IsFlatAtPoint y ↔
      (letI : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
       Module.Flat R (Localization.AtPrime y.kernel)) := by
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let p := (BanachSpectrum.comap f.toBoundedRingHom y).kernel
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime y.kernel) :=
    (Localization.localRingHom p y.kernel f.toAlgHom.toRingHom
      (f.kernel_comap y)).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime y.kernel) :=
    .of_algebraMap_eq fun x =>
      (Localization.localRingHom_to_map p y.kernel f.toAlgHom.toRingHom
        (f.kernel_comap y) x).symm
  change Module.Flat (Localization.AtPrime p) (Localization.AtPrime y.kernel) ↔ _
  exact Module.flat_iff_of_isLocalization
    (S := Localization.AtPrime p) (p := p.primeCompl) (Localization.AtPrime y.kernel)

end BoundedAlgHom

namespace TensorStalkBaseChange

open scoped TensorProduct

variable {R : Type u} {S : Type v} {T : Type w} {D : Type z}
  [CommRing R] [CommRing S] [CommRing T] [CommRing D]
  [Algebra R S] [Algebra R T] [Algebra T D]

/-- The primewise tensor flatness result transported through a coefficient
algebra equivalence. -/
theorem flat_atPrime_of_equiv (e : T ⊗[R] S ≃ₐ[T] D) (p : Ideal D) [p.IsPrime]
    (hflat : Module.Flat R (Localization.AtPrime
      ((p.comap e.toRingHom).comap
        (Algebra.TensorProduct.includeRight (R := R) (A := T)).toRingHom))) :
    Module.Flat T (Localization.AtPrime p) := by
  let P := p.comap e.toRingHom
  have : P.IsPrime := Ideal.IsPrime.comap _
  have : Module.Flat T (Localization.AtPrime P) := flat_atPrime P hflat
  exact Module.Flat.of_linearEquiv (Localization.localAlgEquiv P p e rfl).symm.toLinearEquiv

/-- The primewise tensor unramifiedness result transported through a
coefficient algebra equivalence. -/
theorem formallyUnramified_atPrime_of_equiv (e : T ⊗[R] S ≃ₐ[T] D)
    (p : Ideal D) [p.IsPrime]
    (hunr : Algebra.FormallyUnramified R (Localization.AtPrime
      ((p.comap e.toRingHom).comap
        (Algebra.TensorProduct.includeRight (R := R) (A := T)).toRingHom))) :
    Algebra.FormallyUnramified T (Localization.AtPrime p) := by
  let P := p.comap e.toRingHom
  have : P.IsPrime := Ideal.IsPrime.comap _
  have : Algebra.FormallyUnramified T (Localization.AtPrime P) :=
    formallyUnramified_atPrime P hunr
  exact Algebra.FormallyUnramified.of_equiv (Localization.localAlgEquiv P p e rfl)

end TensorStalkBaseChange

namespace PresentedAffinoidAlgebra.AffinoidPushout

open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- The canonical ordinary tensor comparison as a ring equivalence whenever
its underlying map is bijective. -/
def tensorComparisonEquiv (h : Function.Bijective (tensorComparison f g)) :
    algebraicBaseChange f g ≃+* algebra f g :=
  RingEquiv.ofBijective (tensorComparison f g) h

omit [CompleteSpace K] in
/-- Étaleness at an ordinary point is preserved by the actual affinoid
pushout of a finite type map when its ordinary tensor comparison is bijective. -/
theorem rightMap_isEtaleAtPoint_of_tensorComparison
    (h : Function.Bijective (tensorComparison f g))
    (hf : f.toAlgHom.toRingHom.FiniteType)
    (x : BanachSpectrum (algebra f g))
    (hx : f.IsEtaleAtPoint (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x)) :
    (rightMap f g).IsEtaleAtPoint x := by
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let e : C ⊗[A] B ≃ₐ[C] algebra f g :=
    { tensorComparisonEquiv f g h with
      commutes' := tensorComparison_tensorLeft f g }
  have : Algebra.FiniteType A B := hf
  have : Algebra.FiniteType C (C ⊗[A] B) := inferInstance
  have hr : (rightMap f g).toAlgHom.toRingHom.FiniteType :=
    Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  let q := (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x).kernel
  have hq : (x.kernel.comap e.toRingHom).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom = q := by
    ext b
    change tensorComparison f g (tensorRight f g b) ∈ x.kernel ↔ leftMap f g b ∈ x.kernel
    rw [tensorComparison_tensorRight]
  have hqp : (⟨(x.kernel.comap e.toRingHom).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom,
      inferInstance⟩ : PrimeSpectrum B) = ⟨q, inferInstance⟩ := PrimeSpectrum.ext hq
  have hflat : Module.Flat A (Localization.AtPrime q) :=
    (f.isFlatAtPoint_iff_flat_atPrime _).1 hx.1
  have hunr : Algebra.FormallyUnramified A (Localization.AtPrime q) :=
    (f.isUnramifiedAtPoint_iff_isUnramifiedAt hf _).1 hx.2
  constructor
  · apply ((rightMap f g).isFlatAtPoint_iff_flat_atPrime x).2
    apply TensorStalkBaseChange.flat_atPrime_of_equiv e x.kernel
    exact (congrArg (fun p : PrimeSpectrum B =>
      Module.Flat A (Localization.AtPrime p.asIdeal)) hqp).mpr hflat
  · apply ((rightMap f g).isUnramifiedAtPoint_iff_isUnramifiedAt hr x).2
    apply TensorStalkBaseChange.formallyUnramified_atPrime_of_equiv e x.kernel
    exact (congrArg (fun p : PrimeSpectrum B =>
      Algebra.FormallyUnramified A (Localization.AtPrime p.asIdeal)) hqp).mpr hunr

end PresentedAffinoidAlgebra.AffinoidPushout

end Langlands.Analytic
