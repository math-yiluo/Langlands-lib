import Langlands.Geometry.Analytic.TensorStalkReflection

/-! # Pointwise reflection through actual affinoid pushouts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

open TensorProduct
open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

omit [CompleteSpace K] in
/-- A bijective ordinary tensor comparison transfers finite type to the
actual second pushout leg. -/
theorem rightMap_finiteType_of_tensorComparison
    (h : Function.Bijective (tensorComparison f g))
    (hf : f.toAlgHom.toRingHom.FiniteType) :
    (rightMap f g).toAlgHom.toRingHom.FiniteType := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let e : C ⊗[A] B ≃ₐ[C] algebra f g :=
    { tensorComparisonEquiv f g h with
      commutes' := tensorComparison_tensorLeft f g }
  have : Algebra.FiniteType A B := hf
  exact Algebra.FiniteType.of_surjective e.toAlgHom e.surjective

omit [CompleteSpace K] in
/-- Pointwise étaleness reflects from the actual affinoid pushout when the
ordinary tensor comparison is bijective and both domain structural maps
are algebraically flat. -/
theorem isEtaleAtPoint_of_rightMap_of_tensorComparison
    (h : Function.Bijective (tensorComparison f g))
    (hf : f.toAlgHom.toRingHom.FiniteType)
    (hg : g.toAlgHom.toRingHom.Flat)
    (hl : (leftMap f g).toAlgHom.toRingHom.Flat)
    (x : BanachSpectrum (algebra f g))
    (hx : (rightMap f g).IsEtaleAtPoint x) :
    f.IsEtaleAtPoint (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra B (algebra f g) := (leftMap f g).toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let : Algebra A (algebra f g) :=
    ((rightMap f g).comp g).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower A C (algebra f g) := .of_algebraMap_eq' rfl
  have : IsScalarTower A B (algebra f g) := .of_algebraMap_eq fun a =>
    congrArg (fun q : BoundedAlgHom K A (algebra f g) => q a) (condition f g).symm
  let e : C ⊗[A] B ≃ₐ[C] algebra f g :=
    { tensorComparisonEquiv f g h with
      commutes' := tensorComparison_tensorLeft f g }
  have : Algebra.IsPushout A C B (algebra f g) := by
    constructor
    change Function.Bijective _
    convert e.bijective using 1
    rfl
  have : Module.Flat A C := hg
  have : Module.Flat B (algebra f g) := hl
  have : Algebra.FiniteType A B := hf
  have hr : (rightMap f g).toAlgHom.toRingHom.FiniteType :=
    Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  have hflat : Module.Flat C (Localization.AtPrime x.kernel) :=
    ((rightMap f g).isFlatAtPoint_iff_flat_atPrime x).1 hx.1
  have hunr : Algebra.FormallyUnramified C (Localization.AtPrime x.kernel) :=
    ((rightMap f g).isUnramifiedAtPoint_iff_isUnramifiedAt hr x).1 hx.2
  have href := TensorStalkBaseChange.etale_atPrime_reflect
    (R := A) (S := B) (T := C) x.kernel hflat hunr
  constructor
  · exact (f.isFlatAtPoint_iff_flat_atPrime _).2 href.1
  · exact (f.isUnramifiedAtPoint_iff_isUnramifiedAt hf _).2 href.2

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
