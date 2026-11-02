import Langlands.CommutativeAlgebra.SmoothValuationLocalRegularity
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth valuation stalks and their localized Picard groups -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {A B : Type u} [CommRing A] [CommRing B]

/-- A ring equivalence transports triviality of the module Picard group. -/
theorem subsingleton_pic_of_ringEquiv (e : A ≃+* B)
    [Subsingleton (CommRing.Pic A)] : Subsingleton (CommRing.Pic B) := by
  constructor
  intro x y
  have h : CommRing.Pic.mapRingHom e.symm.toRingHom x =
      CommRing.Pic.mapRingHom e.symm.toRingHom y := Subsingleton.elim _ _
  have hc : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by
    ext b
    exact e.apply_symm_apply b
  simpa only [CommRing.Pic.mapRingHom_mapRingHom, hc,
    CommRing.Pic.mapRingHom_id_apply] using congrArg (CommRing.Pic.mapRingHom e.toRingHom) h

/-- The Picard vanishing theorem for a regular coherent local ring applies
to any actual algebra model of a localization. -/
theorem subsingleton_pic_of_isLocalization_of_regularLocal
    [IsLocalRing A] (hA : FinitelyPresentedRegularRing A)
    (M : Submonoid A) [Algebra A B] [IsLocalization M B] :
    Subsingleton (CommRing.Pic B) := by
  have : Subsingleton (CommRing.Pic (Localization M)) :=
    subsingleton_pic_localization_of_finitelyPresented_finite_projectiveDimension hA.1 hA.2 M
  exact subsingleton_pic_of_ringEquiv (IsLocalization.algEquiv M (Localization M) B).toRingEquiv

end Langlands.CommutativeAlgebra

namespace Langlands.AlgebraicGeometry

open Langlands.CommutativeAlgebra

/-- An actual smooth algebra and prime whose local ring is the specified
ring. This retains a concrete algebra model for applying local algebra. -/
structure SmoothStalkModel (R A : Type u) [CommRing R] [CommRing A] where
  chartRing : Type u
  [commRing : CommRing chartRing]
  [coefficientAlgebra : Algebra R chartRing]
  smooth : Algebra.Smooth R chartRing
  prime : Ideal chartRing
  [primeIsPrime : prime.IsPrime]
  localEquiv : Localization.AtPrime prime ≃+* A

/-- Choose a smooth affine chart through a point and its actual local-ring
identification with the scheme stalk. -/
def smoothStalkModel (R : Type u) [CommRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] (x : X) :
    SmoothStalkModel R (X.presheaf.stalk x) := by
  classical
  exact Classical.choice (show Nonempty (SmoothStalkModel R (X.presheaf.stalk x)) from by
    obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    let U := X.affineCover.X i
    let q := X.affineCover.f i ≫ p
    have : Smooth q := inferInstance
    let g : CommRingCat.of R ⟶ Γ(U, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop
    have hg : g.hom.Smooth := RingHom.Smooth.comp
      (RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective)
      (HasRingHomProperty.appTop @Smooth q inferInstance)
    algebraize [g.hom]
    have hSmooth : Algebra.Smooth R Γ(U, ⊤) := RingHom.smooth_algebraMap.mp hg
    let P := ((isAffineOpen_top U).primeIdealOf ⟨y, trivial⟩).asIdeal
    let := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, trivial⟩ : (⊤ : U.Opens))
    have := (isAffineOpen_top U).isLocalization_stalk ⟨y, trivial⟩
    let e : Localization.AtPrime P ≃+* U.presheaf.stalk y :=
      (IsLocalization.algEquiv P.primeCompl
        (Localization.AtPrime P) (U.presheaf.stalk y)).toRingEquiv
    let e' : U.presheaf.stalk y ≃+* X.presheaf.stalk ((X.affineCover.f i) y) :=
      (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv.symm
    exact ⟨{
      chartRing := Γ(U, ⊤)
      commRing := inferInstance
      coefficientAlgebra := inferInstance
      smooth := hSmooth
      prime := P
      primeIsPrime := inferInstance
      localEquiv := e.trans e' }⟩)

/-- A model over an arbitrary valuation domain proves regularity of the
specified actual ring, in the finitely presented module sense. -/
theorem SmoothStalkModel.regular
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [ValuationRing R]
    (d : SmoothStalkModel R A) : FinitelyPresentedRegularRing A := by
  let := d.commRing
  let := d.coefficientAlgebra
  let := d.primeIsPrime
  let := d.smooth
  exact finitelyPresentedRegularRing_of_ringEquiv d.localEquiv
    (finitelyPresentedRegularRing_atPrime_of_smoothAt_of_valuationRing
      (R := R) d.prime)

/-- Every actual stalk of a smooth scheme over an arbitrary valuation
domain is coherent and regular in the finite-projective-dimension sense. -/
theorem finitelyPresentedRegularRing_stalk_of_smooth_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] (x : X) :
    FinitelyPresentedRegularRing (X.presheaf.stalk x) :=
  (smoothStalkModel R p x).regular

/-- All actual algebra models of localizations of a smooth valuation stalk
have trivial module Picard group. -/
theorem subsingleton_pic_stalk_localization_of_smooth_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] (x : X)
    (M : Submonoid (X.presheaf.stalk x))
    (B : Type u) [CommRing B] [Algebra (X.presheaf.stalk x) B] [IsLocalization M B] :
    Subsingleton (CommRing.Pic B) :=
  subsingleton_pic_of_isLocalization_of_regularLocal
    (finitelyPresentedRegularRing_stalk_of_smooth_of_valuationRing R p x) M

/-- The corresponding actual invertible module admits a rank-one
trivialization over the chosen localization model. -/
theorem nonempty_linearEquiv_invertible_stalk_localization_of_smooth_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] (x : X)
    (M : Submonoid (X.presheaf.stalk x))
    (B : Type u) [CommRing B] [Algebra (X.presheaf.stalk x) B] [IsLocalization M B]
    (N : Type u) [AddCommGroup N] [Module B N] [Module.Invertible B N] :
    Nonempty (N ≃ₗ[B] B) := by
  have : Subsingleton (CommRing.Pic B) :=
    subsingleton_pic_stalk_localization_of_smooth_of_valuationRing R p x M B
  exact Module.Invertible.free_iff_linearEquiv.mp inferInstance

end Langlands.AlgebraicGeometry
