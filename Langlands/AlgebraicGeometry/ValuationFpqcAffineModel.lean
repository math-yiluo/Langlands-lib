import Langlands.AlgebraicGeometry.AlgClosedValuationEtaleAffineness
import Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent
import Langlands.CommutativeAlgebra.ValuationFiniteFreePresentation
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraically closed valuation covers and actual affine etale models -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- An actual faithfully flat affine cover of a valuation spectrum by the
spectrum of a valuation subring of an algebraically closed field. -/
structure AlgClosedValuationFpqcCover (R : CommRingCat.{u}) where
  closure : Type u
  [field : Field closure]
  [algClosed : IsAlgClosed closure]
  valuation : ValuationSubring closure
  projection : Spec (CommRingCat.of valuation) ⟶ Spec R
  flat : Flat projection
  surjective : Surjective projection

attribute [instance] AlgClosedValuationFpqcCover.field AlgClosedValuationFpqcCover.algClosed

/-- Every valuation domain admits an actual algebraically closed valuation
fpqc cover. -/
theorem nonempty_algClosedValuationFpqcCover
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R] :
    Nonempty (AlgClosedValuationFpqcCover R) := by
  let K := FractionRing R
  let L := AlgebraicClosure K
  let ι : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hι : Function.Injective ι :=
    (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  obtain ⟨A, hA, hlocal⟩ := IsLocalRing.exists_factor_valuationRing ι
  let β : R →+* A := ι.codRestrict A.toSubring hA
  let : Algebra R A := β.toAlgebra
  let : IsLocalHom (algebraMap R A) := hlocal
  have hβ : Function.Injective (algebraMap R A) := by
    intro r s h
    exact hι (congrArg (fun x : A => (x : L)) h)
  let : Module.IsTorsionFree R A :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hβ
  let : Module.Flat R A :=
    Langlands.CommutativeAlgebra.flat_of_isTorsionFree_of_valuationRing A
  let : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let p := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hp : Flat p ∧ Surjective p := (flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact ⟨{
    closure := L
    valuation := A
    projection := p
    flat := hp.1
    surjective := hp.2 }⟩

/-- Choose the actual algebraically closed valuation fpqc cover. -/
def algClosedValuationFpqcCover
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R] :
    AlgClosedValuationFpqcCover R :=
  Classical.choice (nonempty_algClosedValuationFpqcCover R)

/-- Every quasi-compact separated etale morphism to an arbitrary valuation
domain spectrum is affine. -/
theorem isAffineHom_etale_over_valuationDomain
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [IsSeparated f] [Etale f] : IsAffineHom f := by
  let C := algClosedValuationFpqcCover R
  let : Flat C.projection := C.flat
  let : Surjective C.projection := C.surjective
  let : IsAffineHom (pullback.snd f C.projection) :=
    isAffineHom_etale_algClosedValuation C.closure C.valuation (pullback.snd f C.projection)
  let : IsAffine (pullback f C.projection) :=
    isAffine_of_isAffineHom (pullback.snd f C.projection)
  let : IsAffine X := FaithfullyFlatAffineDescent.isAffine_of_isPullback
    (IsPullback.of_hasPullback f C.projection)
  infer_instance

/-- The canonical actual affine model of any quasi-compact separated etale
scheme over an arbitrary valuation domain. -/
def valuationEtaleAffineIso
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [IsSeparated f] [Etale f] : X ≅ Spec Γ(X, ⊤) :=
  have := isAffineHom_etale_over_valuationDomain R f
  have := isAffine_of_isAffineHom f
  X.isoSpec

end Langlands.AlgebraicGeometry
