import Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Bezout
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Basic-open and specialization geometry for valuation affineness -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- Every quasi-compact open of the spectrum of a Bezout ring is principal. -/
theorem exists_eq_basicOpen_of_isCompact_of_isBezout
    (R : CommRingCat.{u}) [IsBezout R] (U : (Spec R).Opens)
    (hU : IsCompact (U : Set (Spec R))) : ∃ r : R, U = PrimeSpectrum.basicOpen r := by
  obtain ⟨I, hI, hIU⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hU, U.isOpen⟩
  obtain ⟨r, hr⟩ := (IsBezout.isPrincipal_of_FG I hI).1
  refine ⟨r, ?_⟩
  apply SetLike.coe_injective
  rw [← hIU, hr, PrimeSpectrum.zeroLocus_span]
  exact (PrimeSpectrum.basicOpen_eq_zeroLocus_compl r).symm

/-- Every quasi-compact open of the spectrum of a Bezout ring is affine. -/
theorem isAffineOpen_of_isCompact_of_isBezout
    (R : CommRingCat.{u}) [IsBezout R] (U : (Spec R).Opens)
    (hU : IsCompact (U : Set (Spec R))) : IsAffineOpen U := by
  obtain ⟨r, rfl⟩ := exists_eq_basicOpen_of_isCompact_of_isBezout R U hU
  exact IsAffineOpen.Spec_basicOpen r

/-- A finite set meeting the specialization closure of every point makes
an actual quasi-affine scheme affine. -/
theorem isAffine_of_finite_specializationCover (X : Scheme.{u}) [X.IsQuasiAffine]
    {E : Set X} (hE : E.Finite) (hcover : ∀ x : X, ∃ e ∈ E, x ⤳ e) : IsAffine X := by
  obtain ⟨r, hEr, hr⟩ :=
    OrbitSaturatedAffineOpen.exists_basicOpen_isAffineOpen_of_finite X hE
  have htop : X.basicOpen r = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨e, he, hxe⟩ := hcover x
    exact hxe.mem_open (X.basicOpen r).isOpen (hEr he)
  let : IsAffine (⊤ : X.Opens) := htop ▸ hr
  exact IsAffine.of_isIso X.topIso.inv

/-- The canonical affine coordinate model supplied by a finite specialization cover. -/
def affineIsoOfFiniteSpecializationCover (X : Scheme.{u}) [X.IsQuasiAffine]
    {E : Set X} (hE : E.Finite) (hcover : ∀ x : X, ∃ e ∈ E, x ⤳ e) :
    X ≅ Spec Γ(X, ⊤) :=
  have := isAffine_of_finite_specializationCover X hE hcover
  X.isoSpec

/-- A quasi-affine scheme with a finite jointly surjective family of maps from
spectra of local rings is affine; the maps need not be open or affine. -/
theorem isAffine_of_finite_localSpectrum_family
    (X : Scheme.{u}) [X.IsQuasiAffine]
    {ι : Type u} [Finite ι] (R : ι → CommRingCat.{u}) [∀ i, IsLocalRing (R i)]
    (f : ∀ i, Spec (R i) ⟶ X)
    (hcover : ∀ x : X, ∃ i y, f i y = x) : IsAffine X := by
  apply isAffine_of_finite_specializationCover X
    (E := Set.range (fun i => f i (IsLocalRing.closedPoint (R i)))) (Set.finite_range _)
  intro x
  obtain ⟨i, y, rfl⟩ := hcover x
  exact ⟨f i (IsLocalRing.closedPoint (R i)), ⟨i, rfl⟩,
    (IsLocalRing.specializes_closedPoint y).map (f i).continuous⟩

end Langlands.AlgebraicGeometry
