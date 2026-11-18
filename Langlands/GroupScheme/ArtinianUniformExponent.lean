import Langlands.GroupScheme.Rational.HopfCoordinateComparison
import Langlands.GroupScheme.Torus.FiniteFlatLocalDiagonalizableSubgroup
import Langlands.GroupScheme.NilpotentCoefficientPowers
import Langlands.GroupScheme.FiniteUniformExponent
import Langlands.AbelianScheme.KernelBaseChange
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi

/-! # Uniform exponents over Artinian local bases -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.ArtinianUniformExponent

/-- The Artinian local restriction used in the global exponent argument. -/
def Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    QuasiCompact G.X.hom → LocallyQuasiFinite G.X.hom →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ G.X), x ^ n = 1

/-- A finite reduced algebra over a characteristic-zero field is formally unramified. -/
theorem formallyUnramified_of_finite_reduced
    (k A : Type u) [Field k] [CharZero k] [CommRing A] [Algebra k A]
    [Module.Finite k A] [IsReduced A] : Algebra.FormallyUnramified k A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  let (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have (m : MaximalSpectrum A) : Algebra.FormallyUnramified k (A ⧸ m.asIdeal) :=
    Algebra.FormallyUnramified.of_isSeparable k (A ⧸ m.asIdeal)
  exact Algebra.FormallyUnramified.of_equiv
    ((IsArtinianRing.equivPi A).restrictScalars k).symm

/-- A finite Hopf algebra over a local ring with characteristic-zero residue field
is formally unramified, without a flatness assumption on the Hopf algebra. -/
theorem formallyUnramified_hopf
    (R H : Type u) [CommRing R] [IsLocalRing R] [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [CharZero (IsLocalRing.ResidueField R)] :
    Algebra.FormallyUnramified R H := by
  let k := IsLocalRing.ResidueField R
  let : Algebra H (k ⊗[R] H) := Algebra.TensorProduct.rightAlgebra
  have : IsReduced (k ⊗[R] H) :=
    Langlands.FiniteHopfCharZero.isReduced (k := k) (H := k ⊗[R] H)
  have : Algebra.FormallyUnramified k (k ⊗[R] H) :=
    formallyUnramified_of_finite_reduced k (k ⊗[R] H)
  have : Module.Finite R Ω[H⁄R] := Module.Finite.trans H Ω[H⁄R]
  have : Subsingleton (k ⊗[R] Ω[H⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R k H (k ⊗[R] H)).injective.subsingleton
  exact ⟨(IsLocalRing.subsingleton_tensorProduct (R := R) (M := Ω[H⁄R])).mp this⟩

/-- The Hopf and infinitesimal coordinate choices are isomorphic as base algebras. -/
def coordinatesEquiv {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom] [IsAffine G.X.left] :
    AffineCoordinates.hopfAlgebra G ≃ₐ[R] Lie.coordinateAlgebra G :=
  AffineCoordinates.lieCoordinateAlgEquiv G

/-- Finiteness of a group scheme implies finiteness of its coordinate Hopf algebra
 over an arbitrary ring. -/
theorem finite_hopfAlgebra {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsFinite G.X.hom] [IsAffine G.X.left] :
    Module.Finite R (AffineCoordinates.hopfAlgebra G) :=
  Diagonalizable.finite_hopfAlgebra (H := G)

end Langlands.GroupScheme.ArtinianUniformExponent
