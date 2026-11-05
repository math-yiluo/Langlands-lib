import Langlands.GroupScheme.Descent.AffineIdealDescent
import Langlands.GroupScheme.Rational.GaloisIdealDescent

/-! # Galois-stable tensor ideals give ideal-sheaf descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineIdealDescent

/-- Coordinate equivalences transport an algebraic ideal-extension equality
into actual defining-ideal descent. -/
def ofCoordinateExtension {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {A B : Type u} [CommRing A] [CommRing B]
    (f : X ⟶ Y) (I : X.IdealSheafData)
    (eA : A ≃+* Γ(Y, ⊤)) (eB : B ≃+* Γ(X, ⊤)) (c : A →+* B)
    (hc : f.appTop.hom.comp eA.toRingHom = eB.toRingHom.comp c)
    (J : Ideal A)
    (hJ : J.map c = (I.ideal ⟨⊤, isAffineOpen_top X⟩).comap eB.toRingHom) :
    DefiningIdealDescent f I :=
  ofGlobalIdeal f I (J.map eA.toRingHom) (by
    rw [Ideal.map_map, hc, ← Ideal.map_map, hJ]
    exact Ideal.map_comap_of_surjective eB.toRingHom eB.surjective _)

/-- For any Galois extension, a coefficient-stable tensor-coordinate ideal
comes from an actual ideal sheaf on the original affine scheme. -/
def ofGaloisStableTensorIdeal
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [IsGalois k K]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : X.IdealSheafData)
    (eA : A ≃+* Γ(Y, ⊤)) (eK : K ⊗[k] A ≃+* Γ(X, ⊤))
    (hc : f.appTop.hom.comp eA.toRingHom = eK.toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom)
    (hI : ∀ (σ : K ≃ₐ[k] K) (x : K ⊗[k] A),
      x ∈ (I.ideal ⟨⊤, isAffineOpen_top X⟩).comap eK.toRingHom →
        TensorGaloisPoint.coefficientConjugate k K A σ x ∈
          (I.ideal ⟨⊤, isAffineOpen_top X⟩).comap eK.toRingHom) :
    DefiningIdealDescent f I :=
  ofCoordinateExtension f I eA eK _ hc
    (GaloisIdealDescent.groundIdeal k K A
      ((I.ideal ⟨⊤, isAffineOpen_top X⟩).comap eK.toRingHom))
    (GaloisIdealDescent.map_groundIdeal_eq k K A _ hI)

end Langlands.GroupScheme.AffineIdealDescent
