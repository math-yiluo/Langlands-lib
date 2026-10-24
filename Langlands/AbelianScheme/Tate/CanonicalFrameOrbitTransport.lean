import Langlands.AbelianScheme.Tate.PrimeToAdelicFrameTransport
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathStatement

/-! # Canonical fixed-orbit equivalences conditional on geometric path existence -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u v w z

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
  (A : AbelianScheme S)
  {Ωs Ωt Ωr : Type u}
  [Field Ωs] [IsAlgClosed Ωs] [Field Ωt] [IsAlgClosed Ωt]
  [Field Ωr] [IsAlgClosed Ωr]
  {s : Spec (.of Ωs) ⟶ S} {t : Spec (.of Ωt) ⟶ S} {r : Spec (.of Ωr) ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  {G : Type z} [Group G]

section Full

variable (h : Global.RationalProfiniteIntegerAdeleComparison)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))

/-- The canonical equivalence on full fixed frame orbits, conditional on the
published geometric path-existence proposition. -/
def adelicFrameOrbitCanonicalEquiv (U : Subgroup G)
    (hp : GeometricPathExists s t hs ht) :
    AdelicFrameOrbit A h i V s ρ hs htor hu U ≃
      AdelicFrameOrbit A h i V t ρ ht htor hu U :=
  adelicFrameOrbitTransport A h i V ρ htor hu U (Classical.choice hp)

/-- Every path gives the canonical fixed-orbit equivalence. -/
theorem adelicFrameOrbitCanonicalEquiv_eq_transport (U : Subgroup G)
    (hp : GeometricPathExists s t hs ht) (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hp =
      adelicFrameOrbitTransport A h i V ρ htor hu U p :=
  adelicFrameOrbitTransport_path_independent A h i V ρ htor hu U _ p

@[simp] theorem adelicFrameOrbitCanonicalEquiv_refl (U : Subgroup G)
    (hp : GeometricPathExists s s hs hs) :
    adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hp =
      Equiv.refl (AdelicFrameOrbit A h i V s ρ hs htor hu U) := by
  rw [adelicFrameOrbitCanonicalEquiv_eq_transport A i h V ρ htor hu U hp
    (Iso.refl (fiberFunctor s hs))]
  exact adelicFrameOrbitTransport_refl A h i V ρ htor hu U

/-- Canonical comparison from the first point to the third is successive
comparison through the second point. -/
theorem adelicFrameOrbitCanonicalEquiv_trans (U : Subgroup G)
    (hst : GeometricPathExists s t hs ht) (htr : GeometricPathExists t r ht hr)
    (hsr : GeometricPathExists s r hs hr) :
    adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hsr =
      (adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hst).trans
        (adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U htr) := by
  rw [adelicFrameOrbitCanonicalEquiv_eq_transport A i h V ρ htor hu U hsr
    (Classical.choice hst ≪≫ Classical.choice htr)]
  exact adelicFrameOrbitTransport_trans A h i V ρ htor hu U _ _

theorem adelicFrameOrbitCanonicalEquiv_symm (U : Subgroup G)
    (hst : GeometricPathExists s t hs ht) (hts : GeometricPathExists t s ht hs) :
    (adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hst).symm =
      adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hts := by
  rw [adelicFrameOrbitCanonicalEquiv_eq_transport A i h V ρ htor hu U hts
    (Classical.choice hst).symm]
  exact adelicFrameOrbitTransport_symm A h i V ρ htor hu U _

theorem adelicFrameOrbitCanonicalEquiv_translate {U U' : Subgroup G}
    (hp : GeometricPathExists s t hs ht) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (x : AdelicFrameOrbit A h i V s ρ hs htor hu U) :
    adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U' hp
        (adelicFrameOrbitTranslate A h i V ρ htor hu g hg x) =
      adelicFrameOrbitTranslate A h i V ρ htor hu g hg
        (adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hp x) :=
  adelicFrameOrbitTransport_translate A h i V ρ htor hu (Classical.choice hp) g hg x

theorem adelicFrameOrbitCanonicalEquiv_forget {U U' : Subgroup G}
    (hp : GeometricPathExists s t hs ht) (hU : U ≤ U')
    (x : AdelicFrameOrbit A h i V s ρ hs htor hu U) :
    adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U' hp
        (adelicFrameOrbitForget A h i V ρ htor hu hU x) =
      adelicFrameOrbitForget A h i V ρ htor hu hU
        (adelicFrameOrbitCanonicalEquiv A i h V ρ htor hu U hp x) :=
  adelicFrameOrbitTransport_forget A h i V ρ htor hu (Classical.choice hp) hU x

end Full

section Away

variable (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))

/-- The canonical equivalence on away fixed frame orbits, conditional on the
published geometric path-existence proposition. -/
def primeToAdelicFrameOrbitCanonicalEquiv (U : Subgroup G)
    (hp : GeometricPathExists s t hs ht) :
    PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U ≃
      PrimeToAdelicFrameOrbit A m hAway i V t ρ ht htor hu U :=
  primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U (Classical.choice hp)

/-- Every path gives the canonical fixed-orbit equivalence. -/
theorem primeToAdelicFrameOrbitCanonicalEquiv_eq_transport (U : Subgroup G)
    (hp : GeometricPathExists s t hs ht) (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hp =
      primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U p :=
  primeToAdelicFrameOrbitTransport_path_independent A m hAway i V ρ htor hu U _ p

@[simp] theorem primeToAdelicFrameOrbitCanonicalEquiv_refl (U : Subgroup G)
    (hp : GeometricPathExists s s hs hs) :
    primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hp =
      Equiv.refl (PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) := by
  rw [primeToAdelicFrameOrbitCanonicalEquiv_eq_transport A i m hAway V ρ htor hu U hp
    (Iso.refl (fiberFunctor s hs))]
  exact primeToAdelicFrameOrbitTransport_refl A m hAway i V ρ htor hu U

theorem primeToAdelicFrameOrbitCanonicalEquiv_trans (U : Subgroup G)
    (hst : GeometricPathExists s t hs ht) (htr : GeometricPathExists t r ht hr)
    (hsr : GeometricPathExists s r hs hr) :
    primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hsr =
      (primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hst).trans
        (primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U htr) := by
  rw [primeToAdelicFrameOrbitCanonicalEquiv_eq_transport A i m hAway V ρ htor hu U hsr
    (Classical.choice hst ≪≫ Classical.choice htr)]
  exact primeToAdelicFrameOrbitTransport_trans A m hAway i V ρ htor hu U _ _

theorem primeToAdelicFrameOrbitCanonicalEquiv_symm (U : Subgroup G)
    (hst : GeometricPathExists s t hs ht) (hts : GeometricPathExists t s ht hs) :
    (primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hst).symm =
      primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hts := by
  rw [primeToAdelicFrameOrbitCanonicalEquiv_eq_transport A i m hAway V ρ htor hu U hts
    (Classical.choice hst).symm]
  exact primeToAdelicFrameOrbitTransport_symm A m hAway i V ρ htor hu U _

theorem primeToAdelicFrameOrbitCanonicalEquiv_translate {U U' : Subgroup G}
    (hp : GeometricPathExists s t hs ht) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (x : PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U' hp
        (primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu g hg x) =
      primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu g hg
        (primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hp x) :=
  primeToAdelicFrameOrbitTransport_translate A m hAway i V ρ htor hu
    (Classical.choice hp) g hg x

theorem primeToAdelicFrameOrbitCanonicalEquiv_forget {U U' : Subgroup G}
    (hp : GeometricPathExists s t hs ht) (hU : U ≤ U')
    (x : PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U' hp
        (primeToAdelicFrameOrbitForget A m hAway i V ρ htor hu hU x) =
      primeToAdelicFrameOrbitForget A m hAway i V ρ htor hu hU
        (primeToAdelicFrameOrbitCanonicalEquiv A i m hAway V ρ htor hu U hp x) :=
  primeToAdelicFrameOrbitTransport_forget A m hAway i V ρ htor hu
    (Classical.choice hp) hU x

end Away

end Langlands.AbelianScheme.Tate
