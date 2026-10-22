import Langlands.VirtualRepresentation.Exact
import Langlands.Weil.Representation.TwistProperties
import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.OperationClosureProof
import Langlands.Representation.Twist.AlgebraProof
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Group.Units

/-!
# Character twisting on exact virtual representations

The actual scalar twist preserves exactness and rank, so it descends to the
exact-relation quotient. Continuous characters give actual automorphisms of the
virtual group of continuous complex representations.
-/

noncomputable section

universe uK uG uV uA uB uC

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- Twisted intertwiners have the same underlying linear maps, so short
exactness is equivalent to the original short exactness. -/
theorem isShortExact_twist_iff (χ : G →* Kˣ)
    {A : FiniteRepresentation.{uK, uG, uA} K G}
    {B : FiniteRepresentation.{uK, uG, uB} K G}
    {C : FiniteRepresentation.{uK, uG, uC} K G}
    (f : A.representation.IntertwiningMap B.representation)
    (g : B.representation.IntertwiningMap C.representation) :
    IsShortExact (A := twist χ A) (B := twist χ B) (C := twist χ C)
      (Langlands.twistIntertwining χ f)
      (Langlands.twistIntertwining χ g) ↔ IsShortExact f g := Iff.rfl

/-- The inverse character undoes the twist on the actual carrier. -/
def twistInvEquiv (χ : G →* Kˣ) (A : FiniteRepresentation K G) :
    Equiv (twist χ⁻¹ (twist χ A)) A := by
  change (Langlands.twist χ⁻¹ (Langlands.twist χ A.representation)).Equiv A.representation
  rw [Langlands.twist_inv_twist]
  exact Representation.Equiv.refl _

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]
variable (χ : G →* Kˣ)
variable (P Q : FiniteRepresentation.{uK, uG, uV} K G → Prop)

/-- Twisting on genuine classes with explicit source and target object predicates. -/
def twistClassWith
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A)) :
    IsomorphismClassesWith P → IsomorphismClassesWith Q :=
  Quotient.map
    (fun A => ⟨FiniteRepresentation.twist χ A.val, hPQ A.val A.property⟩)
    (fun _ _ ⟨e⟩ => ⟨FiniteRepresentation.twistEquiv χ e⟩)

/-- The class map respects the actual exact-sequence relations. -/
theorem twistClassWith_isExactAdditive
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A)) :
    IsExactAdditive P (fun c => ofClass Q (twistClassWith χ P Q hPQ c)) := by
  intro A B C f g h
  exact ofRepresentation_shortExact Q
    ((isShortExact_twist_iff χ (A := A.val) (B := B.val) (C := C.val) f g).mpr h)

/-- The descended integer-linear scalar-twist map. -/
def twist (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A)) :
    ExactGrothendieckGroup P →ₗ[ℤ] ExactGrothendieckGroup Q :=
  lift P (fun c => ofClass Q (twistClassWith χ P Q hPQ c))
    (twistClassWith_isExactAdditive χ P Q hPQ)

@[simp]
theorem twist_ofClass
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A))
    (c : IsomorphismClassesWith P) :
    twist χ P Q hPQ (ofClass P c) = ofClass Q (twistClassWith χ P Q hPQ c) :=
  lift_ofClass P _ _ c

@[simp]
theorem twist_ofRepresentation
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A))
    (A : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}) :
    twist χ P Q hPQ (ofRepresentation P A) =
      ofRepresentation Q ⟨FiniteRepresentation.twist χ A.val, hPQ A.val A.property⟩ :=
  twist_ofClass χ P Q hPQ _

/-- Twisting preserves the genuine integer degree. -/
theorem degree_comp_twist
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A)) :
    (degree Q).comp (twist χ P Q hPQ) = degree P := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change degree Q (twist χ P Q hPQ (ofRepresentation P A)) =
      degree P (ofRepresentation P A)
    simp only [twist_ofRepresentation, degree_ofRepresentation, rank_twist]

theorem degree_twist
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A))
    (x : ExactGrothendieckGroup P) :
    degree Q (twist χ P Q hPQ x) = degree P x :=
  LinearMap.congr_fun (degree_comp_twist χ P Q hPQ) x

/-- Restriction to the actual degree-zero submodules. -/
def twistDegreeZero
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.twist χ A)) :
    degreeZero P →ₗ[ℤ] degreeZero Q :=
  (twist χ P Q hPQ).restrict fun x hx => by
    change degree Q (twist χ P Q hPQ x) = 0
    rw [degree_twist, (mem_degreeZero P x).mp hx]

variable {χ P Q}

/-- The trivial twist is identity even if its object-closure proof is arbitrary. -/
theorem twist_one (hP : ∀ A, P A → P (FiniteRepresentation.twist 1 A)) :
    twist 1 P P hP = LinearMap.id := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change twist 1 P P hP (ofRepresentation P A) = ofRepresentation P A
    rw [twist_ofRepresentation]
    exact ofRepresentation_eq_of_equiv P (FiniteRepresentation.twistOneEquiv A.val)

/-- Composition of descended maps follows actual multiplication of characters. -/
theorem twist_comp (χ η : G →* Kˣ)
    (R : FiniteRepresentation.{uK, uG, uV} K G → Prop)
    (hη : ∀ A, P A → Q (FiniteRepresentation.twist η A))
    (hχ : ∀ A, Q A → R (FiniteRepresentation.twist χ A))
    (hχη : ∀ A, P A → R (FiniteRepresentation.twist (χ * η) A)) :
    (twist χ Q R hχ).comp (twist η P Q hη) = twist (χ * η) P R hχη := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change twist χ Q R hχ (twist η P Q hη (ofRepresentation P A)) =
      twist (χ * η) P R hχη (ofRepresentation P A)
    rw [twist_ofRepresentation, twist_ofRepresentation, twist_ofRepresentation]
    exact ofRepresentation_eq_of_equiv R (FiniteRepresentation.twistMulEquiv χ η A.val)

private theorem inverse_twist_comp
    (hχ : ∀ A, P A → P (FiniteRepresentation.twist χ A))
    (hχinv : ∀ A, P A → P (FiniteRepresentation.twist χ⁻¹ A)) :
    (twist χ⁻¹ P P hχinv).comp (twist χ P P hχ) = LinearMap.id := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change twist χ⁻¹ P P hχinv (twist χ P P hχ (ofRepresentation P A)) =
      ofRepresentation P A
    rw [twist_ofRepresentation, twist_ofRepresentation]
    exact ofRepresentation_eq_of_equiv P (FiniteRepresentation.twistInvEquiv χ A.val)

/-- If the selected family is closed under both twists, the descended map is an
actual automorphism. No invariance of an arbitrary predicate is assumed. -/
def twistEquivalence (χ : G →* Kˣ) (P : FiniteRepresentation.{uK, uG, uV} K G → Prop)
    (hχ : ∀ A, P A → P (FiniteRepresentation.twist χ A))
    (hχinv : ∀ A, P A → P (FiniteRepresentation.twist χ⁻¹ A)) :
    ExactGrothendieckGroup P ≃ₗ[ℤ] ExactGrothendieckGroup P where
  toLinearMap := twist χ P P hχ
  invFun := twist χ⁻¹ P P hχinv
  left_inv x := LinearMap.congr_fun (inverse_twist_comp hχ hχinv) x
  right_inv x := by
    have h : (twist χ P P hχ).comp (twist χ⁻¹ P P hχinv) = LinearMap.id := by
      apply hom_ext P
      intro c
      induction c using Quotient.inductionOn with
      | h A =>
        change twist χ P P hχ (twist χ⁻¹ P P hχinv (ofRepresentation P A)) =
          ofRepresentation P A
        rw [twist_ofRepresentation, twist_ofRepresentation]
        apply ofRepresentation_eq_of_equiv P
        change (Langlands.twist χ (Langlands.twist χ⁻¹ A.val.representation)).Equiv
          A.val.representation
        rw [Langlands.twist_twist_inv]
        exact Representation.Equiv.refl _
    exact LinearMap.congr_fun h x

section Continuous

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Continuous-character twisting on the exact virtual group of continuous
complex representations. Both closure obligations are proved. -/
def continuousTwist (χ : G →ₜ* ℂˣ) :
    ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous) ≃ₗ[ℤ]
      ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
        A.IsContinuous) :=
  twistEquivalence χ.toMonoidHom _
    (fun _ hA => FiniteRepresentation.isContinuous_twist χ hA)
    (fun _ hA => FiniteRepresentation.isContinuous_twist χ⁻¹ hA)

end Continuous

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
