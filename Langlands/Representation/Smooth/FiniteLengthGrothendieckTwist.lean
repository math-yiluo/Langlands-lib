import Langlands.Representation.Category.Twist
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor
import Mathlib.RingTheory.Length

/-!
# Character twists on the exact finite-length smooth Grothendieck group

The actual scalar twist preserves group-algebra length and all short exact
sequences. An open-kernel character therefore induces an integer-linear
automorphism of the existing exact finite-length Grothendieck group.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]

/-- Scalar character twists preserve the full group-algebra module length. -/
theorem length_twist {V : Type uV} [AddCommGroup V] [Module R V]
    (χ : G →* Rˣ) (ρ : Representation R G V) :
    Module.length R[G] (Langlands.twist χ ρ).asModule =
      Module.length R[G] ρ.asModule := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    ((Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := Langlands.twist χ ρ)).symm.trans
        ((twistSubrepresentationOrderIso χ ρ).symm.trans
          (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ))))

/-- Finite group-algebra length is unchanged by a scalar character twist. -/
theorem finiteLength_twist_iff {V : Type uV} [AddCommGroup V] [Module R V]
    (χ : G →* Rˣ) (ρ : Representation R G V) :
    IsFiniteLength R[G] (Langlands.twist χ ρ).asModule ↔
      IsFiniteLength R[G] ρ.asModule := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff, length_twist]

namespace SmoothRep

variable [TopologicalSpace G]

/-- Twisting the actual smooth action preserves finite group-algebra length. -/
theorem twistFunctor_preservesFiniteLength (χ : G →* Rˣ)
    (hχ : IsOpen (χ.ker : Set G)) :
    PreservesFiniteLength (twistFunctor.{uR, uG, uV} χ hχ) := by
  intro A hA
  exact (finiteLength_twist_iff χ A.representation).mpr hA

/-- A common twist retains the underlying linear maps and all exact relations. -/
theorem twistFunctor_preservesShortExact (χ : G →* Rˣ)
    (hχ : IsOpen (χ.ker : Set G)) :
    PreservesFiniteLengthShortExact (twistFunctor.{uR, uG, uV} χ hχ) := by
  intro A B C f g _ _ _ h
  exact h

namespace FiniteLengthGrothendieckGroup

/-- The actual scalar twist on the full exact finite-length Grothendieck group. -/
def twist (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uR, uG, uV} R G :=
  map (twistFunctor χ hχ) (twistFunctor_preservesFiniteLength χ hχ)
    (twistFunctor_preservesShortExact χ hχ)

/-- On every genuine class the map gives the literal twisted smooth object. -/
theorem twist_ofRepresentation (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) (hA : A.HasFiniteLength)
    (hOut : (A.twist χ hχ).HasFiniteLength) :
    twist χ hχ (ofRepresentation A hA) = ofRepresentation (A.twist χ hχ) hOut :=
  map_ofRepresentation _ _ _ A hA

/-- The trivial character acts as the identity on every virtual class. -/
theorem twist_one (h1 : IsOpen ((1 : G →* Rˣ).ker : Set G)) :
    twist.{uR, uG, uV} 1 h1 = LinearMap.id := by
  apply hom_ext_object R G
  intro A
  change twist 1 h1 (ofRepresentation A.val A.property) =
    ofRepresentation A.val A.property
  rw [twist_ofRepresentation 1 h1 A.val A.property
    (twistFunctor_preservesFiniteLength 1 h1 A.val A.property)]
  exact ofObject_eq_of_iso (twistOneIso h1 A.val)

/-- Successive actual twists give the product-character map on the exact K0. -/
theorem twist_mul (χ η : G →* Rˣ)
    (hχ : IsOpen (χ.ker : Set G)) (hη : IsOpen (η.ker : Set G))
    (hχη : IsOpen ((χ * η).ker : Set G)) :
    twist.{uR, uG, uV} (χ * η) hχη = (twist χ hχ).comp (twist η hη) := by
  apply hom_ext_object R G
  intro A
  change twist (χ * η) hχη (ofRepresentation A.val A.property) =
    twist χ hχ (twist η hη (ofRepresentation A.val A.property))
  have hηA := twistFunctor_preservesFiniteLength η hη A.val A.property
  have hχηA := twistFunctor_preservesFiniteLength χ hχ (A.val.twist η hη) hηA
  have hProd := twistFunctor_preservesFiniteLength (χ * η) hχη A.val A.property
  rw [twist_ofRepresentation (χ * η) hχη A.val A.property hProd,
    twist_ofRepresentation η hη A.val A.property hηA,
    twist_ofRepresentation χ hχ (A.val.twist η hη) hηA hχηA]
  exact (ofObject_eq_of_iso (twistTwistIso χ η hχ hη hχη A.val)).symm

/-- Inverse-character twisting undoes twisting on all virtual classes. -/
theorem twist_inv_comp (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (hInv : IsOpen ((χ⁻¹).ker : Set G)) :
    (twist.{uR, uG, uV} χ⁻¹ hInv).comp (twist χ hχ) = LinearMap.id := by
  apply hom_ext_object R G
  intro A
  change twist χ⁻¹ hInv (twist χ hχ (ofRepresentation A.val A.property)) =
    ofRepresentation A.val A.property
  have hχA := twistFunctor_preservesFiniteLength χ hχ A.val A.property
  have hInvA := twistFunctor_preservesFiniteLength χ⁻¹ hInv (A.val.twist χ hχ) hχA
  rw [twist_ofRepresentation χ hχ A.val A.property hχA,
    twist_ofRepresentation χ⁻¹ hInv (A.val.twist χ hχ) hχA hInvA]
  exact ofRepresentation_eq_of_equiv _ _
    (equivOfRepresentationEq (Langlands.twist_inv_twist χ A.val.representation))

/-- The inverse-character map is also a right inverse on the entire exact K0. -/
theorem twist_comp_inv (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (hInv : IsOpen ((χ⁻¹).ker : Set G)) :
    (twist.{uR, uG, uV} χ hχ).comp (twist χ⁻¹ hInv) = LinearMap.id := by
  apply hom_ext_object R G
  intro A
  change twist χ hχ (twist χ⁻¹ hInv (ofRepresentation A.val A.property)) =
    ofRepresentation A.val A.property
  have hInvA := twistFunctor_preservesFiniteLength χ⁻¹ hInv A.val A.property
  have hχA := twistFunctor_preservesFiniteLength χ hχ (A.val.twist χ⁻¹ hInv) hInvA
  rw [twist_ofRepresentation χ⁻¹ hInv A.val A.property hInvA,
    twist_ofRepresentation χ hχ (A.val.twist χ⁻¹ hInv) hInvA hχA]
  exact ofRepresentation_eq_of_equiv _ _
    (equivOfRepresentationEq (Langlands.twist_twist_inv χ A.val.representation))

private theorem open_ker_inv (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsOpen ((χ⁻¹).ker : Set G) := by
  have hk : (χ⁻¹).ker = χ.ker := by
    ext g
    simp
  simpa only [hk] using hχ

/-- Every open-kernel scalar character gives an integer-linear automorphism of
actual finite-length smooth virtual representations. Its inverse is the twist
by the inverse character. -/
def twistEquiv (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G ≃ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uR, uG, uV} R G where
  toLinearMap := twist χ hχ
  invFun := twist χ⁻¹ (open_ker_inv χ hχ)
  left_inv x := LinearMap.congr_fun (twist_inv_comp χ hχ (open_ker_inv χ hχ)) x
  right_inv x := LinearMap.congr_fun (twist_comp_inv χ hχ (open_ker_inv χ hχ)) x

@[simp]
theorem twistEquiv_toLinearMap (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    (twistEquiv.{uR, uG, uV} χ hχ).toLinearMap = twist χ hχ := rfl

end FiniteLengthGrothendieckGroup
end SmoothRep
end Langlands
