import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Twist.DualProof
import Langlands.Representation.Twist.SmoothProof

/-! # Twisting smooth parts and smooth contragredients

An open-kernel character preserves smooth vectors. The resulting representation
equivalences retain the ambient vector or linear functional.
-/

noncomputable section

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [IsTopologicalGroup G]

/-- Identify the smooth part of a twist with the twist of the smooth part. -/
def smoothPartTwistEquiv (chi : G →* Rˣ) (rho : Representation R G V)
    (hchi : IsOpen (chi.ker : Set G)) :
    (smoothPart (twist chi rho)).Equiv (twist chi (smoothPart rho)) where
  toLinearEquiv :=
    { toFun := fun v => ⟨v.val, (isSmoothVector_twist_iff chi rho hchi v.val).mp v.property⟩
      invFun := fun v => ⟨v.val, (isSmoothVector_twist_iff chi rho hchi v.val).mpr v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    ext v
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem inverseCharacter_ker (chi : G →* Rˣ) :
    (chi⁻¹).ker = chi.ker := by
  ext g
  simp

/-- Identify the smooth dual of a twist with the inverse-character twist of the
smooth dual. The map preserves each underlying linear functional. -/
def smoothContragredientTwistEquiv (chi : G →* Rˣ) (rho : Representation R G V)
    (hchi : IsOpen (chi.ker : Set G)) :
    (smoothContragredient (twist chi rho)).Equiv
      (twist (V := SmoothDual rho) chi⁻¹ (smoothContragredient rho)) where
  toLinearEquiv :=
    { toFun := fun ell => ⟨ell.val, by
        have h : IsSmoothVector (twist chi⁻¹ rho.dual) ell.val :=
          Eq.mp (congrArg (fun tau : Representation R G (Module.Dual R V) =>
            IsSmoothVector tau ell.val) (dual_twist chi rho)) ell.property
        exact (isSmoothVector_twist_iff chi⁻¹ rho.dual
          (by simpa only [inverseCharacter_ker] using hchi) ell.val).mp h⟩
      invFun := fun ell => ⟨ell.val, by
        change IsSmoothVector (twist chi rho).dual ell.val
        rw [dual_twist]
        exact (isSmoothVector_twist_iff chi⁻¹ rho.dual
          (by simpa only [inverseCharacter_ker] using hchi) ell.val).mpr ell.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro ell
    apply Subtype.ext
    change (twist chi rho).dual g ell.val = (twist chi⁻¹ rho.dual) g ell.val
    exact congrArg (fun tau : Representation R G (Module.Dual R V) =>
      tau g ell.val) (dual_twist chi rho)

end Langlands
