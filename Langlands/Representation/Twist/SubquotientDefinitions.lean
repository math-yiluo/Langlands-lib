import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Character twists of subrepresentations and quotients

The invariant submodules are unchanged by a unit-valued scalar twist.
All constructions use Mathlib's existing subrepresentation and quotient types.
-/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- Retain an invariant submodule while twisting the ambient action. -/
def twistSubrepresentation (chi : G →* Rˣ) {rho : Representation R G V}
    (S : Subrepresentation rho) : Subrepresentation (twist chi rho) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g _ hv :=
    S.toSubmodule.smul_mem (chi g : R) (S.apply_mem_toSubmodule g hv)

/-- An invariant submodule for a twist is invariant for the original action. -/
def untwistSubrepresentation (chi : G →* Rˣ) {rho : Representation R G V}
    (S : Subrepresentation (twist chi rho)) : Subrepresentation rho where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g _ hv := by
    have h := S.toSubmodule.smul_mem (((chi g)⁻¹ : Rˣ) : R)
      (S.apply_mem_toSubmodule g hv)
    simpa [twist, smul_smul] using h

/-- A scalar character twist preserves the ordered lattice of subrepresentations. -/
def twistSubrepresentationOrderIso (chi : G →* Rˣ) (rho : Representation R G V) :
    Subrepresentation rho ≃o Subrepresentation (twist chi rho) where
  toFun := twistSubrepresentation chi
  invFun := untwistSubrepresentation chi
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

/-- Twisting a restricted representation agrees with restricting the twisted action. -/
def twistSubrepresentationEquiv (chi : G →* Rˣ) {rho : Representation R G V}
    (S : Subrepresentation rho) :
    (twist chi S.toRepresentation).Equiv
      (twistSubrepresentation chi S).toRepresentation where
  toLinearEquiv := LinearEquiv.refl R S.toSubmodule
  isIntertwining' g := by
    ext v
    rfl

/-- Twisting a quotient agrees with quotienting the twisted representation. -/
def twistQuotientEquiv (chi : G →* Rˣ) {rho : Representation R G V}
    (S : Subrepresentation rho) :
    (twist chi (rho.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
      ((twist chi rho).quotient (twistSubrepresentation chi S).toSubmodule
        (twistSubrepresentation chi S).apply_mem_toSubmodule) where
  toLinearEquiv := LinearEquiv.refl R (V ⧸ S.toSubmodule)
  isIntertwining' g := by
    ext v
    rfl

end Langlands
