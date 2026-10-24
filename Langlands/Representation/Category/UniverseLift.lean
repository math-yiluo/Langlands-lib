import Langlands.Representation.Category.Basic
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Mathlib.Algebra.Module.ULift

/-!
# Universe lifts of actual complex representations

Internal carrier-universe infrastructure. The action on `ULift V` is conjugate
to the original action by `up` and `down`. The resulting representation
equivalence relates carriers in different universes; it is not a categorical
isomorphism between objects of different fixed-universe categories.
-/

namespace Langlands

universe uX uG uV

variable {G : Type uG} [Group G] {V : Type uV}
  [AddCommGroup V] [Module ℂ V]

/-- Lift the carrier, preserving the actual action pointwise. -/
def universeLiftRepresentation (ρ : Representation ℂ G V) :
    Representation ℂ G (ULift.{uX} V) where
  toFun g :=
    { toFun v := ULift.up (ρ g v.down)
      map_add' v w := by
        apply ULift.ext
        exact map_add (ρ g) v.down w.down
      map_smul' c v := by
        apply ULift.ext
        exact map_smul (ρ g) c v.down }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Module.End.mul_apply]

@[simp]
theorem universeLiftRepresentation_apply (ρ : Representation ℂ G V)
    (g : G) (v : ULift.{uX} V) :
    universeLiftRepresentation ρ g v = ULift.up (ρ g v.down) := rfl

@[simp]
theorem universeLiftRepresentation_up (ρ : Representation ℂ G V) (g : G) (v : V) :
    universeLiftRepresentation ρ g (ULift.up.{uX} v) = ULift.up (ρ g v) := rfl

@[simp]
theorem universeLiftRepresentation_down (ρ : Representation ℂ G V)
    (g : G) (v : ULift.{uX} V) :
    (universeLiftRepresentation ρ g v).down = ρ g v.down := rfl

/-- The actual cross-universe representation equivalence, forward `up`, inverse
`down`. -/
def universeLiftEquiv (ρ : Representation ℂ G V) :
    ρ.Equiv (universeLiftRepresentation.{uX} ρ) :=
  Representation.Equiv.mk (ULift.moduleEquiv.symm) fun g => by
    ext v
    rfl

@[simp]
theorem universeLiftEquiv_apply (ρ : Representation ℂ G V) (v : V) :
    universeLiftEquiv.{uX} ρ v = ULift.up v := rfl

@[simp]
theorem universeLiftEquiv_symm_apply (ρ : Representation ℂ G V) (v : ULift.{uX} V) :
    (universeLiftEquiv ρ).symm v = v.down := rfl

theorem isIrreducible_universeLift_iff (ρ : Representation ℂ G V) :
    Representation.IsIrreducible (universeLiftRepresentation.{uX} ρ) ↔
      Representation.IsIrreducible ρ :=
  (isIrreducible_iff_of_equiv (universeLiftEquiv ρ)).symm

variable [TopologicalSpace G]

theorem isSmooth_universeLift_iff (ρ : Representation ℂ G V) :
    IsSmooth (universeLiftRepresentation.{uX} ρ) ↔ IsSmooth ρ :=
  ⟨isSmooth_of_injective (universeLiftEquiv ρ).toIntertwiningMap
      (universeLiftEquiv ρ).injective,
    isSmooth_of_surjective (universeLiftEquiv ρ).toIntertwiningMap
      (universeLiftEquiv ρ).surjective⟩

theorem isAdmissible_universeLift_iff (ρ : Representation ℂ G V) :
    IsAdmissible (universeLiftRepresentation.{uX} ρ) ↔ IsAdmissible ρ :=
  (isAdmissible_iff_of_equiv (universeLiftEquiv ρ)).symm

namespace SmoothRep

/-- A smooth representation with carrier raised to `Type (max uV uX)`. -/
def universeLift (A : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothRep.{0, uG, max uV uX} ℂ G :=
  of (universeLiftRepresentation A.representation)
    ((isSmooth_universeLift_iff A.representation).mpr A.isSmooth)

@[simp]
theorem universeLift_representation (A : SmoothRep.{0, uG, uV} ℂ G) :
    (universeLift.{uX} A).representation =
      universeLiftRepresentation.{uX} A.representation := rfl

/-- The source and bundled lift are equivalent as actual representations. -/
def universeLiftEquiv (A : SmoothRep.{0, uG, uV} ℂ G) :
    A.representation.Equiv (universeLift.{uX} A).representation :=
  Langlands.universeLiftEquiv A.representation

@[simp]
theorem universeLiftEquiv_apply (A : SmoothRep.{0, uG, uV} ℂ G) (v : A) :
    universeLiftEquiv.{uX} A v = ULift.up v := rfl

@[simp]
theorem universeLiftEquiv_symm_apply (A : SmoothRep.{0, uG, uV} ℂ G)
    (v : universeLift.{uX} A) :
    (universeLiftEquiv A).symm v = v.down := rfl

theorem isIrreducible_universeLift_iff (A : SmoothRep.{0, uG, uV} ℂ G) :
    (universeLift.{uX} A).IsIrreducible ↔ A.IsIrreducible :=
  Langlands.isIrreducible_universeLift_iff A.representation

theorem isAdmissible_universeLift_iff (A : SmoothRep.{0, uG, uV} ℂ G) :
    (universeLift.{uX} A).IsAdmissible ↔ A.IsAdmissible :=
  Langlands.isAdmissible_universeLift_iff A.representation

end SmoothRep
end Langlands
