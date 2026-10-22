import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.Int

/-!
# The generic integer-Frobenius pullback

This constructs the pullback of a continuous homomorphism to the actual
profinite completion of the integers along its canonical integer map.
The integers have the discrete topology. This is not an identification with
the absolute Weil group of any field.
-/

namespace Langlands.Weil

universe u

/-- The additive integers, written multiplicatively for the group interfaces.
Their standard topology is discrete. Multiplicative `1` represents integer `0`. -/
abbrev Degree := Multiplicative ℤ

/-- The actual profinite completion of the integer group, using Mathlib's
inverse limit of all finite quotient groups. -/
abbrev ProfiniteIntegers : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Degree)

/-- Integer Frobenius powers. The choice of arithmetic or geometric Frobenius
belongs to the identification of the residue Galois group with this completion. -/
def frobenius : Degree →ₜ* ProfiniteIntegers where
  toMonoidHom := (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of Degree)).hom
  continuous_toFun := continuous_of_discreteTopology

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]

/-- Pairs with matching images in the profinite completion. -/
def pullbackSubgroup (φ : Γ →ₜ* ProfiniteIntegers) : Subgroup (Γ × Degree) :=
  (φ.toMonoidHom.comp (MonoidHom.fst Γ Degree)).eqLocus
    (frobenius.toMonoidHom.comp (MonoidHom.snd Γ Degree))

/-- The generic Weil pullback with its subgroup structure and the subtype
topology from `Γ × Degree`, where `Degree` is discrete. -/
abbrev Pullback (φ : Γ →ₜ* ProfiniteIntegers) := ↥(pullbackSubgroup φ)

/-- The continuous projection to the original topological group. -/
def projection (φ : Γ →ₜ* ProfiniteIntegers) : Pullback φ →ₜ* Γ where
  toMonoidHom := (MonoidHom.fst Γ Degree).comp (pullbackSubgroup φ).subtype
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The continuous degree homomorphism to the discrete integer group. -/
def degree (φ : Γ →ₜ* ProfiniteIntegers) : Pullback φ →ₜ* Degree where
  toMonoidHom := (MonoidHom.snd Γ Degree).comp (pullbackSubgroup φ).subtype
  continuous_toFun := continuous_snd.comp continuous_subtype_val

/-- Degree as an ordinary integer-valued function. -/
def degreeInt (φ : Γ →ₜ* ProfiniteIntegers) (w : Pullback φ) : ℤ :=
  (degree φ w).toAdd

/-- Inertia in the original group, carrying its existing subgroup topology. -/
def inertia (φ : Γ →ₜ* ProfiniteIntegers) : Subgroup Γ :=
  φ.toMonoidHom.ker

/-- The degree-zero subgroup of the pullback. -/
def inertiaSubgroup (φ : Γ →ₜ* ProfiniteIntegers) : Subgroup (Pullback φ) :=
  (degree φ).toMonoidHom.ker

/-- Inertia enters the pullback by `g ↦ (g, 0)` in additive degree notation. -/
def inertiaInclusion (φ : Γ →ₜ* ProfiniteIntegers) :
    inertia φ →ₜ* Pullback φ where
  toMonoidHom :=
    ((inertia φ).subtype.prod (1 : inertia φ →* Degree)).codRestrict
      (pullbackSubgroup φ) (fun g => by
        change φ g.val = frobenius 1
        exact g.property.trans (map_one frobenius).symm)
  continuous_toFun := by
    exact (continuous_subtype_val.prodMk continuous_const).subtype_mk _

end Langlands.Weil
