import Langlands.Cohomology.SupercuspidalExtCharZero.Statement
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.OrbitSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Admissibility from compact coefficients in characteristic zero

Finite-orbit averaging extends every compact-open fixed-vector functional smoothly.
The basis-in-a-projected-orbit proof then gives finite-dimensional fixed vectors over
any field of characteristic zero, without a topology on the coefficient field.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalExtCharZero

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [CharZero k] in
/-- Orbit maps of smooth vectors are locally constant, over an arbitrary field. -/
theorem orbitMap_locallyConstant (ρ : SmoothRep.{u, u, u} k G) (v : ρ) :
    IsLocallyConstant (fun g : G => ρ.representation g v) := by
  obtain ⟨K, hK⟩ := ρ.isSmooth v
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (K : Set G),
    K.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro x hx
    have hfix : ρ.representation (g⁻¹ * x) v = v := hK ⟨g⁻¹ * x, hx⟩
    calc
      ρ.representation x v = ρ.representation g (ρ.representation (g⁻¹ * x) v) := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      _ = ρ.representation g v := congrArg (ρ.representation g) hfix

/-- Extend a functional on compact-open fixed vectors using finite-orbit averaging. -/
def fixedCoefficientFunctional (ρ : SmoothRep.{u, u, u} k G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : Module.Dual k (fixedVectors ρ.representation K.toSubgroup)) :
    Module.Dual k ρ :=
  Compact.CharZero.fixedExtension ρ.representation ρ.isSmooth K hK ℓ

@[simp]
theorem fixedCoefficientFunctional_apply (ρ : SmoothRep.{u, u, u} k G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : Module.Dual k (fixedVectors ρ.representation K.toSubgroup)) (v : ρ) :
    fixedCoefficientFunctional ρ K hK ℓ v =
      ℓ (Compact.CharZero.fixedProjection ρ.representation ρ.isSmooth K hK v) :=
  rfl

theorem fixedCoefficientFunctional_isSmoothVector (ρ : SmoothRep.{u, u, u} k G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : Module.Dual k (fixedVectors ρ.representation K.toSubgroup)) :
    IsSmoothVector ρ.representation.dual (fixedCoefficientFunctional ρ K hK ℓ) :=
  Compact.CharZero.fixedExtension_isSmoothVector ρ.representation ρ.isSmooth K hK ℓ

/-- An irreducible smooth representation with compact smooth-dual coefficients has
finite-dimensional fixed vectors under every compact open subgroup. -/
theorem finiteDimensional_fixedVectors (ρ : SmoothRep.{u, u, u} k G)
    (hirr : ρ.IsIrreducible) (hc : HasCompactCoefficients ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    FiniteDimensional k (fixedVectors ρ.representation K.toSubgroup) := by
  classical
  by_cases h0 : fixedVectors ρ.representation K.toSubgroup = ⊥
  · rw [h0]
    infer_instance
  obtain ⟨ξ, hξK, hξ0⟩ := (Submodule.ne_bot_iff _).mp h0
  let P := Compact.CharZero.fixedProjection ρ.representation ρ.isSmooth K hK
  let u : G → fixedVectors ρ.representation K.toSubgroup :=
    fun g => P (ρ.representation g ξ)
  have hspan : Submodule.span k (Set.range u) = ⊤ := by
    have hrange : Set.range u = P '' Set.range (fun g => ρ.representation g ξ) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_range_orbit_eq_top hirr hξ0, Submodule.map_top,
      LinearMap.range_eq_top]
    intro v
    exact ⟨v, Compact.CharZero.fixedProjection_fixed ρ.representation ρ.isSmooth K hK v⟩
  obtain ⟨b, hbu, hbspan, hbli⟩ := exists_linearIndependent k (Set.range u)
  let B : Module.Basis b k (fixedVectors ρ.representation K.toSubgroup) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  let Λ := fixedCoefficientFunctional ρ K hK B.sumCoords
  have hsupp : HasCompactSupport (matrixCoefficient ρ.representation Λ ξ) :=
    hc ξ Λ (fixedCoefficientFunctional_isSmoothVector ρ K hK _)
  have hcoef : ∀ g, matrixCoefficient ρ.representation Λ ξ g = B.sumCoords (u g) :=
    fun _ => rfl
  have hu : IsLocallyConstant u := (orbitMap_locallyConstant ρ ξ).comp P
  let _ : TopologicalSpace (fixedVectors ρ.representation K.toSubgroup) := ⊥
  have : DiscreteTopology (fixedVectors ρ.representation K.toSubgroup) := ⟨rfl⟩
  have hfin : (u '' tsupport (matrixCoefficient ρ.representation Λ ξ)).Finite :=
    (hsupp.isCompact.image hu.continuous).finite_of_discrete
  have hbfin : b.Finite := by
    refine hfin.subset fun x hx => ?_
    obtain ⟨g, rfl⟩ := hbu hx
    refine ⟨g, subset_tsupport _ ?_, rfl⟩
    rw [Function.mem_support, hcoef]
    have hB : B ⟨u g, hx⟩ = u g := Module.Basis.mk_apply hbli _ _
    rw [← hB, B.sumCoords_self_apply]
    exact one_ne_zero
  have : Finite b := hbfin.to_subtype
  exact Module.Finite.of_basis B

end Langlands.Cohomology.SupercuspidalExtCharZero
