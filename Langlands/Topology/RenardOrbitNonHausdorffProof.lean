import Langlands.Topology.RenardOrbitNonHausdorffStatement
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Int

/-! # Renard II.3.3: a non-Hausdorff orbit quotient

The discrete group `Multiplicative ℤ` acts on the one-point compactification
`OnePoint ℤ` of the discrete integers by translation, fixing `∞`. The two orbits
are `ℤ` and `{∞}`; every open neighbourhood of `∞` meets `ℤ`, so their classes
cannot be separated in the quotient topology.
-/

set_option autoImplicit false

namespace Langlands.Topology.RenardOrbitQuotient

open OnePoint

/-- Translation of `OnePoint ℤ` by the integer underlying `g : Multiplicative ℤ`,
fixing the point at infinity. -/
@[instance_reducible]
def translationAction : MulAction (Multiplicative ℤ) (OnePoint ℤ) where
  smul g x := OnePoint.map (fun m : ℤ => Multiplicative.toAdd g + m) x
  one_smul x := by
    induction x using OnePoint.rec with
    | infty => rfl
    | coe m =>
      change ((Multiplicative.toAdd (1 : Multiplicative ℤ) + m : ℤ) : OnePoint ℤ) = m
      rw [toAdd_one, zero_add]
  mul_smul g h x := by
    induction x using OnePoint.rec with
    | infty => rfl
    | coe m =>
      change ((Multiplicative.toAdd (g * h) + m : ℤ) : OnePoint ℤ) =
        ((Multiplicative.toAdd g + (Multiplicative.toAdd h + m) : ℤ) : OnePoint ℤ)
      rw [toAdd_mul, add_assoc]

attribute [local instance] translationAction

theorem smul_infty (g : Multiplicative ℤ) : g • (∞ : OnePoint ℤ) = ∞ :=
  rfl

theorem smul_coe (g : Multiplicative ℤ) (m : ℤ) :
    g • (m : OnePoint ℤ) = ((Multiplicative.toAdd g + m : ℤ) : OnePoint ℤ) :=
  rfl

/-- Each translation is the one-point extension of a homeomorphism of `ℤ`; the
group is discrete, so joint continuity reduces to these. -/
theorem translation_continuousSMul : ContinuousSMul (Multiplicative ℤ) (OnePoint ℤ) := by
  refine ⟨continuous_prod_of_discrete_left.mpr fun g => ?_⟩
  exact (Homeomorph.onePointCongr (Homeomorph.addLeft (Multiplicative.toAdd g))).continuous

theorem isLocallyProfinite_group : IsLocallyProfinite (Multiplicative ℤ) :=
  isLocallyProfinite_of_mathlib

theorem isLocallyProfinite_space : IsLocallyProfinite (OnePoint ℤ) :=
  isLocallyProfinite_of_weaklyLocallyCompactSpace

/-- The orbit classes of `∞` and of `0` cannot be separated. -/
theorem not_t2Space_orbitQuotient :
    ¬ T2Space (Quotient (MulAction.orbitRel (Multiplicative ℤ) (OnePoint ℤ))) := by
  intro hT2
  let π : OnePoint ℤ → Quotient (MulAction.orbitRel (Multiplicative ℤ) (OnePoint ℤ)) :=
    Quotient.mk _
  have hne : π ∞ ≠ π ((0 : ℤ) : OnePoint ℤ) := by
    intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg' : ((Multiplicative.toAdd g + 0 : ℤ) : OnePoint ℤ) = ∞ := hg
    exact OnePoint.coe_ne_infty _ hg'
  obtain ⟨U, V, hU, hV, hUinf, hV0, hUV⟩ := t2_separation hne
  have hUo : IsOpen (π ⁻¹' U) := hU.preimage continuous_quot_mk
  obtain ⟨m, hm⟩ := OnePoint.denseRange_coe.exists_mem_open hUo ⟨∞, hUinf⟩
  have hmV : π (m : OnePoint ℤ) ∈ V := by
    have hπ : π (m : OnePoint ℤ) = π ((0 : ℤ) : OnePoint ℤ) := by
      apply Quotient.sound
      refine ⟨Multiplicative.ofAdd m, ?_⟩
      change ((Multiplicative.toAdd (Multiplicative.ofAdd m) + 0 : ℤ) : OnePoint ℤ) = m
      rw [toAdd_ofAdd, add_zero]
    rw [hπ]
    exact hV0
  exact Set.disjoint_left.mp hUV hm hmV

/-- Proof of `NonHausdorffOrbitQuotientStatement` by the translation action of
the discrete integers on their one-point compactification. -/
theorem nonHausdorffOrbitQuotient : NonHausdorffOrbitQuotientStatement :=
  ⟨Multiplicative ℤ, OnePoint ℤ, inferInstance, inferInstance, inferInstance,
    translationAction, inferInstance, translation_continuousSMul, isLocallyProfinite_group,
    isLocallyProfinite_space, not_t2Space_orbitQuotient⟩

end Langlands.Topology.RenardOrbitQuotient
