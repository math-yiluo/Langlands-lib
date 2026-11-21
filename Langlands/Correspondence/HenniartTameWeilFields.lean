import Langlands.Correspondence.HenniartWeilTameAveraging
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Degree-`m` tame fields and Frobenius cosets in the actual Weil group
-/

noncomputable section

namespace Langlands.Henniart

open Weil.Local

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- The image of the Weil group of an actual degree-`m` tame extension,
using the inclusion induced by the prescribed intermediate field. -/
abbrev tameFieldWeilImage {m : ℕ} (E : TameTotallyRamifiedExtensions K m) :
    Subgroup (localWeilGroup K) := (intermediateWeilMap K E.1).toMonoidHom.range

/-- The quotient of Weil inertia by an open normal subgroup of the Weil group,
viewed as a quotient of inertia itself. -/
abbrev tameInertiaCosets (J : OpenNormalSubgroup (localWeilGroup K)) :=
  localInertia K ⧸ J.toSubgroup.subgroupOf (localInertia K)

/-- A common inertia kernel and the parametrization of actual tame totally
ramified fields by the translates of a chosen Frobenius lift. -/
structure TameWeilFrobeniusData (m : ℕ) (φ : localWeilGroup K) where
  kernel : OpenNormalSubgroup (localWeilGroup K)
  kernel_le_inertia : kernel.toSubgroup ≤ localInertia K
  cosetEquiv : Fin m ≃ tameInertiaCosets K kernel
  fieldEquiv : tameInertiaCosets K kernel ≃ TameTotallyRamifiedExtensions K m
  inertiaIntersection (a : tameInertiaCosets K kernel) :
    tameFieldWeilImage K (fieldEquiv a) ⊓ localInertia K = kernel.toSubgroup
  frobenius_mem (g : localInertia K) :
    (g : localWeilGroup K) * φ ∈ tameFieldWeilImage K (fieldEquiv (QuotientGroup.mk g))

/-- Over a p-adic field, all the degree-`m` tame totally ramified intermediate
fields are parametrized by the translates of any fixed degree-one lift,
modulo a common open normal subgroup of inertia of index `m`. -/
def TameWeilFrobeniusParametrizationStatement.{uK} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (m : ℕ), ¬ p ∣ m →
    ∀ (φ : localWeilGroup K), localDegreeInt K φ = 1 → Nonempty (TameWeilFrobeniusData K m φ)

end Langlands.Henniart
