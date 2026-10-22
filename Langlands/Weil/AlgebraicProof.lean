import Langlands.Weil.Algebraic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite

/-! # Algebraic properties of the integer-Frobenius pullback -/

namespace Langlands.Weil

universe u

/-- A nonzero integer survives in the finite cyclic group of order `|n| + 1`. -/
theorem degree_residuallyFinite : Group.ResiduallyFinite Degree := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  let n := g.toAdd.natAbs + 1
  let : NeZero n := ⟨Nat.succ_ne_zero _⟩
  refine ⟨Multiplicative (ZMod n), inferInstance, inferInstance,
    (Int.castAddHom (ZMod n)).toMultiplicative, ?_⟩
  intro h
  change (g.toAdd : ZMod n) = 0 at h
  have hd : n ∣ g.toAdd.natAbs :=
    Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hp : 0 < g.toAdd.natAbs := Int.natAbs_pos.mpr hg
  exact Nat.not_succ_le_self _ (Nat.le_of_dvd hp hd)

/-- The canonical integer map into its actual profinite completion is injective. -/
theorem frobenius_injective : Function.Injective frobenius := by
  exact (ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (GrpCat.of Degree)).mpr degree_residuallyFinite

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
variable (φ : Γ →ₜ* ProfiniteIntegers)

/-- The two images of a pullback element agree. -/
theorem pullback_commutes :
    φ.comp (projection φ) = frobenius.comp (degree φ) := by
  ext w
  exact w.property

/-- The first coordinate determines the second because integer Frobenius is injective. -/
theorem projection_injective : Function.Injective (projection φ) := by
  intro x y h
  apply Subtype.ext
  refine Prod.ext h ?_
  apply frobenius_injective
  exact x.property.symm.trans ((congrArg φ h).trans y.property)

/-- Projection has precisely the integer-Frobenius preimage as its image. -/
theorem projection_range :
    (projection φ).toMonoidHom.range =
      frobenius.toMonoidHom.range.comap φ.toMonoidHom := by
  ext g
  change (∃ w : Pullback φ, projection φ w = g) ↔
    (∃ n : Degree, frobenius n = φ g)
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨degree φ w, w.property.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨(g, n), hn.symm⟩, rfl⟩

/-- Inertia inclusion retains its original first coordinate. -/
theorem inertiaInclusion_injective : Function.Injective (inertiaInclusion φ) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (projection φ) h

/-- Projection after inertia inclusion is the original subgroup inclusion. -/
theorem projection_comp_inertiaInclusion :
    (projection φ).toMonoidHom.comp (inertiaInclusion φ).toMonoidHom =
      (inertia φ).subtype := by
  ext x
  rfl

/-- Original inertia maps onto exactly the degree-zero subgroup. -/
theorem inertiaInclusion_range :
    (inertiaInclusion φ).toMonoidHom.range = inertiaSubgroup φ := by
  ext w
  change (∃ x : inertia φ, inertiaInclusion φ x = w) ↔ degree φ w = 1
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hw
    have hx : φ (projection φ w) = 1 := by
      calc
        φ (projection φ w) = frobenius (degree φ w) := w.property
        _ = 1 := by rw [hw, map_one]
    refine ⟨⟨projection φ w, hx⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hw.symm

/-- A surjective input homomorphism supplies a pullback element of every degree. -/
theorem degree_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (degree φ) := by
  intro n
  obtain ⟨g, hg⟩ := hφ (frobenius n)
  exact ⟨⟨(g, n), hg⟩, rfl⟩

/-- The entire accepted algebraic interface, uniformly in the group universe. -/
theorem algebraicProperties : AlgebraicProperties.{u} := by
  refine ⟨frobenius_injective, ?_⟩
  intro Γ _ _ φ
  exact ⟨pullback_commutes φ, projection_injective φ, projection_range φ,
    inertiaInclusion_injective φ, projection_comp_inertiaInclusion φ,
    inertiaInclusion_range φ, degree_surjective φ⟩

end Langlands.Weil
