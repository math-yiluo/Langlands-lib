import Langlands.Galois.FiniteHeckeAvatarLift
import Langlands.Galois.FiniteUnramifiedGaloisRestrictionProof
import Langlands.Galois.FrobeniusDensity
import Langlands.Global.Arithmetic.ClassFieldProof
import Langlands.Global.Arithmetic.FiniteArtinUnramifiedCriterionProof
import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness
import Langlands.ClassFieldTheory.Global.Artin.ArtinMap
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtin
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinNormalization

/-!
# Geometrically normalized lifts of finite idèle-class characters

This file proves `Langlands.GaloisRepresentation.FiniteHeckeAvatarLiftStatement` and,
unconditionally, `FiniteGeometricArtinLifting`: a continuous character `ξ` of the idèle classes
of a number field `K` into a finite abelian group `A` (discrete topology), trivial on the local
units at the finite places outside a finite set `S`, has a unique continuous lift `ψ` to the
absolute Galois group that is trivial on local inertia outside `S` and takes every geometric
Frobenius lift at `v ∉ S` to `ξ` of a uniformizer at `v`.

**Existence** uses the three premises of the statement. The kernel of `ξ` is open of finite
index; its class field `L` (first premise) comes with a continuous surjective normalized map
`ρ` onto `Gal(L/K)` with the same kernel, so `ξ = θ ∘ ρ` with `θ` injective. The lift is
`g ↦ θ ((g|_L)⁻¹)`. Outside `S`, `ρ` kills the local units, so `L / K` is unramified there
(second premise); restriction kills inertia and sends the inverse of a geometric Frobenius lift
to an arithmetic Frobenius (third premise), which by the normalization of `ρ` and the uniqueness
of an arithmetic Frobenius at an unramified prime is `ρ` of a uniformizer.

**Uniqueness** uses neither the premises nor class field theory: two lifts agree on the images
of the chosen geometric Frobenius lifts outside `S`, hence (the target being commutative) on
their conjugates, which are dense (`dense_conjugates_globalGeometricFrobenius_degreeOne`); the
set where two continuous maps into a Hausdorff space agree is closed.

With the premises proved (`finiteAbelianClassFieldExistence`, `finiteArtinUnramifiedCriterion`,
`finiteUnramifiedGaloisRestriction`) this gives `finiteGeometricArtinLifting`. Through the
global Artin map `geometricArtinMap K` the lift is `ξ` carried to the Galois side: if `σ` lifts
`geometricArtinMap K x` to the absolute Galois group, then `ψ σ = ξ x`
(`MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap`).

## Main declarations

* `MatchesGeometricArtinOutside.isTrivialOnLocalUnits`, `MatchesGeometricArtinOutside.unique`.
* `exists_matchesGeometricArtinOutside`: existence from the three premises.
* `finiteHeckeAvatarLift`, `finiteGeometricArtinLifting`: the published statements.
* `MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap`: the lift through
  `geometricArtinMap`.
-/

noncomputable section

universe uK uA

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.ClassFieldTheory.Global.Artin
open scoped NumberField

variable {K : Type uK} [Field K] [NumberField K] {A : Type uA} [TopologicalSpace A]

/-- If a character `ψ` of the absolute Galois group matches `ξ` at a place `v ∉ S`, then `ξ` is
trivial on the local units at `v`: a unit times a uniformizer is a uniformizer, and both have
the value of `ψ` at a geometric Frobenius lift. -/
theorem MatchesGeometricArtinOutside.isTrivialOnLocalUnits [Group A]
    {S : Finset (FinitePlace K)} {ξ : IdeleClasses K →ₜ* A}
    {ψ : Field.absoluteGaloisGroup K →ₜ* A} (h : MatchesGeometricArtinOutside S ξ ψ)
    {v : FinitePlace K} (hv : v ∉ S) : IsTrivialOnLocalUnits ξ v := by
  intro a ha
  obtain ⟨π, hπ⟩ := exists_uniformizer v
  obtain ⟨g, hg⟩ := exists_geometricFrobeniusLift v
  rw [Submonoid.mem_units_iff] at ha
  have hval : Valued.v (a : FiniteCompletion K v) = 1 := by
    refine le_antisymm ha.1 ?_
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (a : FiniteCompletion K v) *
            Valued.v ((a⁻¹ : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) := by
          rw [← map_mul, Units.mul_inv, map_one]
      _ ≤ Valued.v (a : FiniteCompletion K v) := mul_le_of_le_one_right' ha.2
  have hπ' : Valued.v ((a * π : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) =
      WithZero.exp (-1 : ℤ) := by
    rw [Units.val_mul, map_mul, hval, one_mul, hπ]
  have e := ((h v hv).2 (a * π) hπ' g hg).symm.trans ((h v hv).2 π hπ g hg)
  rw [map_mul, map_mul, mul_eq_right] at e
  exact e

variable [CommGroup A]

/-- Two continuous characters of the absolute Galois group with values in a commutative
Hausdorff group that both match `ξ` outside `S` are equal. -/
theorem MatchesGeometricArtinOutside.unique [T2Space A] {S : Finset (FinitePlace K)}
    {ξ : IdeleClasses K →ₜ* A} {ψ₁ ψ₂ : Field.absoluteGaloisGroup K →ₜ* A}
    (h₁ : MatchesGeometricArtinOutside S ξ ψ₁) (h₂ : MatchesGeometricArtinOutside S ξ ψ₂) :
    ψ₁ = ψ₂ := by
  have hclosed : IsClosed {g : Field.absoluteGaloisGroup K | ψ₁ g = ψ₂ g} :=
    isClosed_eq ψ₁.continuous ψ₂.continuous
  have hsub : {g : Field.absoluteGaloisGroup K | ∃ v : FinitePlace K,
      v ∉ S ∧ (residueCardinality v).Prime ∧
        ∃ t : Field.absoluteGaloisGroup K, t * globalGeometricFrobenius v * t⁻¹ = g} ⊆
      {g | ψ₁ g = ψ₂ g} := by
    rintro _ ⟨v, hv, -, t, rfl⟩
    obtain ⟨π, hπ⟩ := exists_uniformizer v
    have e₁ := (h₁ v hv).2 π hπ (geometricFrobeniusLift v) (geometricFrobeniusLift_spec v)
    have e₂ := (h₂ v hv).2 π hπ (geometricFrobeniusLift v) (geometricFrobeniusLift_spec v)
    change ψ₁ (t * globalGeometricFrobenius v * t⁻¹) = ψ₂ (t * globalGeometricFrobenius v * t⁻¹)
    simp only [map_mul, map_inv, mul_inv_cancel_comm]
    exact e₁.trans e₂.symm
  have hall := (dense_conjugates_globalGeometricFrobenius_degreeOne (K := K) S).closure_eq ▸
    closure_minimal hsub hclosed
  ext g
  exact hall (Set.mem_univ g)

/-- The candidate lift through a finite Galois subextension `L` and a homomorphism `θ` from its
Galois group: `g ↦ θ ((g|_L)⁻¹)`, a homomorphism because `A` is commutative, continuous because
`Gal(L/K)` is discrete. -/
private def finiteRestrictionLift (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L] (θ : (L ≃ₐ[K] L) →* A) :
    Field.absoluteGaloisGroup K →ₜ* A where
  toFun g := θ (finiteGaloisRestriction L g)⁻¹
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_inv_rev]
    exact mul_comm _ _
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun s : L ≃ₐ[K] L => θ s⁻¹)).comp
      (finiteGaloisRestriction L).continuous

omit [TopologicalSpace A] in
/-- A homomorphism with the same kernel as a surjective homomorphism `ρ` factors through `ρ` by an
injective homomorphism. -/
private theorem exists_injective_comp_eq {G H : Type*} [Group G] [Group H] {ρ : G →* H}
    (hρ : Function.Surjective ρ) (ξ : G →* A) (hker : ρ.ker = ξ.ker) :
    ∃ θ : H →* A, Function.Injective θ ∧ ∀ x, θ (ρ x) = ξ x := by
  let θ : H →* A := ρ.liftOfRightInverse (Function.surjInv hρ)
    (Function.rightInverse_surjInv hρ) ⟨ξ, hker.le⟩
  have hθ : ∀ x, θ (ρ x) = ξ x := fun x =>
    ρ.liftOfRightInverse_comp_apply _ _ ⟨ξ, hker.le⟩ x
  refine ⟨θ, ?_, hθ⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨x, rfl⟩ := hρ y
  have hx : x ∈ ξ.ker := (hθ x).symm.trans hy
  rw [← hker] at hx
  exact hx

/-- Given the second and third premises, the candidate lift through a finite abelian `L` with a
continuous surjective normalized map `ρ` and `ξ = θ ∘ ρ`, `θ` injective, matches `ξ` outside
`S`. -/
private theorem matchesGeometricArtinOutside_finiteRestrictionLift
    (h2 : FiniteArtinUnramifiedCriterionStatement.{uK, uK})
    (h3 : FiniteUnramifiedGaloisRestrictionStatement.{uK})
    {ξ : IdeleClasses K →ₜ* A} {S : Finset (FinitePlace K)}
    (hS : ∀ v ∉ S, IsTrivialOnLocalUnits ξ v)
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (ρ : letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥; IdeleClasses K →ₜ* (L ≃ₐ[K] L))
    (hsurj : letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥; Function.Surjective ρ)
    (hnorm : letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
      letI := NumberField.of_module_finite K L
      HasArithmeticArtinNormalization ρ.toMonoidHom)
    (θ : (L ≃ₐ[K] L) →* A) (hθinj : Function.Injective θ)
    (hθ : letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥; ∀ x, θ (ρ x) = ξ x) :
    MatchesGeometricArtinOutside S ξ (finiteRestrictionLift L θ) := by
  let := NumberField.of_module_finite K L
  refine fun v hv => ?_
  have hunits : ∀ a : (FiniteCompletion K v)ˣ,
      a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units →
        ρ (finiteClassInclusion K v a) = 1 := fun a ha =>
    hθinj ((hθ _).trans ((hS v hv a ha).trans (map_one θ).symm))
  obtain ⟨w, hw⟩ := exists_liesOver K L v
  have hunram := h2 K L hcomm ρ hsurj hnorm v hunits w hw
  obtain ⟨hin, hfrob⟩ := h3 K L hcomm v w hw hunram
  refine ⟨fun i => ?_, fun π hπ g hg => ?_⟩
  · change θ (finiteGaloisRestriction L (localToGlobalGalois v i.val))⁻¹ = 1
    rw [hin i, inv_one, map_one]
  · have heq : finiteGaloisRestriction L (localToGlobalGalois v g⁻¹) =
        ρ (finiteClassInclusion K v π) :=
      eq_of_isArithFrobAt_mapAlgHom w hunram (hfrob g hg) (hnorm v w hw hunram π hπ)
    change θ (finiteGaloisRestriction L (localToGlobalGalois v g))⁻¹ =
      ξ (finiteClassInclusion K v π)
    rw [← map_inv, ← map_inv, heq]
    exact hθ _

/-- Existence of the lift from the three premises of `FiniteHeckeAvatarLiftStatement`. -/
theorem exists_matchesGeometricArtinOutside
    (h1 : FiniteAbelianClassFieldExistenceStatement.{uK})
    (h2 : FiniteArtinUnramifiedCriterionStatement.{uK, uK})
    (h3 : FiniteUnramifiedGaloisRestrictionStatement.{uK})
    [Finite A] [DiscreteTopology A] (ξ : IdeleClasses K →ₜ* A) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, IsTrivialOnLocalUnits ξ v) :
    ∃ ψ : Field.absoluteGaloisGroup K →ₜ* A, MatchesGeometricArtinOutside S ξ ψ := by
  obtain ⟨L, hfin, hgal, hcomm, ρ, hsurj, hnorm, hker⟩ :=
    h1 K ⟨ξ.toMonoidHom.ker, (isOpen_discrete ({1} : Set A)).preimage ξ.continuous⟩
      (Subgroup.finiteIndex_ker ξ.toMonoidHom)
  let := hfin
  obtain ⟨θ, hθinj, hθ⟩ := exists_injective_comp_eq hsurj ξ.toMonoidHom hker
  exact ⟨_, matchesGeometricArtinOutside_finiteRestrictionLift h2 h3 hS L hcomm ρ hsurj hnorm θ
    hθinj hθ⟩

/-- The lift through the global Artin map: if `ψ` matches `ξ` outside some `S` and `σ` in the
absolute Galois group lifts `geometricArtinMap K x`, then `ψ σ = ξ x`. -/
theorem MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap [Finite A]
    [DiscreteTopology A] {S : Finset (FinitePlace K)} {ξ : IdeleClasses K →ₜ* A}
    {ψ : Field.absoluteGaloisGroup K →ₜ* A} (hψ : MatchesGeometricArtinOutside S ξ ψ)
    (x : IdeleClasses K) (σ : Field.absoluteGaloisGroup K)
    (hσ : LocalClassField.absoluteAbelianizationProjection K σ = geometricArtinMap K x) :
    ψ σ = ξ x := by
  obtain ⟨L, hfin, hgal, hcomm, ρ, hsurj, hnorm, hker⟩ :=
    finiteAbelianClassFieldExistence K
      ⟨ξ.toMonoidHom.ker, (isOpen_discrete ({1} : Set A)).preimage ξ.continuous⟩
      (Subgroup.finiteIndex_ker ξ.toMonoidHom)
  let := hfin
  let := NumberField.of_module_finite K L
  have : IsAbelianGalois K L := { toIsMulCommutative := IsMulCommutative.of_comm hcomm }
  obtain ⟨θ, hθinj, hθ⟩ := exists_injective_comp_eq hsurj ξ.toMonoidHom hker
  rw [hψ.unique (matchesGeometricArtinOutside_finiteRestrictionLift finiteArtinUnramifiedCriterion
    finiteUnramifiedGaloisRestriction (fun v hv => hψ.isTrivialOnLocalUnits hv) L hcomm ρ hsurj
    hnorm θ hθinj hθ)]
  let : TopologicalSpace (L ≃ₐ[K] L) := ⊥
  have hρ : ρ = arithmeticFiniteArtinBot K L :=
    eq_of_hasArithmeticArtinNormalization ρ _ hnorm
      arithmeticFiniteArtin_hasArithmeticArtinNormalization
  change θ (AlgEquiv.restrictNormalHom L σ)⁻¹ = ξ x
  rw [restrictNormalHom_eq_inv_arithmeticFiniteArtin L x σ hσ, inv_inv]
  refine (congrArg θ ?_).trans (hθ x)
  rw [hρ]
  rfl

/-- The three premises give the unique geometrically normalized lift. -/
theorem finiteHeckeAvatarLift : FiniteHeckeAvatarLiftStatement.{uK, uA} := by
  intro h1 h2 h3 K _ _ A _ _ ξ S hS
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_matchesGeometricArtinOutside h1 h2 h3 ξ S hS
  exact ⟨ψ, hψ, fun ψ' hψ' => hψ'.unique hψ⟩

/-- A continuous character of the idèle classes into a finite abelian group, trivial on the local
units outside a finite set `S`, has a unique continuous lift to the absolute Galois group that
is trivial on inertia outside `S` and takes geometric Frobenius lifts to the values at
uniformizers. -/
theorem finiteGeometricArtinLifting : FiniteGeometricArtinLifting.{uK, uA} :=
  finiteHeckeAvatarLift finiteAbelianClassFieldExistence finiteArtinUnramifiedCriterion
    finiteUnramifiedGaloisRestriction

end Langlands.GaloisRepresentation
