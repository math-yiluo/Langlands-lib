/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity
public import WeilConjectures.Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import WeilConjectures.Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.DirectSum.Basis

/-!
# Purity of real lisse Weil sheaves on curves

This file states the climax of the block: an `ι`-real lisse Weil sheaf on a smooth
geometrically connected curve over a finite field is, constituent by constituent, punctually
`ι`-pure of the expected weight.

The route is the classical one. A rank-one lisse Weil sheaf has finite geometric image
(`AlgebraicGeometry.WeilGroup.IsLisse.finite_geometric_image`), hence is punctually pure of
the weight of its Frobenius scalar
(`AlgebraicGeometry.WeilGroup.IsLisse.isPunctuallyPure_of_finrank_eq_one`). The
Rankin–Selberg argument, applied to the even tensor powers of a real sheaf on an affine curve,
turns a bound on the determinant weights of the constituents into a bound on all local
eigenvalues (`AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal`). Semi-continuity
propagates a weight bound across the boundary of an open subcurve
(`AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_of_hasWeightsAtMost`). Finally an
exterior power of the semisimplification squeezes the eigenvalues of a single weight block
from both sides on an affine curve
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine`), and
restricting to an affine open neighbourhood of each closed point gives the general case
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`, using the transfer
lemmas of `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Restriction`).

## Implementation notes

The arithmetic and geometric monodromy groups of `definition-monodromy-groups--1` are the Zariski
closures of `ρ (W (C₀))` and `ρ (π₁ C)` inside `GL V`. Zariski closures of subgroups of `GL V`
are owned by the algebraic groups block (`definition-monodromy-groups`,
`proposition-central-element-arithmetic-monodromy-group--1`) and do not exist here; only the map
`AlgebraicGeometry.WeilGroup.toLinearAut` whose images they are closures of is recorded, and the
positive central Frobenius representative of
`proposition-central-element-arithmetic-monodromy-group--1` is left to that block.

An `AlgebraicGeometry.WeilGroup p` is presented through the étale fundamental group of the
curve `C₀` over `𝔽_q`; the identification of its geometric part `ker deg` with the étale
fundamental group of the geometric curve `C = C₀ ×_{𝔽_q} 𝔽̄_q` (the homotopy exact sequence) is
not available. The rank-one theorems, and everything downstream of them, therefore assume it, in
the form `AlgebraicGeometry.WeilGroup.IsEtaleQuotient` (the geometric part of `W` is,
Frobenius-equivariantly, the étale fundamental group of `C`), together with `ℓ ≠ char 𝔽_q`,
without which they are false (for `ℓ = p` the character of a Frobenius-invariant
Artin–Schreier–Witt tower has infinite geometric image). The Rankin–Selberg statements
moreover use the Grothendieck–Lefschetz trace formula relating
`AlgebraicGeometry.WeilGroup.eulerSeries` to compactly supported cohomology, which is
recorded without proof in `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin`.

## Main definitions

- `AlgebraicGeometry.WeilGroup.toLinearAut`

## Main statements

- `AlgebraicGeometry.WeilGroup.IsLisse.finite_geometric_image`
- `AlgebraicGeometry.WeilGroup.IsLisse.isPunctuallyPure_of_finrank_eq_one`
- `AlgebraicGeometry.WeilGroup.le_add_of_isConstituent_tprod_of_hasDetWeight`: the determinant
  weights of the constituents of a tensor product are bounded by the sum of the bounds.
- `AlgebraicGeometry.WeilGroup.frobeniusWeight_le_add_inv_two_pow_of_isReal`: the Rankin–Selberg
  bound for the iterated tensor squares.
- `AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal`, and its unfolded form
  `AlgebraicGeometry.WeilGroup.sq_norm_le_rpow_of_isReal`
- `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_of_hasWeightsAtMost`
- `AlgebraicGeometry.BoundaryDatum.isPunctuallyPure_of_isPunctuallyPure_restrict`
- `AlgebraicGeometry.WeilGroup.IsLisse.hasDetWeight`: every lisse Weil sheaf has a determinant
  weight, read off from the rank-one determinant line.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_subquotient_of_isReal`: the composition factors
  of a real lisse Weil sheaf on an affine curve are pure of their determinant weights.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine`
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`
-/

@[expose] public section

universe u

open CategoryTheory

/- `Mathlib.AlgebraicGeometry.Group.Affine` (imported through linear algebraic groups) makes
`Spec k` an object over itself through `specOverSpec`, which is not reducibly the identity
structure `CategoryTheory.instOverClass` used by Weil sheaves on `Spec k`. Prefer the latter
in this file. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V)

/-- Blueprint `definition-monodromy-groups--1`: Arithmetic monodromy and a central representative.

The Weil representation `ρ` viewed as a homomorphism to the automorphism group of `V`: every
`ρ g` is invertible because `g` is invertible, so `ρ` factors through `GL V = (V →ₗ V)ˣ`,
which is multiplicatively equivalent to `V ≃ₗ V`. The arithmetic and geometric monodromy
groups of `definition-monodromy-groups` are the Zariski closures of the images of `W (C₀)` and of
`π₁ C` under this map. -/
noncomputable def toLinearAut : W.carrier →* (V ≃ₗ[PadicAlgCl l] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (PadicAlgCl l) V).toMonoidHom.comp
    ρ.asGroupHom

variable (ι : PadicAlgCl l →+* ℂ)

variable {W l} in
/-- The determinant of a lisse Weil representation is continuous on the geometric part: in a
basis it is a polynomial in the matrix coefficients. -/
theorem IsLisse.continuous_detCharacter (hρ : W.IsLisse l ρ) :
    Continuous fun g : W.geometric ↦ (ρ.detCharacter g : PadicAlgCl l) := by
  let b := Module.finBasis (PadicAlgCl l) V
  have h : Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ hρ.continuous_toMatrix b i j
  simpa only [Representation.coe_detCharacter_apply, LinearMap.det_toMatrix] using h.matrix_det

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Purity of rank-one Weil sheaves.

The geometric image `χ (π₁ U)` of a rank-one lisse Weil sheaf on a smooth geometrically
connected curve `U₀ / 𝔽_q` is finite, for `ℓ ≠ p` and a Weil group linked to the étale
fundamental group (`AlgebraicGeometry.WeilGroup.IsEtaleQuotient`).

This is the heart of the matter: the `ℓ`-adic logarithm turns an `N`-th power of `χ`
restricted to `π₁ U` into a continuous additive map invariant under conjugation by `γ`, and
such a map is a Frobenius-fixed class in `H¹ (U, ℚ̄_ℓ)`, which vanishes because on a proper
curve `H¹` is dual to a Tate module with no Frobenius-fixed vector, and the boundary
contribution for an open curve is a nonzero power of `q`
(`AlgebraicGeometry.WeilGroup.finite_range_of_continuous`, applied to `χ = det ρ`). -/
theorem IsLisse.finite_geometric_image [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient]
    (hrank : Module.finrank (PadicAlgCl l) V = 1) (hρ : W.IsLisse l ρ) :
    (Set.range fun g : W.geometric ↦ ρ g).Finite := by
  have hfin := W.finite_range_of_continuous ρ.detCharacter hρ.continuous_detCharacter
  refine (hfin.image fun c : (PadicAlgCl l)ˣ ↦
    (c : PadicAlgCl l) • (LinearMap.id : V →ₗ[PadicAlgCl l] V)).subset ?_
  rintro _ ⟨g, rfl⟩
  refine ⟨ρ.detCharacter g, ⟨g, rfl⟩, ?_⟩
  dsimp only
  rw [Representation.coe_detCharacter_apply, ← LinearMap.eq_det_smul_id_of_finrank_eq_one hrank]

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: Purity of rank-one Weil sheaves.

A rank-one lisse Weil sheaf `L` on a smooth geometrically connected curve `U₀ / 𝔽_q`, with
character `χ : W (U₀) → ℚ̄_ℓ ˣ`, is punctually `ι`-pure of weight
`w = 2 log |ι c| / log q`, where `c = χ γ` is the value at the chosen degree-one lift; here
`ℓ ≠ p` and the Weil group is linked to the étale fundamental group
(`AlgebraicGeometry.WeilGroup.IsEtaleQuotient`).

Once the geometric image is finite (`AlgebraicGeometry.WeilGroup.IsLisse.finite_geometric_image`),
`χ` is a root of unity times the constant character `c ^ deg`, so the local scalar at a point
of degree `e` has complex modulus `|ι c| ^ e = q ^ (e * w / 2)`
(`AlgebraicGeometry.WeilGroup.frobeniusWeight_eq_of_continuous`). -/
theorem IsLisse.isPunctuallyPure_of_finrank_eq_one [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient]
    (hrank : Module.finrank (PadicAlgCl l) V = 1) (hρ : W.IsLisse l ρ) :
    W.IsPunctuallyPure l ρ ι
      (frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift))) := by
  intro x α hα
  have hα' : α = LinearMap.det (ρ (W.frobenius x)) := by
    rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα
    obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hv
    conv at hv => lhs; rw [LinearMap.eq_det_smul_id_of_finrank_eq_one hrank (ρ _)]
    exact (smul_left_injective _ hv0 hv).symm
  rw [hα', ← Representation.coe_detCharacter_apply, ← Representation.coe_detCharacter_apply]
  exact W.frobeniusWeight_eq_of_continuous ρ.detCharacter hρ.continuous_detCharacter ι x

end WeilGroup

namespace WeilGroup

section DetWeight

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V V' : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] [FiniteDimensional (PadicAlgCl l) V']
  {ρ : Representation (PadicAlgCl l) W.carrier V} (ι : PadicAlgCl l →+* ℂ)

omit [Finite K] [IsCurve p] in
/-- The determinant line `ULift ℚ̄_ℓ` is one-dimensional. -/
theorem finrank_ulift_padicAlgCl :
    Module.finrank (PadicAlgCl l) (ULift.{u} (PadicAlgCl l)) = 1 :=
  (ULift.moduleEquiv (R := PadicAlgCl l) (M := PadicAlgCl l)).finrank_eq.trans
    (Module.finrank_self _)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The determinant line `ULift ℚ̄_ℓ` with `g` acting by `det ρ(g)` has determinant `det ρ`. -/
theorem det_ofCharacter_detCharacter (g : W.carrier) :
    LinearMap.det (Representation.ofCharacter ρ.detCharacter (ULift.{u} (PadicAlgCl l)) g) =
      LinearMap.det (ρ g) := by
  change LinearMap.det ((ρ.detCharacter g : PadicAlgCl l) •
    (LinearMap.id : ULift.{u} (PadicAlgCl l) →ₗ[PadicAlgCl l] ULift.{u} (PadicAlgCl l))) = _
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_ulift_padicAlgCl, pow_one,
    Representation.coe_detCharacter_apply]

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The local eigenvalue of the determinant line at `x` is `det ρ(F_x)`. -/
theorem det_mem_localEigenvalues_ofCharacter (x : C.finitePoints) :
    LinearMap.det (ρ (W.frobenius x)) ∈
      W.localEigenvalues l (Representation.ofCharacter ρ.detCharacter (ULift.{u} (PadicAlgCl l)))
        x := by
  rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ULift.up 1) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Representation.ofCharacter_apply,
      Representation.coe_detCharacter_apply]
  · exact fun h ↦ one_ne_zero (congrArg ULift.down h)

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]

/-- Blueprint `theorem-rank-one-sheaves-have-finite` (`corollary-determinant-weights--1`): a lisse
Weil representation `ρ` has determinant weight `wt_{ι, q}(det ρ(γ)) / rank ρ`, for the degree-one
lift `γ`: its determinant line is a rank-one lisse sheaf, hence punctually pure of the weight
of its Frobenius scalar. -/
theorem IsLisse.hasDetWeight [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient] (hρ : W.IsLisse l ρ) :
    W.HasDetWeight l ρ ι (frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift)) /
      Module.finrank (PadicAlgCl l) V) := by
  intro x
  have h := IsLisse.isPunctuallyPure_of_finrank_eq_one W l _ ι finrank_ulift_padicAlgCl
    (hρ.ofCharacter_detCharacter _) x _ (det_mem_localEigenvalues_ofCharacter x)
  rw [det_ofCharacter_detCharacter] at h
  rw [h]
  rcases eq_or_ne (Module.finrank (PadicAlgCl l) V) 0 with h0 | h0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    simp [h0, LinearMap.det_eq_one_of_subsingleton, frobeniusWeight]
  · field_simp

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: the determinant of a lisse Weil representation
takes finitely many values on the geometric fundamental group, since the determinant line has finite
geometric image. -/
theorem IsLisse.hasFiniteGeometricDet [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient]
    (hρ : W.IsLisse l ρ) :
    ρ.HasFiniteGeometricDet W.deg := by
  have hfin := IsLisse.finite_geometric_image W l _ finrank_ulift_padicAlgCl
    (hρ.ofCharacter_detCharacter (ULift.{u} (PadicAlgCl l)))
  let f : (PadicAlgCl l)ˣ → Module.End (PadicAlgCl l) (ULift.{u} (PadicAlgCl l)) :=
    fun a ↦ (a : PadicAlgCl l) • LinearMap.id
  have hf : Function.Injective f := fun a b h ↦ Units.ext <| by
    simpa [f] using congrArg ULift.down (LinearMap.congr_fun h (ULift.up 1))
  refine Set.Finite.of_finite_image ?_ hf.injOn
  rw [← Set.range_comp]
  exact hfin

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] in
/-- A nonzero Weil representation has at most one determinant weight, as soon as the curve
has a closed point. -/
theorem HasDetWeight.eq [Nontrivial V] {γ γ' : ℝ} (h : W.HasDetWeight l ρ ι γ)
    (h' : W.HasDetWeight l ρ ι γ') (x : C.finitePoints) : γ = γ' :=
  mul_left_cancel₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') ((h x).symm.trans (h' x))

omit [FiniteDimensional (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V']
  [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] in
/-- Determinant weights are invariant under equivalence of representations. -/
theorem HasDetWeight.of_equiv {σ : Representation (PadicAlgCl l) W.carrier V'} (e : ρ.Equiv σ)
    {γ : ℝ} (h : W.HasDetWeight l ρ ι γ) : W.HasDetWeight l σ ι γ := fun x ↦ by
  rw [e.det_apply, e.finrank_eq]
  exact h x

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] in
/-- Local eigenvalues are invariant under equivalence of representations. -/
theorem localEigenvalues_of_equiv {σ : Representation (PadicAlgCl l) W.carrier V'}
    (e : ρ.Equiv σ) (x : C.finitePoints) :
    W.localEigenvalues l σ x = W.localEigenvalues l ρ x := by
  rw [localEigenvalues, localEigenvalues, e.charpoly_apply]

end DetWeight

section RankinSelberg

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V V' : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] [FiniteDimensional (PadicAlgCl l) V']
  {ρ : Representation (PadicAlgCl l) W.carrier V} {σ : Representation (PadicAlgCl l) W.carrier V'}
  (ι : PadicAlgCl l →+* ℂ)

/-- An irreducible representation is nonzero. -/
private theorem nontrivial_of_isIrreducible {V'' : Type*} [AddCommGroup V'']
    [Module (PadicAlgCl l) V''] {τ : Representation (PadicAlgCl l) W.carrier V''}
    (hτ : τ.IsIrreducible) : Nontrivial V'' := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]

/-- Blueprint `sk-p-tensor`: the determinant weights of the constituents of a tensor product
`ℱ ⊗ 𝒢` of lisse Weil sheaves are bounded by `d₁ + d₂` if those of `ℱ` are bounded by `d₁` and
those of `𝒢` by `d₂`: by the tensor rule a constituent of `ℱ ⊗ 𝒢` has determinant weight
`dw (ℱ_i) + dw (𝒢_j)` for constituents `ℱ_i` of `ℱ` and `𝒢_j` of `𝒢`, and by
`theorem-rank-one-sheaves-have-finite` every lisse Weil sheaf has its determinant weight in the
sense of `AlgebraicGeometry.WeilGroup.HasDetWeight`, which is unique as soon as the curve has a
closed point `x₀`. -/
theorem le_add_of_isConstituent_tprod_of_hasDetWeight [Fact (ringChar K ≠ l)]
    [W.IsEtaleQuotient] (x₀ : C.finitePoints)
    (hρ : W.IsLisse l ρ) (hσ : W.IsLisse l σ) {d₁ d₂ : ℝ}
    (hd₁ : ∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
      [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
      (γ : ℝ), τ.IsConstituent ρ → W.HasDetWeight l τ ι γ → γ ≤ d₁)
    (hd₂ : ∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
      [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
      (γ : ℝ), τ.IsConstituent σ → W.HasDetWeight l τ ι γ → γ ≤ d₂)
    {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
    [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
    (γ : ℝ) (hτ : τ.IsConstituent (ρ.tprod σ)) (hγ : W.HasDetWeight l τ ι γ) :
    γ ≤ d₁ + d₂ := by
  obtain ⟨N, M, hcov, ⟨e⟩⟩ := hτ.exists_covBy
  have hQirr := (Subrepresentation.isIrreducible_subquotient_iff hcov.le).2 hcov
  have hQlisse := (hρ.tprod hσ).subquotient M N
  obtain ⟨UV, SV, UE, SE, hV, hE, hVirr, hEirr, -, -, hsum⟩ :=
    Representation.exists_detWeight_eq_add_of_subquotient_tprod
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift ρ σ
      (fun UV SV _ ↦ (hρ.subquotient SV UV).hasFiniteGeometricDet)
      (fun UE SE _ ↦ (hσ.subquotient SE UE).hasFiniteGeometricDet) hQirr
      hQlisse.hasFiniteGeometricDet
  have h₁ := hd₁ _ _ ⟨hVirr, UV, SV, hV.le, ⟨SV.subquotientAsModuleLinearEquiv UV⟩⟩
    ((hρ.subquotient SV UV).hasDetWeight ι)
  have h₂ := hd₂ _ _ ⟨hEirr, UE, SE, hE.le, ⟨SE.subquotientAsModuleLinearEquiv UE⟩⟩
    ((hσ.subquotient SE UE).hasDetWeight ι)
  have := nontrivial_of_isIrreducible hQirr
  rw [detWeight_weightCharacter, detWeight_weightCharacter, detWeight_weightCharacter] at hsum
  rw [HasDetWeight.eq ι (hγ.of_equiv ι e) (hQlisse.hasDetWeight ι) x₀, hsum]
  exact add_le_add h₁ h₂

/-- The `ι`-weight of a square is twice the `ι`-weight. -/
private theorem frobeniusWeight_sq (qx : ℕ) (α : PadicAlgCl l) :
    frobeniusWeight ι qx (α ^ 2) = 2 * frobeniusWeight ι qx α := by
  simp only [frobeniusWeight, map_pow, norm_pow, Real.log_pow]
  push_cast
  ring

/-- The Rankin–Selberg step of `proposition-bound-largest-determinant-weight`.

Let `ℋ` be a lisse Weil sheaf on a smooth geometrically connected affine curve whose inverse
local factors have nonnegative coefficients and whose constituents have determinant weight at
most `D`. Then every local eigenvalue of `ℋ` has `ι`-weight at most `D + 2`.

The eigenvalues `λ` of the geometric Frobenius on `H_c² (U, ℋ)` satisfy
`|ι λ| ≤ q ^ (D / 2 + 1)` (`proposition-bound-largest-determinant-weight`), so by the Euler product
(`theorem-trace-formula-euler-product--4`) the Euler series of `ℋ` converges on the disc of radius
`R = q ^ (-(D / 2 + 1))`. By positivity every local factor converges there as well
(`lemma-positivity-convergence--1`), so its denominator `ι P_x (ℋ, T ^ e)` has no zero in that
disc; a local eigenvalue `β` produces the zero `T` with `T ^ e = (ι β)⁻¹`, whence
`|ι β| ^ (-1 / e) ≥ R`. -/
theorem frobeniusWeight_le_add_two_of_hasNonnegCoeffs [IsAffine C] [Fact (ringChar K ≠ l)]
    (hρ : W.IsLisse l ρ)
    (hpos : ∀ x, (W.eulerFactor l ρ ι x).HasNonnegCoeffs) {D : ℝ}
    (hD : ∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
      [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
      (γ : ℝ), τ.IsConstituent ρ → W.HasDetWeight l τ ι γ → γ ≤ D)
    (x : C.finitePoints) {β : PadicAlgCl l} (hβ : β ∈ W.localEigenvalues l ρ x) :
    frobeniusWeight ι (C.pointNorm x.1) β ≤ D + 2 := by
  classical
  open PowerSeries in
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  set e := p.degreeOver x.1
  have he : e ≠ 0 := p.degreeOver_ne_zero x.2
  -- the eigenvalues of the geometric Frobenius on `H_c²`
  set Tq := W.compactTopFrobenius l ρ
  set S := Tq.charpoly.roots.map ι
  have hS : ∀ c ∈ S, ‖c‖ ≤ q ^ (D / 2 + 1) := by
    intro c hc
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hc
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp only [map_zero, norm_zero]
      positivity
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hμ
    obtain ⟨N, M, hNM, hc, hdet⟩ := exists_isConstituent_hasDetWeight_of_hasEigenvalue ρ ι hμ
    have hle := hD _ _ hc hdet
    have hpos : 0 < ‖ι (μ / Nat.card K)‖ := by
      simp [hμ0]
    rw [frobeniusWeight, div_le_iff₀ hlogq] at hle
    have h1 : ‖ι (μ / Nat.card K)‖ ≤ q ^ (D / 2) := by
      rw [← Real.exp_log hpos, Real.rpow_def_of_pos hq0]
      exact Real.exp_le_exp.2 (by nlinarith)
    have h2 : ‖ι μ‖ = q * ‖ι (μ / Nat.card K)‖ := by
      rw [map_div₀, norm_div, map_natCast, Complex.norm_natCast, ← hqdef]
      field_simp
    rw [h2, Real.rpow_add hq0, Real.rpow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 hq0.le
  -- the Euler series converges on the disc of radius `R`
  set R : ℝ := q ^ (-(D / 2 + 1))
  have hR : 0 < R := Real.rpow_pos_of_pos hq0 _
  have hRS : ∀ c ∈ S, ‖c‖ * R ≤ 1 := fun c hc ↦ by
    calc ‖c‖ * R ≤ q ^ (D / 2 + 1) * R := mul_le_mul_of_nonneg_right (hS c hc) hR.le
      _ = 1 := by rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  set Dser : PowerSeries ℂ := ((Tq.charpolyRev.map ι : Polynomial ℂ) : PowerSeries ℂ)
    with hDdef
  have hDser : Dser = (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod := by
    rw [hDdef, LinearMap.charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod_one_sub_C_mul_X,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun c _ ↦ by simp)
  have hDser0 : PowerSeries.constantCoeff Dser ≠ 0 := by
    rw [hDser, map_multiset_prod, Multiset.map_map, Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
      simp]
    exact one_ne_zero
  obtain ⟨P₁, hP₁⟩ := exists_eulerSeries_mul_eq_coe ρ ι hρ
  have hL : W.eulerSeries l ρ ι = (P₁ : PowerSeries ℂ) * Dser⁻¹ := by
    rw [← hP₁, mul_assoc, PowerSeries.mul_inv_cancel _ hDser0, mul_one]
  -- the local polynomial at `x` and a zero of it
  set Qx : Polynomial ℂ := ((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ e)
  have hβ0 : ι β ≠ 0 :=
    (map_ne_zero ι).2 fun h ↦ zero_notMem_localEigenvalues (ρ := ρ) x (h ▸ hβ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι β)⁻¹ (Nat.pos_of_ne_zero he)
  have hQz : Qx.eval z = 0 := by
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, hz, map_localPolynomial,
      Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨1 - Polynomial.C (ι β) * Polynomial.X,
      Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem ι hβ), ?_⟩)
    simp [hβ0]
  have hQ0 : Qx.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_X, zero_pow he, eval_zero_map_localPolynomial]
    exact one_ne_zero
  -- the zero lies outside the disc of radius `R`
  have hzR : R ≤ ‖z‖ := by
    by_contra! hlt
    set r : NNReal := ⟨(‖z‖ + R) / 2, by positivity⟩
    have hzr : ‖z‖ < r := by change ‖z‖ < (‖z‖ + R) / 2; linarith
    have hrR : (r : ℝ) < R := by change (‖z‖ + R) / 2 < R; linarith
    have hr : ∀ c ∈ S, ‖c‖ * r < 1 := fun c hc ↦ by
      rcases eq_or_ne c 0 with rfl | hc0
      · simp
      · calc ‖c‖ * r < ‖c‖ * R := mul_lt_mul_of_pos_left hrR (norm_pos_iff.2 hc0)
          _ ≤ 1 := hRS c hc
    have h1 : (r : ENNReal) ≤ (W.eulerSeries l ρ ι).radius := by
      rw [hL, hDser]
      exact PowerSeries.le_radius_coe_mul_inv_prod P₁ S hr
    have h2 := PowerSeries.radius_tprod_le_radius hpos (constantCoeff_eulerFactor ι)
      (multipliable_eulerFactors W l ρ ι) x
    have h3 : (‖z‖₊ : ENNReal) < ((Qx : PowerSeries ℂ)⁻¹).radius :=
      lt_of_lt_of_le (by exact_mod_cast hzr) (h1.trans h2)
    exact PowerSeries.eval_ne_zero_of_lt_radius_inv hQ0 h3 hQz
  -- hence `|ι β| ≤ q ^ (e (D / 2 + 1))`
  have hnorm : ‖ι β‖ ≤ q ^ ((e : ℝ) * (D / 2 + 1)) := by
    have hze : ‖z‖ ^ e = ‖ι β‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
    have hRe : R ^ e ≤ ‖ι β‖⁻¹ := hze ▸ pow_le_pow_left₀ hR.le hzR e
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le] at hRe
    have := (le_inv_comm₀ (by positivity) (norm_pos_iff.2 hβ0)).1 hRe
    rwa [← Real.rpow_neg hq0.le, neg_mul, neg_neg, mul_comm] at this
  rw [frobeniusWeight, Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2, Nat.cast_pow,
    Real.log_pow, div_le_iff₀ (by positivity)]
  have := Real.log_le_log (norm_pos_iff.2 hβ0) hnorm
  rw [Real.log_rpow hq0] at this
  change 2 * Real.log ‖ι β‖ ≤ (D + 2) * (e * Real.log q)
  nlinarith

/-- The iterated Rankin–Selberg bound: if `ℱ` is lisse and `ι`-real on a smooth geometrically
connected affine curve and its constituents have determinant weight at most `d`, then every
local eigenvalue of `ℱ` has `ι`-weight at most `d + 2 ^ (-j)`, for every `j`.

For `j = 0` apply `AlgebraicGeometry.WeilGroup.frobeniusWeight_le_add_two_of_hasNonnegCoeffs`
to the tensor square `ℱ ⊗ ℱ`, whose inverse local factors are nonnegative
(`lemma-positivity-euler-factors--1`) and whose constituents have determinant weight at most `2 d`
(`sk-p-tensor`), and to the local eigenvalue `α ^ 2`; for `j + 1` apply the case `j` to
`ℱ ⊗ ℱ`, which is again lisse and `ι`-real. -/
theorem frobeniusWeight_le_add_inv_two_pow_of_isReal [IsAffine C] [Fact (ringChar K ≠ l)]
    [W.IsEtaleQuotient] (j : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
      [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V),
      W.IsLisse l ρ → W.IsReal l ρ ι → ∀ {d : ℝ},
      (∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
        [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
        (γ : ℝ), τ.IsConstituent ρ → W.HasDetWeight l τ ι γ → γ ≤ d) →
      ∀ (x : C.finitePoints), ∀ α ∈ W.localEigenvalues l ρ x,
        frobeniusWeight ι (C.pointNorm x.1) α ≤ d + 1 / 2 ^ j := by
  induction j with
  | zero =>
    intro V _ _ _ ρ hρ hreal d hd x α hα
    have h := frobeniusWeight_le_add_two_of_hasNonnegCoeffs ι (hρ.tprod hρ)
      (hreal.hasNonnegCoeffs_eulerFactor_tprod_self ι)
      (le_add_of_isConstituent_tprod_of_hasDetWeight ι x hρ hρ hd hd) x
      (sq_mem_localEigenvalues_tprod_self hα)
    rw [frobeniusWeight_sq] at h
    norm_num
    linarith
  | succ j ih =>
    intro V _ _ _ ρ hρ hreal d hd x α hα
    have h := ih (ρ.tprod ρ) (hρ.tprod hρ) (hreal.tprod ι hreal)
      (le_add_of_isConstituent_tprod_of_hasDetWeight ι x hρ hρ hd hd) x _
      (sq_mem_localEigenvalues_tprod_self hα)
    rw [frobeniusWeight_sq] at h
    have h2 : (1 : ℝ) / 2 ^ (j + 1) = 1 / 2 ^ j / 2 := by rw [pow_succ]; ring
    rw [h2]
    linarith

end RankinSelberg

end WeilGroup

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `proposition-bound-largest-determinant-weight--1`: Rankin–Selberg upper bound.

Let `U₀` be an affine smooth geometrically connected curve over `𝔽_q` and let `ℱ ≠ 0` be an
`ι`-real lisse Weil sheaf on it all of whose irreducible constituents have determinant weight
at most `d`. Then every local Frobenius eigenvalue of `ℱ` has `ι`-weight at most `d`.

The proof runs the Rankin–Selberg trick on the even tensor powers `ℋ_m = ℱ ^ ⊗ (2 m)`. Their
constituents have determinant weight at most `2 m d`, so the top compactly supported
cohomology `H_c² (U, ℋ_m)`, a coinvariant Tate twist, has eigenvalues of modulus at most
`q ^ (m d + 1)`; the Grothendieck trace formula therefore bounds the radius of convergence of
`L_ι (U₀, ℋ_m, T)` below by `q ^ (-(m d + 1))`. Reality of `ℱ` makes every coefficient of
every inverse local factor nonnegative, so each individual factor inherits that radius bound
from the product, and a zero of the local denominator at `|ι α| ^ (-2 m / e)` gives
`wt (α) ≤ d + 1 / m` for every `m`. -/
theorem hasWeightsAtMost_of_isReal [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient] [Nontrivial V]
    (hρ : W.IsLisse l ρ)
    (hreal : W.IsReal l ρ ι) {d : ℝ}
    (hd : ∀ {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
      [FiniteDimensional (PadicAlgCl l) V'] (σ : Representation (PadicAlgCl l) W.carrier V')
      (γ : ℝ), σ.IsConstituent ρ → W.HasDetWeight l σ ι γ → γ ≤ d) :
    W.HasWeightsAtMost l ρ ι d := by
  intro x α hα
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε one_half_lt_one
  have h := frobeniusWeight_le_add_inv_two_pow_of_isReal ι j ρ hρ hreal hd x α hα
  rw [one_div_pow] at hj
  linarith

/-- Blueprint `proposition-bound-largest-determinant-weight`: Upper bound via the largest
determinant weight.

Let `U₀` be a smooth geometrically connected affine curve, `ℱ` an `ι`-real lisse Weil sheaf on
it and `d` an upper bound for the determinant weights of its constituents. Then every local
eigenvalue `α` of `ℱ` at a closed point `x` satisfies `|ι α| ^ 2 ≤ q_x ^ d`.

This is `AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal` with the weight unfolded: the
Rankin–Selberg bound for the iterated tensor squares
(`AlgebraicGeometry.WeilGroup.frobeniusWeight_le_add_inv_two_pow_of_isReal`) gives
`|ι α| ^ 2 ≤ q_x ^ (d + 2 ^ (-j))` for every `j`. -/
theorem sq_norm_le_rpow_of_isReal [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient] [Nontrivial V]
    (hρ : W.IsLisse l ρ)
    (hreal : W.IsReal l ρ ι) {d : ℝ}
    (hd : ∀ {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
      [FiniteDimensional (PadicAlgCl l) V'] (σ : Representation (PadicAlgCl l) W.carrier V')
      (γ : ℝ), σ.IsConstituent ρ → W.HasDetWeight l σ ι γ → γ ≤ d)
    (x : C.finitePoints) {α : PadicAlgCl l} (hα : α ∈ W.localEigenvalues l ρ x) :
    ‖ι α‖ ^ 2 ≤ (C.pointNorm x.1 : ℝ) ^ d := by
  have h := hasWeightsAtMost_of_isReal W l ρ ι hρ hreal hd x α hα
  have hα0 : 0 < ‖ι α‖ := norm_pos_iff.2 <|
    (map_ne_zero ι).2 fun h ↦ zero_notMem_localEigenvalues (ρ := ρ) x (h ▸ hα)
  have hq : (1 : ℝ) < C.pointNorm x.1 := by exact_mod_cast C.one_lt_pointNorm x.2
  rw [frobeniusWeight, div_le_iff₀ (Real.log_pos hq)] at h
  rw [← Real.exp_log (pow_pos hα0 2), Real.rpow_def_of_pos (zero_lt_one.trans hq),
    Real.log_pow]
  exact Real.exp_le_exp.2 (by push_cast; linarith)

end WeilGroup

namespace BoundaryDatum

variable {U : Scheme.{u}} {pU : U ⟶ Spec (.of K)} [IsCurve pU] {j : U ⟶ C}
  [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} {WC : WeilGroup p}
  (D : BoundaryDatum j WU WC) (l : ℕ) [Fact l.Prime] {V : Type u}
  [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ι : PadicAlgCl l →+* ℂ)

/-- Semi-continuity of weights, the first assertion of `proposition-weights-j-boundary-points`, on
the representation side and conditional on the Euler-product hypothesis `hD`; this is not a proof of
that assertion.

For a boundary datum `D` on a smooth geometrically connected curve `C₀`, if the lisse Weil sheaf
`ℱ` on `U₀` has weights at most `w`, then `j_* ℱ` has weights at most `w` on `C₀`. Concretely:
at a boundary point `s`, the residue Frobenius acts on the boundary stalk `V ^ (I_s)`, and every
one of its eigenvalues `α`, witnessed by a nonzero invariant eigenvector `v`, has `ι`-weight at
most `w` relative to the residue cardinality `q_s`.

Shrinking to an affine neighbourhood, the counting bound `N_e ≤ A q ^ e` for closed points of
degree `e` shows that `L_ι (U₀, ℱ, T)⁻¹` has radius at least `q ^ (-(w + 2) / 2)`, while the
open–closed sequence identifies `H_c² (C, j_* ℱ)` with a coinvariant Tate twist whose
eigenvalues are bounded by `q ^ ((w + 2) / 2)`. The trace formula then confines the zeros of
the boundary factor, giving the preliminary bound `|ι α| ≤ q_s ^ ((w + 2) / 2)`; applying it
to the tensor powers `ℱ ^ ⊗ n`, whose boundary stalks receive `(V ^ (I_s)) ^ ⊗ n`, improves it
to `|ι α| ≤ q_s ^ (w / 2 + 1 / n)` for every `n`, and `n → ∞` finishes
(`AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_of_hasEigenvalue_boundaryFrobenius`).

The curve `C₀` is smooth and geometrically connected and `ℓ ≠ char 𝔽_q`, as in the setting
`situation-weil` of the block, and `ℱ` is lisse. The trace formula used in the proof, in its
Euler-product form for middle extensions (`proposition-weights-j-boundary-points`), is the
hypothesis `hD`: it does not follow from the fields of a `BoundaryDatum` (see
`AlgebraicGeometry.BoundaryDatum.HasMiddleExtensionEulerProduct`). The unconditional, sheaf-level
form of this assertion is
`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`. -/
theorem frobeniusWeight_le_of_hasWeightsAtMost [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] (hD : D.HasMiddleExtensionEulerProduct l ι)
    (ρ : Representation (PadicAlgCl l) WU.carrier V) (hρ : WU.IsLisse l ρ) {w : ℝ}
    (hw : WU.HasWeightsAtMost l ρ ι w) (s : ↥((Set.range j.base)ᶜ)) {α : PadicAlgCl l} {v : V}
    (hv : v ∈ D.boundaryStalk l ρ s) (hv0 : v ≠ 0) (hα : ρ (D.residueFrobenius s) v = α • v) :
    WeilGroup.frobeniusWeight ι (C.pointNorm s.1) α ≤ w := by
  refine D.frobeniusWeight_le_of_hasEigenvalue_boundaryFrobenius l ι hD ρ hρ hw s
    (Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hv⟩) ⟨?_, ?_⟩)
  · rw [Module.End.mem_eigenspace_iff]
    ext
    simp [boundaryFrobenius, hα]
  · exact fun h ↦ hv0 (congrArg Subtype.val h)

/-- Blueprint `proposition-weights-j-boundary-points`: Semi-continuity of weights, the second
assertion.

The consequence of the weight bound for `j_* ℱ`: a lisse Weil sheaf `𝒢` on a smooth
geometrically connected curve `C₀` whose restriction to the open `U₀` is punctually `ι`-pure of
weight `w` is punctually `ι`-pure of weight `w` on all of `C₀`.

At a closed point of `U₀` this is the hypothesis, the local Frobenius of `C₀` being conjugate to
the image of that of `U₀`. At a boundary point `s` the middle extension of `𝒢|_{U₀}` is `𝒢`
itself (`lemma-boundary-stalk--2`), so the semi-continuity argument runs with the Euler
product of the lisse sheaf `𝒢` on an affine neighbourhood of `s`
(`theorem-trace-formula-euler-product--4`); applied to `𝒢` and to its dual `𝒢 ^ ∨`, whose
eigenvalues are the inverses of those of `𝒢`, it gives an upper bound `w` and a lower bound `w`
(`corollary-unramified-boundary-point--2`,
`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_forall_mem_range`). -/
theorem isPunctuallyPure_of_isPunctuallyPure_restrict [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
    (ρ : Representation (PadicAlgCl l) WC.carrier V) {w : ℝ} (hρ : WC.IsLisse l ρ)
    (hpure : WU.IsPunctuallyPure l (ρ.comp D.restrict) ι w) :
    WC.IsPunctuallyPure l ρ ι w := by
  refine WC.isPunctuallyPure_of_forall_mem_range l ρ ι j hρ fun x hx α hα ↦ ?_
  obtain ⟨y, hy⟩ := hx
  have hyfin : y ∈ U.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso j y).1 (hy ▸ x.2)
  have hxy : j.mapFinitePoints ⟨y, hyfin⟩ = x := Subtype.ext hy
  rw [← hxy] at hα ⊢
  exact D.toRestriction.frobeniusWeight_eq_of_isPunctuallyPure_comp l ρ ι hpure _ α hα

end BoundaryDatum

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

-- The constituent bound elaborates exterior powers of direct sums of subquotients.
/-- Steps 1–3 of `theorem-purity-real-sheaves-curves--1`, for the composition factors.

Let `ρ` be an `ι`-real lisse Weil representation on a smooth geometrically connected affine
curve, and `0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ` a composition series. Then every composition factor
`Q j = F (j + 1) ⧸ F j` is punctually `ι`-pure of its determinant weight
`γ = wt_{ι, q}(det Q j (γ)) / rank Q j`.

The semisimplification `S = ⨁ i, Q i` has the local polynomials of `ρ`, so its exterior power
`E = ⋀^(N + 1) S`, where `N` is the total rank of the factors of determinant weight `> γ`, is
real (`proposition-weights-under-usual-operations`); by the exterior-power rule (`sk-p-exterior`)
its constituents have determinant weight at most `B + γ`, where `B` is the sum of the determinant
weights of those factors counted with rank. The Rankin–Selberg bound
(`proposition-bound-largest-determinant-weight--1`) then bounds every local eigenvalue of `E` by
`B + γ`. At a closed point `x`, the product of an eigenvalue `β` of `Q j` with all eigenvalues of
the factors of weight `> γ` is such an eigenvalue (`lemma-filtrations-spectra`), of weight
`wt β + B`; so `wt β ≤ γ`. The weights of the eigenvalues of `Q j` sum to the weight
`rank (Q j) * γ` of its determinant, so all of them equal `γ`. -/
theorem isPunctuallyPure_subquotient_of_isReal [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient] (hρ : W.IsLisse l ρ)
    (hreal : W.IsReal l ρ ι) {n : ℕ}
    {F : ℕ → Subrepresentation ρ} (h0 : F 0 = ⊥) (hn : F n = ⊤)
    (hF : ∀ i < n, F i ⋖ F (i + 1)) {j : ℕ} (hj : j < n) :
    W.IsPunctuallyPure l ((F (j + 1)).subquotient (F j)) ι
      (frobeniusWeight ι (Nat.card K)
          (LinearMap.det ((F (j + 1)).subquotient (F j) W.frobeniusLift)) /
        Module.finrank (PadicAlgCl l)
          ((F (j + 1)).toSubmodule ⧸ (F j).toSubmodule.comap (F (j + 1)).toSubmodule.subtype)) := by
  classical
  intro x α hα
  let Qt : Fin n → Type u := fun i ↦
    (F (i + 1)).toSubmodule ⧸ (F i).toSubmodule.comap (F (i + 1)).toSubmodule.subtype
  let Q : ∀ i, Representation (PadicAlgCl l) W.carrier (Qt i) := fun i ↦
    (F (i + 1)).subquotient (F i)
  let d : Fin n → ℕ := fun i ↦ Module.finrank (PadicAlgCl l) (Qt i)
  let w : Fin n → ℝ := fun i ↦
    frobeniusWeight ι (Nat.card K) (LinearMap.det (Q i W.frobeniusLift)) / d i
  let j' : Fin n := ⟨j, hj⟩
  change α ∈ W.localEigenvalues l (Q j') x at hα
  change frobeniusWeight ι (C.pointNorm x.1) α = w j'
  set γ := w j' with hγ
  set qx := C.pointNorm x.1
  let eig : Fin n → Multiset (PadicAlgCl l) := fun i ↦ W.localEigenvalues l (Q i) x
  -- the composition factors
  have hQlisse (i : Fin n) : W.IsLisse l (Q i) := hρ.subquotient _ _
  have hQirr (i : Fin n) : (Q i).IsIrreducible :=
    (Subrepresentation.isIrreducible_subquotient_iff (hF i i.2).le).2 (hF i i.2)
  have hQnontriv (i : Fin n) : Nontrivial (Qt i) := by
    have := hQirr i
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (bot_ne_top : (⊥ : Subrepresentation (Q i)) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hQdet (i : Fin n) : W.HasDetWeight l (Q i) ι (w i) := (hQlisse i).hasDetWeight ι
  have hcardeig (i : Fin n) : Multiset.card (eig i) = d i := by
    rw [show d i = (Q i (W.frobenius x)).charpoly.natDegree from
      (LinearMap.charpoly_natDegree _).symm]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hweig (i : Fin n) : frobeniusWeight ι qx (eig i).prod = d i * w i := by
    change frobeniusWeight ι qx (Q i (W.frobenius x)).charpoly.roots.prod = _
    rw [← Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    exact hQdet i x
  have h0eig (i : Fin n) : (0 : PadicAlgCl l) ∉ eig i := zero_notMem_localEigenvalues x
  -- the semisimplification
  let S := Representation.directSum Q
  have hcharpoly (g : W.carrier) : (S g).charpoly = (ρ g).charpoly := by
    rw [Representation.charpoly_directSum, LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le (ρ g)
      (fun i ↦ (F i).toSubmodule) n (by rw [h0]; rfl) (by rw [hn]; rfl) (fun i hi ↦ (hF i hi).le)
      (fun i ↦ (F i).apply_mem_toSubmodule g)]
    exact Fin.prod_univ_eq_prod_range (fun i ↦ ((F (i + 1)).subquotient (F i) g).charpoly) n
  have heigS : W.localEigenvalues l S x = ∑ i, eig i := by
    change (S (W.frobenius x)).charpoly.roots = _
    rw [Representation.charpoly_directSum, Polynomial.roots_prod _ _
      (Finset.prod_ne_zero_iff.2 fun i _ ↦ (LinearMap.charpoly_monic _).ne_zero)]
    rfl
  -- the factors of determinant weight above `γ`
  let A : Finset (Fin n) := Finset.univ.filter fun i ↦ γ < w i
  let N := ∑ i ∈ A, d i
  let B := ∑ i ∈ A, (d i : ℝ) * w i
  have hj'A : j' ∉ A := by simp [A, γ]
  have hSlisse : W.IsLisse l S := IsLisse.directSum hQlisse
  have hSnontriv : Nontrivial (DirectSum (Fin n) Qt) :=
    (DirectSum.of_injective (β := Qt) j').nontrivial
  -- the bound on the determinant weights of the constituents of `⋀^(N + 1) S`
  have hbound : ∀ {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
      [FiniteDimensional (PadicAlgCl l) V'] (τ : Representation (PadicAlgCl l) W.carrier V')
      (γ' : ℝ), τ.IsConstituent (S.exteriorPower (N + 1)) → W.HasDetWeight l τ ι γ' →
      γ' ≤ B + γ := by
    intro V' _ _ _ τ γ' hτ hγ'
    obtain ⟨N₁, M₁, hcov, ⟨eτ⟩⟩ := hτ.exists_covBy
    have hRirr : (M₁.subquotient N₁).IsIrreducible :=
      eτ.isIrreducible_iff.1 hτ.1
    have hRlisse : W.IsLisse l (M₁.subquotient N₁) := (hSlisse.exteriorPower _).subquotient _ _
    obtain ⟨T, hT, hTc, hTs⟩ :=
      Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift S (N + 1)
      (Representation.directSumSummand Q)
      (fun i ↦ (Representation.directSumSummandEquiv Q i).isIrreducible_iff.1 (hQirr i))
      (fun i ↦ ((hQlisse i).of_equiv
        (Representation.directSumSummandEquiv Q i)).hasFiniteGeometricDet)
      (Representation.isInternal_directSumSummand Q) hcov.lt hRirr hRlisse.hasFiniteGeometricDet
    have hτnontriv : Nontrivial V' := by
      have := hτ.1
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    have hγ'eq : γ' = (M₁.subquotient N₁).detWeight (weightCharacter ι (Nat.card K))
        W.frobeniusLift := by
      have hτlisse : W.IsLisse l τ := hRlisse.of_equiv eτ.symm
      have heq := HasDetWeight.eq (ρ := τ) ι hγ' (hτlisse.hasDetWeight ι) x
      have heq' : γ' = frobeniusWeight ι (Nat.card K)
          (LinearMap.det ((M₁.subquotient N₁) W.frobeniusLift)) /
          Module.finrank (PadicAlgCl l)
            (M₁.toSubmodule ⧸ N₁.toSubmodule.comap M₁.toSubmodule.subtype) := by
        simpa only [eτ.det_apply, eτ.finrank_eq] using heq
      exact heq'.trans (detWeight_weightCharacter ι _ _ _).symm
    have hWM : Representation.weightMultiset (weightCharacter ι (Nat.card K)) W.frobeniusLift
        (Representation.directSumSummand Q) = ∑ i, Multiset.replicate (d i) (w i) := by
      simp only [Representation.weightMultiset]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have e := Representation.directSumSummandEquiv Q i
      have hdet : (Representation.directSumSummand Q i).toRepresentation.detWeight
          (weightCharacter ι (Nat.card K)) W.frobeniusLift = w i := by
        calc
          _ = (Q i).detWeight (weightCharacter ι (Nat.card K)) W.frobeniusLift :=
            e.detWeight_eq _ _
          _ = w i := by
            rw [detWeight_weightCharacter]
      rw [e.finrank_eq, hdet]
    have hfilter : (∑ i, Multiset.replicate (d i) (w i)).filter (γ < ·) =
        ∑ i ∈ A, Multiset.replicate (d i) (w i) := by
      have key (s : Finset (Fin n)) : (∑ i ∈ s, Multiset.replicate (d i) (w i)).filter (γ < ·) =
          ∑ i ∈ s.filter (fun i ↦ γ < w i), Multiset.replicate (d i) (w i) := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Multiset.filter_add, ih, Finset.filter_insert]
          split_ifs with h
          · rw [Finset.sum_insert (by simp [ha]),
              Multiset.filter_eq_self.2 fun b hb ↦ (Multiset.eq_of_mem_replicate hb) ▸ h]
          · rw [Multiset.filter_eq_nil.2 fun b hb ↦ (Multiset.eq_of_mem_replicate hb) ▸ h,
              zero_add]
      exact key Finset.univ
    rw [hWM] at hT
    have hle := Multiset.sum_le_sum_filter_add_of_le γ hT (by
      rw [hTc, hfilter, Multiset.card_sum]
      simp [N])
    rw [hfilter, Multiset.sum_sum] at hle
    simp only [Multiset.sum_replicate, nsmul_eq_mul] at hle
    rw [hγ'eq, hTs]
    exact hle
  -- the upper bound for the eigenvalues of the block `Q j`
  have key (β : PadicAlgCl l) (hβ : β ∈ eig j') : frobeniusWeight ι qx β ≤ γ := by
    let t := β ::ₘ ∑ i ∈ A, eig i
    have ht : t.prod ∈ W.localEigenvalues l (S.exteriorPower (N + 1)) x := by
      change t.prod ∈ (_root_.exteriorPower.map (N + 1) (S (W.frobenius x))).charpoly.roots
      rw [LinearMap.charpoly_roots_exteriorPower]
      change t.prod ∈ ((W.localEigenvalues l S x).powersetCard (N + 1)).map Multiset.prod
      rw [heigS]
      refine Multiset.mem_map_of_mem _ (Multiset.mem_powersetCard.2 ⟨?_, ?_⟩)
      · change β ::ₘ (∑ i ∈ A, eig i) ≤ _
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j'), ← Multiset.singleton_add]
        exact add_le_add (Multiset.singleton_le.2 hβ) (Finset.sum_le_sum_of_subset fun i hi ↦
          Finset.mem_erase.2 ⟨fun h ↦ hj'A (h ▸ hi), Finset.mem_univ _⟩)
      · simp [t, Multiset.card_sum, hcardeig, N, add_comm]
    have hEnontriv : Nontrivial (⋀[PadicAlgCl l]^(N + 1) (DirectSum (Fin n) Qt)) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have h' : W.localEigenvalues l (S.exteriorPower (N + 1)) x = 0 := by
        rw [localEigenvalues, LinearMap.charpoly_eq_one_of_subsingleton, Polynomial.roots_one,
          Multiset.empty_eq_zero]
      rw [h'] at ht
      exact Multiset.notMem_zero _ ht
    have hE := hasWeightsAtMost_of_isReal W l (S.exteriorPower (N + 1)) ι
      (hSlisse.exteriorPower _) (hreal.exteriorPower_of_charpoly_eq ι (fun _ ↦ hcharpoly _) _)
      hbound x _ ht
    have hne : ∀ i ∈ A, (eig i).prod ≠ 0 := fun i _ ↦ Multiset.prod_ne_zero (h0eig i)
    have hw : frobeniusWeight ι qx t.prod = frobeniusWeight ι qx β + B := by
      rw [Multiset.prod_cons, Multiset.prod_sum,
        frobeniusWeight_mul ι qx (fun h ↦ h0eig j' (h ▸ hβ)) (Finset.prod_ne_zero_iff.2 hne),
        frobeniusWeight_prod ι qx A hne]
      simp only [hweig, B]
    linarith
  -- the product of the eigenvalues of `Q j` has weight `rank (Q j) * γ`
  have hsum : ((eig j').map (frobeniusWeight ι qx)).sum =
      Multiset.card ((eig j').map (frobeniusWeight ι qx)) • γ := by
    rw [← frobeniusWeight_multiset_prod ι qx (h0eig j'), hweig, Multiset.card_map, hcardeig,
      nsmul_eq_mul]
  exact Multiset.eq_of_le_of_sum_eq (fun a ha ↦ by
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
      exact key b hb) hsum _ (Multiset.mem_map_of_mem _ hα)

/-- Blueprint `theorem-purity-real-sheaves-curves--1`: Purity of real lisse sheaves on curves.

Let `C₀ / 𝔽_q` be a smooth geometrically connected curve and `ρ` an `ι`-real lisse Weil
representation. Every irreducible constituent `σ` of `ρ` is punctually `ι`-pure of its
determinant weight `γ`. This declaration is Steps 1–4 of the blueprint proof, for an affine
curve; Step 0, the reduction of a general curve to an affine open, is
`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`. Indeed `σ` is a
composition factor `F (i₀ + 1) ⧸ F i₀` of a composition series of `ρ`, and the composition
factors are pure of their determinant weights
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_subquotient_of_isReal`); the determinant weight
of a nonzero representation is unique. -/
theorem isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine [IsAffine C]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
    [W.IsEtaleQuotient] (hρ : W.IsLisse l ρ)
    (hreal : W.IsReal l ρ ι) {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
    [FiniteDimensional (PadicAlgCl l) V']
    (σ : Representation (PadicAlgCl l) W.carrier V') (hσ : σ.IsConstituent ρ)
    {γ : ℝ} (hγ : W.HasDetWeight l σ ι γ) :
    W.IsPunctuallyPure l σ ι γ := by
  obtain ⟨N, M, hNM, hE⟩ := hσ.exists_covBy
  obtain ⟨n, F, i₀, h0, hn, hF, hi₀, hFi₀, hFi₀'⟩ := Subrepresentation.exists_covBy_chain hNM
  rw [← hFi₀, ← hFi₀'] at hE
  obtain ⟨e⟩ := hE
  intro x α hα
  rw [← localEigenvalues_of_equiv e] at hα
  rw [isPunctuallyPure_subquotient_of_isReal W l ρ ι hρ hreal h0 hn hF hi₀ x α hα]
  have hirr := (Subrepresentation.isIrreducible_subquotient_iff (hF i₀ hi₀).le).2 (hF i₀ hi₀)
  have : Nontrivial ((F (i₀ + 1)).toSubmodule ⧸
      (F i₀).toSubmodule.comap (F (i₀ + 1)).toSubmodule.subtype) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (bot_ne_top : (⊥ : Subrepresentation ((F (i₀ + 1)).subquotient (F i₀))) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  exact ((hρ.subquotient _ _).hasDetWeight ι).eq ι (hγ.of_equiv ι e) x

section Transfer

/-! ### Transfer along a restriction of Weil groups

Let `j : U₀ ⟶ C₀` be an open immersion of curves and `r : W(U₀) →* W(C₀)` a homomorphism of
Weil groups carrying the local Frobenius at each closed point `x` of `U₀` into the Frobenius
conjugacy class at `j x`. Then the local invariants of a representation `ρ` of `W(C₀)` at `j x`
are those of `ρ ∘ r` at `x`. -/

variable {U : Scheme.{u}} {pU : U ⟶ Spec (.of K)} [IsCurve pU] {j : U ⟶ C} [IsOpenImmersion j]
  {WU : WeilGroup pU} {WC : WeilGroup p} {r : WU.carrier →* WC.carrier}
  (hr : ∀ (x : U.finitePoints) (y : C.finitePoints), j.base x.1 = y.1 →
    IsConj (WC.frobenius y) (r (WU.frobenius x)))
  {l : ℕ} [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) WC.carrier V)

/-- The image of a closed point of `U₀` under the open immersion `j` is a closed point of
`C₀`. -/
def finitePointsMap (j : U ⟶ C) [IsOpenImmersion j] (x : U.finitePoints) : C.finitePoints :=
  ⟨j.base x.1, (Scheme.Hom.mem_finitePoints_iff_of_isIso j x.1).2 x.2⟩

omit [IsOpenImmersion j] in
include hr in
/-- The local Frobenius eigenvalues of `ρ ∘ r` at `x` are those of `ρ` at `j x`. -/
theorem localEigenvalues_comp_of_isConj (x : U.finitePoints) (y : C.finitePoints)
    (hxy : j.base x.1 = y.1) :
    WU.localEigenvalues l (ρ.comp r) x = WC.localEigenvalues l ρ y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (hr x y hxy)
  let e : V ≃ₗ[PadicAlgCl l] V := LinearEquiv.ofLinearMap (ρ c) (ρ c⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  have he : ρ (r (WU.frobenius x)) = e.conj (ρ (WC.frobenius y)) := by
    rw [← hc]
    ext v
    simp [e, LinearEquiv.conj_apply, map_mul]
  simp only [localEigenvalues, MonoidHom.comp_apply]
  rw [he, LinearEquiv.charpoly_conj]

variable {ρ}

include hr in
/-- The restriction of an `ι`-real representation is `ι`-real. -/
theorem IsReal.comp_of_isConj {ι : PadicAlgCl l →+* ℂ} (hρ : WC.IsReal l ρ ι) :
    WU.IsReal l (ρ.comp r) ι := by
  intro x n
  have h : WU.localPolynomial l (ρ.comp r) x = WC.localPolynomial l ρ (finitePointsMap j x) :=
    (localPolynomial_eq_charpolyRev_of_isConj (ρ := ρ) (hr x _ rfl)).symm
  rw [h]
  exact hρ _ n

omit [FiniteDimensional (PadicAlgCl l) V] in
include hr in
/-- The restriction of a representation of determinant weight `γ` has determinant weight `γ`:
the norms of `x` and `j x` agree. -/
theorem HasDetWeight.comp_of_isConj {ι : PadicAlgCl l →+* ℂ} {γ : ℝ}
    (hρ : WC.HasDetWeight l ρ ι γ) : WU.HasDetWeight l (ρ.comp r) ι γ := by
  intro x
  have h := isConj_iff_eq.1 (MonoidHom.map_isConj
    (LinearMap.det : Module.End (PadicAlgCl l) V →* PadicAlgCl l)
    (ρ.map_isConj (hr x (finitePointsMap j x) rfl)))
  rw [MonoidHom.comp_apply, ← h, ← Scheme.Hom.pointNorm_of_isIso j x.1]
  exact hρ (finitePointsMap j x)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The restriction of a lisse representation along a continuous homomorphism of Weil groups
preserving degrees is lisse. -/
theorem IsLisse.comp_of_continuous (hρ : WC.IsLisse l ρ) (hcont : Continuous r)
    (hdeg : WC.deg.comp r = WU.deg) : WU.IsLisse l (ρ.comp r) := by
  refine ⟨fun b i i' ↦ ?_⟩
  have hgeo (g : WU.geometric) : r g ∈ WC.geometric := by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hdeg]
    exact g.2
  let r' : WU.geometric → WC.geometric := fun g ↦ ⟨r g, hgeo g⟩
  have : Continuous r' := (hcont.comp continuous_subtype_val).subtype_mk _
  exact (hρ.continuous_toMatrix b i i').comp this

include hr in
/-- If the restriction `ρ ∘ r` is punctually `ι`-pure of weight `w`, then `ρ` is so at the
closed points of `C₀` in the image of `j`. -/
theorem frobeniusWeight_eq_of_isPunctuallyPure_comp {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    (hpure : WU.IsPunctuallyPure l (ρ.comp r) ι w) (x : U.finitePoints) (y : C.finitePoints)
    (hxy : j.base x.1 = y.1) {α : PadicAlgCl l} (hα : α ∈ WC.localEigenvalues l ρ y) :
    frobeniusWeight ι (C.pointNorm y.1) α = w := by
  rw [← localEigenvalues_comp_of_isConj hr ρ x y hxy] at hα
  rw [← hxy, Scheme.Hom.pointNorm_of_isIso j x.1]
  exact hpure x α hα

end Transfer

/-- **Local eigenvalues are compatible with restriction to an open.** For a restriction
`W(U₀) → W(C₀)` of Weil groups along `j : U₀ ⟶ C₀`, the local Frobenius eigenvalues of
`ρ ∘ restrict` at a closed point `x` of `U₀` are those of `ρ` at `j x`: the restriction carries
the local Frobenius at `x` into the Frobenius conjugacy class at `j x`. This is the first step of
reducing purity on `C₀` to purity on an affine open subcurve. -/
theorem localEigenvalues_comp_restrict {U : Scheme.{u}} {pU : U ⟶ Spec (.of K)}
    [IsCurve pU] {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU}
    {WC : WeilGroup p} (R : Restriction j WU WC) {l : ℕ} [Fact l.Prime] {V : Type u}
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) WC.carrier V) (x : U.finitePoints) (y : C.finitePoints)
    (hxy : j.base x.1 = y.1) :
    WU.localEigenvalues l (ρ.comp R.restrict) x = WC.localEigenvalues l ρ y :=
  localEigenvalues_comp_of_isConj R.restrict_frobenius ρ x y hxy

/-- **Restriction of a Weil group to an affine open.** Every closed point `y` of a smooth
geometrically connected curve `C₀` lies in a nonempty affine open `j : U₀ ⟶ C₀`, itself a smooth
geometrically connected curve, with a Weil group `W(U₀)` and a continuous, surjective,
degree-preserving homomorphism `r : W(U₀) →* W(C₀)` carrying local Frobenius elements into the
Frobenius conjugacy classes. It is the restriction `W(U₀) → W(C₀, s)` to the standard Weil group
(`AlgebraicGeometry.WeilGroup.restrictionOfPath`), followed by the inverse of
`AlgebraicGeometry.WeilGroup.toStandard`. -/
theorem exists_restriction_isAffine [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    (W : WeilGroup p) (y : C) :
    ∃ (U : C.Opens) (_ : IsAffine U) (_ : IsCurve (U.ι ≫ p))
      (_ : SmoothOfRelativeDimension 1 (U.ι ≫ p)) (_ : GeometricallyConnected (U.ι ≫ p))
      (WU : WeilGroup (U.ι ≫ p)) (r : WU.carrier →* W.carrier), y ∈ U ∧ Continuous r ∧
      Function.Surjective r ∧ W.deg.comp r = WU.deg ∧
      ∀ (x : U.toScheme.finitePoints) (y : C.finitePoints), U.ι.base x.1 = y.1 →
        IsConj (W.frobenius y) (r (WU.frobenius x)) := by
  have := SmoothOfRelativeDimension.smooth 1 p
  have := W.connectedSpace
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : C.Opens) from trivial)
  have : IsAffine V := hV
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  have : IsCurve (V.ι ≫ p) := isCurve_comp_of_isAffine V.ι
  have : SmoothOfRelativeDimension 1 (V.ι ≫ p) := by
    simpa using smoothOfRelativeDimension_comp (n := 0) (m := 1) V.ι p
  have : GeometricallyConnected (V.ι ≫ p) := geometricallyConnected_comp V.ι
  have : ConnectedSpace V := GeometricallyConnected.connectedSpace_of_subsingleton (V.ι ≫ p)
  obtain ⟨sV⟩ := (V.ι ≫ p).nonempty_algebraicClosure_point
  obtain ⟨GV, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup sV
  obtain ⟨τ⟩ := PreGaloisCategory.nonempty_iso_of_fiberFunctor
    (Scheme.FiniteEtale.fiber (sV ≫ V.ι)) (Scheme.FiniteEtale.fiber W.basePoint)
  let R := restrictionOfPath (p := p) (pU := V.ι ≫ p) V.ι rfl τ GV W.fundamentalGroup
  let e := W.toStandard.symm
  refine ⟨V, hV, inferInstance, inferInstance, inferInstance, _,
    e.toMulEquiv.toMonoidHom.comp R.restrict, hyV,
    e.continuous.comp R.continuous_restrict, e.surjective.comp R.surjective_restrict, ?_,
    fun x y' hxy ↦ ?_⟩
  · rw [← R.deg_restrict, ← MonoidHom.comp_assoc]
    refine congrArg (MonoidHom.comp · R.restrict) (MonoidHom.ext fun g ↦ ?_)
    rw [MonoidHom.comp_apply, W.deg_eq]
    exact congrArg (Scheme.FiniteEtale.weilGroupDeg p W.basePoint W.fundamentalGroup)
      (W.toStandard.apply_symm_apply g)
  · have h := (W.isConj_toStandard_frobenius y').trans (R.restrict_frobenius x y' hxy)
    have h' := e.toMulEquiv.toMonoidHom.map_isConj h
    convert h' using 1
    exact (W.toStandard.symm_apply_apply _).symm

/-- Blueprint `theorem-purity-real-sheaves-curves--1`: Purity of real lisse sheaves on curves.

The main theorem of the block. Let `C₀ / 𝔽_q` be a smooth geometrically connected curve,
`ℓ ≠ char 𝔽_q`, and `ℱ` an `ι`-real lisse Weil sheaf on it. Then every irreducible constituent
`V` of `ℱ` is punctually `ι`-pure of weight `dw_ι (V)`, its own determinant weight. This is also
the full statement of `theorem-purity-real-sheaves-curves--1`, whose Step 0 is the proof given here.
(The hypothesis `AlgebraicGeometry.WeilGroup.IsEtaleQuotient` holds for every Weil group of a
geometrically connected curve, `AlgebraicGeometry.WeilGroup.isEtaleQuotient`.)

Purity is a condition at each closed point `x` separately. Choose an affine open `U₀ ∋ x`; it is
again a smooth geometrically connected curve, and `W(C₀)` receives a surjective restriction from
a Weil group of `U₀` (`AlgebraicGeometry.WeilGroup.Restriction.exists_weilGroup`). The restriction
`ℱ|_{U₀}` is lisse and `ι`-real, `V|_{U₀}` is a constituent of it (`lemma-boundary-stalk--2`), with
the same determinant weight, and its local eigenvalues at `x` are those of `V`. The affine case
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine`) applied
on `U₀` gives purity of `V` at `x`. -/
theorem isPunctuallyPure_of_isConstituent_of_isReal [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] [W.IsEtaleQuotient]
    (hρ : W.IsLisse l ρ) (hreal : W.IsReal l ρ ι)
    {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
    [FiniteDimensional (PadicAlgCl l) V']
    (σ : Representation (PadicAlgCl l) W.carrier V') (hσ : σ.IsConstituent ρ)
    {γ : ℝ} (hγ : W.HasDetWeight l σ ι γ) :
    W.IsPunctuallyPure l σ ι γ := by
  intro y α hα
  obtain ⟨U, _, _, _, _, WU, r, hyU, hcont, hsurj, hdeg, hr⟩ := exists_restriction_isAffine W y.1
  have hpure := isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine WU l (ρ.comp r) ι
    (hρ.comp_of_continuous hcont hdeg) (hreal.comp_of_isConj hr) (σ.comp r) (hσ.comp hsurj)
    (hγ.comp_of_isConj hr)
  let x : U.toScheme.finitePoints :=
    ⟨⟨y.1, hyU⟩, (Scheme.Hom.mem_finitePoints_iff_of_isIso U.ι _).1 y.2⟩
  exact frobeniusWeight_eq_of_isPunctuallyPure_comp hr hpure x y rfl hα

end WeilGroup

end AlgebraicGeometry
