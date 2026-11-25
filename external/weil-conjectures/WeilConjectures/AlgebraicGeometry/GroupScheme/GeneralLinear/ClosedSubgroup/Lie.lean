/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation
public import WeilConjectures.RingTheory.HopfAlgebra.Cartier

/-!
# The Lie algebras of the closed subgroup schemes of `GL_n`

Let `V(I)` be the closed subgroup scheme of `𝔾𝕃(n; k)` cut out by a Hopf ideal `I` of the
coordinate ring `k[GL_n]` (`AlgebraicGeometry.GeneralLinearGroup.subgroupScheme`). This file
specialises the general theory of `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie` and
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie` to these groups, in the language
of Hopf ideals used by the weight arguments: the differentials `Lie(V(J)) → Lie(V(I))` of the
closed immersions, the Lie algebra clauses of Cartier's theorem for the *reduced* identity
component `V(identityComponent I)`, and the matrix description of the tangent vectors
`1 + εX` of `V(I)`.

Everything that holds for an arbitrary group scheme is stated there, for an arbitrary group scheme;
what remains here is specific to the reduced identity component and the reduced centre, which this
development only has in Hopf-ideal form, and to the matrix description of the points of `V(I)`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraMap`: the differential of the closed immersion
  `V(J) ⟶ V(I)` of closed subgroup schemes of `GL_n`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap`,
  `AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap_identityComponent`: if the
  closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)`, then the Lie algebra of `V(J)`,
  and of its identity component, contains the brackets of the Lie algebra of `V(I)`, respectively of
  its identity component.
- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraMap_identityComponent_bijective`,
  `AlgebraicGeometry.GeneralLinearGroup.finrank_lie_eq_ringKrullDim`: the Lie algebra only sees
  the reduced identity component and has the dimension of the group (Cartier's theorem).
- `AlgebraicGeometry.GeneralLinearGroup.dualUnit_mem_zeroLocus_identityComponent`,
  `AlgebraicGeometry.GeneralLinearGroup.mem_range_dualCotangentToMatrixₗ`,
  `AlgebraicGeometry.GeneralLinearGroup.finrank_cotangent_eq_finrank_range_dualCotangentToMatrixₗ`:
  the matrix form of these clauses of Cartier's theorem, for the points `1 + εX` of `V(I)` over the
  dual numbers: in characteristic zero they are points of the reduced identity component, and they
  are the dual of the cotangent space `𝔪/𝔪²` of `k[GL_n] ⧸ I` at the identity.
- `AlgebraicGeometry.GeneralLinearGroup.eq_of_le_of_bijective_lieAlgebraMap`: a closed subgroup
  of a connected matrix group with the same Lie algebra is the whole group.
The group–Lie comparison (`lemma-stable-subspaces-center`) and the central–geometric product
(`lemma-identity-component`) for these groups are in
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Comparison` and
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Product`.

## Blueprint

- `def-wf-lie-algebra-derivation`: the Lie algebra of an algebraic group as its tangent space at the
  identity.
- `proposition-cartier-s-theorem`: the Lie algebra clauses of Cartier's theorem.
- `lemma-restriction-normal-subgroup`: pairs `V(J) ⊆ V(I)` with `⁅V(I), V(I)⁆ ⊆ V(J)`.
- `lemma-identity-component`: the multiplication morphism `Z(G°)° × H° ⟶ G°`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory TrivSqZeroExt
open scoped MonObj Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

section ClosedSubgroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The differential `Lie(V(J)) → Lie(V(I))` of the closed immersion `V(J) ⟶ V(I)`, an injective
homomorphism of Lie algebras. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable abbrev lieAlgebraMap (h : I ≤ J) :
    GrpObj.Lie (subgroupScheme J) →ₗ⁅k⁆ GrpObj.Lie (subgroupScheme I) :=
  GrpObj.differential (subgroupSchemeHom h)

theorem lieAlgebraMap_injective (h : I ≤ J) : Function.Injective (lieAlgebraMap h) :=
  GrpObj.differential_injective _

/-- If the closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)`, then the bracket of two
tangent vectors of `V(I)` is a tangent vector of `V(J)`: the bracket is the mixed term of the
commutator of the points `1 + εX` and `1 + δY` over `k[ε, δ]/(ε², δ²)`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
theorem lie_mem_range_lieAlgebraMap (h : I ≤ J) [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    (X Y : GrpObj.Lie (subgroupScheme I)) : ⁅X, Y⁆ ∈ (lieAlgebraMap h).range :=
  GrpObj.lie_mem_range_differential_of_containsCommutators (subgroupSchemeHom h) X Y

end ClosedSubgroup

section Cartier

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The point `1 + εX` of `GL_n` with values in the dual numbers reduces to the identity modulo
`ε`: as an algebra map on the coordinate ring, its reduction is the counit. -/
theorem fst_comp_evalAlgHom_dualUnit (X : Matrix n n k) :
    (fstHom k k k).comp (evalAlgHom (dualUnit X)) =
      Bialgebra.counitAlgHom k (CoordinateRing n k) := by
  rw [← evalAlgHom_map, map_fstHom_dualUnit]
  rfl

/-- In characteristic zero, every tangent vector of `G = V(I)` is tangent to the reduced identity
component, in matrix form: a point `1 + εX` of `V(I)` with values in the dual numbers is a point
of `V(identityComponent I)`.

`identityComponent I` is the ideal of the *reduced* identity component. By Cartier's lemma
(`Bialgebra.isPrime_iInf_pow_ker_counitAlgHom`) the functions on `G` vanishing near the identity
form a prime ideal `P`, so `V(P)` is an irreducible closed subset of `V(I)` through the identity,
contained in the identity component. A function vanishing on the identity component thus lies
in `P`, hence vanishes in the local ring at the identity and on every tangent vector there.
(blueprint: `lemma-connected-components-images-homomorphisms--3`, clause (3)) -/
theorem dualUnit_mem_zeroLocus_identityComponent [IsAlgClosed k] [CharZero k] {X : Matrix n n k}
    (hX : dualUnit X ∈ zeroLocus I (DualNumber k)) :
    dualUnit X ∈ zeroLocus (identityComponent I) (DualNumber k) := by
  rw [mem_zeroLocus] at hX ⊢
  intro a ha
  set B := CoordinateRing n k ⧸ I
  set P := ⨅ r : ℕ, RingHom.ker (Bialgebra.counitAlgHom k B) ^ r
  have hP : P.IsPrime := Bialgebra.isPrime_iInf_pow_ker_counitAlgHom k B
  set P' := P.comap (Ideal.Quotient.mk I)
  have hP' : P'.IsPrime := Ideal.IsPrime.comap _ (hK := hP)
  have hIP : I ≤ P' := fun b hb ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hb]
    exact zero_mem _
  have h1 : toPrimeSpectrum (1 : GL n k) ∈
      PrimeSpectrum.zeroLocus (P' : Set (CoordinateRing n k)) := fun b hb ↦ by
    have hb' : Ideal.Quotient.mk I b ∈ RingHom.ker (Bialgebra.counitAlgHom k B) := by
      have := (Submodule.mem_iInf _).1 (Ideal.mem_comap.1 hb) 1
      rwa [pow_one] at this
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, Bialgebra.Quotient.counit_mk] at hb'
    exact hb'
  have hsub : PrimeSpectrum.zeroLocus (P' : Set (CoordinateRing n k)) ⊆
      connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
        (toPrimeSpectrum 1) :=
    (IsPreirreducible.isPreconnected ((PrimeSpectrum.isIrreducible_zeroLocus_iff P').2
      (by rw [hP'.radical]; exact hP')).2).subset_connectedComponentIn h1
        (PrimeSpectrum.zeroLocus_anti_mono hIP)
  have haP : Ideal.Quotient.mk I a ∈ P := by
    have := PrimeSpectrum.vanishingIdeal_anti_mono hsub ha
    rwa [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hP'.radical] at this
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  obtain ⟨s, hs, hsa⟩ := AlgHom.mem_iInf_pow_ker_iff.1 haP
  let φ : B →ₐ[k] DualNumber k := Ideal.Quotient.liftₐ I (evalAlgHom (dualUnit X)) hX
  have hφ : (fstHom k k k).comp φ = Bialgebra.counitAlgHom k B := by
    refine Ideal.Quotient.algHom_ext _ ?_
    rw [AlgHom.comp_assoc]
    exact fst_comp_evalAlgHom_dualUnit X
  have hunit : IsUnit (φ s) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    have := congrArg (· s) hφ
    simp only [AlgHom.comp_apply, fstHom_apply] at this
    rw [this, hs]
    exact isUnit_one
  have h := congrArg φ hsa
  rw [map_mul, map_zero] at h
  exact (hunit.mul_right_eq_zero).1 h

/-- A tangent vector of `V(I)` whose matrix satisfies the equations of `J ≥ I` is tangent to
`V(J)`. -/
theorem exists_kerPost_eq_of_mem_zeroLocus {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k]
    (h : I ≤ J) (p : GrpObj.pointsKer (subgroupScheme I) GrpObj.aug₁)
    (hp : GeneralLinearGroup.homMulEquiv n k (DualNumber k) (p.1 ≫ subgroupSchemeι I) ∈
      zeroLocus J (DualNumber k)) :
    ∃ q : GrpObj.pointsKer (subgroupScheme J) GrpObj.aug₁,
      GrpObj.kerPost (subgroupSchemeHom h) q = p := by
  set q₀ := zeroLocusMulEquiv J (DualNumber k) ⟨_, hp⟩
  have hq₀ : q₀ ≫ subgroupSchemeHom h = p.1 := by
    rw [zeroLocusMulEquiv_comp_subgroupSchemeHom]
    apply injective_homMulEquiv_comp I (DualNumber k)
    dsimp only
    rw [homMulEquiv_zeroLocusMulEquiv_comp]
  have hmem : q₀ ∈ GrpObj.pointsKer (subgroupScheme J) (GrpObj.aug₁ (k := k)) := by
    rw [GrpObj.mem_pointsKer]
    apply (cancel_mono (subgroupSchemeHom h)).1
    rw [MonObj.one_comp, points.map, Category.assoc, hq₀]
    exact GrpObj.mem_pointsKer.1 p.2
  exact ⟨⟨q₀, hmem⟩, Subtype.ext hq₀⟩

-- the group structure on points of the quotient scheme makes instance search slow
/-- In characteristic zero, every tangent vector of `G = V(I)` is tangent to the reduced identity
component `V(identityComponent I)`: the differential `Lie(G°) → Lie(G)` is bijective.

`CharZero` is needed because `identityComponent I` is the ideal of the *reduced* identity
component. The matrix form, for the points `1 + εX` of `V(I)` over the dual numbers, is
`dualUnit_mem_zeroLocus_identityComponent`: a tangent vector `1 + εX` of `V(I)` satisfies the
equations of `identityComponent I`, so it is the image of a tangent vector of
`V(identityComponent I)` (`exists_kerPost_eq_of_mem_zeroLocus`). (blueprint:
`proposition-cartier-s-theorem`) -/
theorem lieAlgebraMap_identityComponent_bijective [IsAlgClosed k] [CharZero k] :
    Function.Bijective (lieAlgebraMap (le_identityComponent I)) := by
  refine ⟨lieAlgebraMap_injective _, fun x ↦ ?_⟩
  obtain ⟨p, hpx⟩ : ∃ p, GrpObj.lieEquivTangent _ x = p := ⟨_, rfl⟩
  obtain ⟨X, hXp⟩ : ∃ X, tangentMatrix n k (GrpObj.kerPost (subgroupSchemeι I) p) = X :=
    ⟨_, rfl⟩
  have hX : GeneralLinearGroup.homMulEquiv n k (DualNumber k) (p.1 ≫ subgroupSchemeι I) =
      dualUnit X :=
    Units.ext (by
      rw [show p.1 ≫ subgroupSchemeι I = (GrpObj.kerPost (subgroupSchemeι I) p).1 from rfl,
        coe_homMulEquiv_tangent, hXp, coe_dualUnit])
  have hI : dualUnit X ∈ zeroLocus I (DualNumber k) := by
    rw [← hX, ← SetLike.mem_coe, ← range_homMulEquiv_comp I (DualNumber k)]
    exact Set.mem_range_self p.1
  have hI' := dualUnit_mem_zeroLocus_identityComponent I hI
  rw [← hX] at hI'
  obtain ⟨q, hq⟩ := exists_kerPost_eq_of_mem_zeroLocus I (le_identityComponent I) p hI'
  refine ⟨(GrpObj.lieEquivTangent _).symm q, (GrpObj.lieEquivTangent _).injective ?_⟩
  rw [GrpObj.lieEquivTangent_differential, Equiv.apply_symm_apply, hq, hpx]

/-- Over an algebraically closed field of characteristic zero, the Lie algebra of an algebraic
group is the Lie algebra of its reduced identity component. (blueprint:
`proposition-cartier-s-theorem`) -/
noncomputable def lieAlgebraEquivIdentityComponent [IsAlgClosed k] [CharZero k] :
    GrpObj.Lie (subgroupScheme (identityComponent I)) ≃ₗ⁅k⁆ GrpObj.Lie (subgroupScheme I) :=
  LieEquiv.ofBijective _ (lieAlgebraMap_identityComponent_bijective I)

/-! #### The tangent space at the identity, in matrices

The points `1 + εX` of `V(I)` over the dual numbers are the linear forms on the cotangent space
`𝔪/𝔪²` of the coordinate ring `k[GL_n] ⧸ I` at the identity: `X i j = ψ (x_ij - δ_ij)`. -/

local notation "𝔪" => RingHom.ker (Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I))

/-- The tangent vector `X ∈ gl_n` of a linear form `ψ` on the cotangent space at the identity of
`V(I)`: `X i j = ψ (x_ij - δ_ij)`. -/
noncomputable def dualCotangentToMatrix (ψ : Module.Dual k (𝔪).Cotangent) : Matrix n n k :=
  Matrix.of fun i j ↦ (Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I)).cotangentDerivation ψ
    (Ideal.Quotient.mk I (coord n k i j))

/-- The point `1 + εX_ψ` of `V(I)` is the dual-number point of the tangent vector `ψ`. -/
theorem evalAlgHom_dualUnit_dualCotangentToMatrix (ψ : Module.Dual k (𝔪).Cotangent) :
    evalAlgHom (k := k) (R := DualNumber k) (dualUnit (dualCotangentToMatrix I ψ)) =
      ((Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I)).toDualNumber ψ).comp
        (Ideal.Quotient.mkₐ k I) := by
  refine algHom_ext fun i j ↦ ?_
  rw [evalAlgHom_coord, coe_dualUnit, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.fst_toDualNumber, Bialgebra.counitAlgHom_apply, Bialgebra.Quotient.counit_mk]
    rw [counit_coord]
    simp [Matrix.one_apply, apply_ite TrivSqZeroExt.fst]
  · rw [AlgHom.snd_toDualNumber]
    simp [Matrix.one_apply, apply_ite TrivSqZeroExt.snd, dualCotangentToMatrix]

theorem dualUnit_dualCotangentToMatrix_mem_zeroLocus (ψ : Module.Dual k (𝔪).Cotangent) :
    dualUnit (dualCotangentToMatrix I ψ) ∈ zeroLocus I (DualNumber k) :=
  mem_zeroLocus.2 fun a ha ↦ by
    rw [evalAlgHom_dualUnit_dualCotangentToMatrix, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/-- `ψ ↦ X_ψ`, from the dual of the cotangent space of `k[GL_n] ⧸ I` at the identity to `gl_n`,
as a linear map. -/
noncomputable def dualCotangentToMatrixₗ : Module.Dual k (𝔪).Cotangent →ₗ[k] Matrix n n k where
  toFun := dualCotangentToMatrix I
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem dualCotangentToMatrixₗ_apply (ψ : Module.Dual k (𝔪).Cotangent) :
    dualCotangentToMatrixₗ I ψ = dualCotangentToMatrix I ψ :=
  rfl

theorem dualCotangentToMatrixₗ_injective : Function.Injective (dualCotangentToMatrixₗ I) :=
  fun ψ ψ' h ↦ by
    have h' := congrArg (fun X : Matrix n n k ↦
      evalAlgHom (k := k) (R := DualNumber k) (dualUnit X)) h
    simp only [dualCotangentToMatrixₗ_apply, evalAlgHom_dualUnit_dualCotangentToMatrix] at h'
    exact AlgHom.toDualNumber_injective (Ideal.Quotient.algHom_ext k h')

/-- The tangent vectors of `V(I)` at the identity, as matrices, are exactly the `X ∈ gl_n` with
`1 + εX ∈ V(I)`: the range of `ψ ↦ X_ψ`. -/
theorem mem_range_dualCotangentToMatrixₗ {X : Matrix n n k} :
    X ∈ LinearMap.range (dualCotangentToMatrixₗ I) ↔ dualUnit X ∈ zeroLocus I (DualNumber k) := by
  refine ⟨?_, fun hX ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩
    exact dualUnit_dualCotangentToMatrix_mem_zeroLocus I ψ
  · let φ : (CoordinateRing n k ⧸ I) →ₐ[k] DualNumber k :=
      Ideal.Quotient.liftₐ I (evalAlgHom (k := k) (R := DualNumber k) (dualUnit X))
        (mem_zeroLocus.1 hX)
    have hφ : (fstHom k k k).comp φ = Bialgebra.counitAlgHom k _ := by
      refine Ideal.Quotient.algHom_ext _ ?_
      rw [AlgHom.comp_assoc]
      exact fst_comp_evalAlgHom_dualUnit _
    refine ⟨(Bialgebra.counitAlgHom k _).cotangentForm φ hφ, ?_⟩
    ext i j
    change dualCotangentToMatrix I _ i j = _
    rw [dualCotangentToMatrix, Matrix.of_apply]
    rw [← AlgHom.snd_toDualNumber, AlgHom.toDualNumber_cotangentForm]
    simp [φ, coe_dualUnit, Matrix.one_apply, apply_ite TrivSqZeroExt.snd]

/-- The dimension of the cotangent space of `k[GL_n] ⧸ I` at the identity is the dimension of
the space of matrices `X` with `1 + εX ∈ V(I)`. -/
theorem finrank_cotangent_eq_finrank_range_dualCotangentToMatrixₗ :
    Module.finrank k (𝔪).Cotangent =
      Module.finrank k (LinearMap.range (dualCotangentToMatrixₗ I)) := by
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  have := (Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I)).finiteDimensional_cotangent
  rw [LinearMap.finrank_range_of_inj (dualCotangentToMatrixₗ_injective I),
    Subspace.dual_finrank_eq]

/-- The matrix `X` of a tangent vector `1 + εX` of `V(I)`: the differential of `V(I) ⟶ GL_n`
followed by `Lie(GL_n) = gl_n`. -/
noncomputable def lieToMatrix : GrpObj.Lie (subgroupScheme I) →ₗ[k] Matrix n n k :=
  (lieAlgebraEquivMatrix n k).toLinearEquiv.toLinearMap ∘ₗ
    (GrpObj.differential (subgroupSchemeι I)).toLinearMap

theorem lieToMatrix_apply (x : GrpObj.Lie (subgroupScheme I)) :
    lieToMatrix I x = tangentMatrix n k
      (GrpObj.kerPost (subgroupSchemeι I) (GrpObj.lieEquivTangent _ x)) := by
  change toMatrix n k (GrpObj.differential (subgroupSchemeι I) x) = _
  rw [toMatrix, GrpObj.lieEquivTangent_differential]

theorem lieToMatrix_injective : Function.Injective (lieToMatrix I) :=
  (lieAlgebraEquivMatrix n k).injective.comp (GrpObj.differential_injective _)

/-- The matrices of the tangent vectors of `V(I)` are the `X` with `1 + εX ∈ V(I)`. -/
theorem range_lieToMatrix :
    LinearMap.range (lieToMatrix I) = LinearMap.range (dualCotangentToMatrixₗ I) := by
  ext X
  rw [mem_range_dualCotangentToMatrixₗ]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p, GrpObj.lieEquivTangent _ x = p := ⟨_, rfl⟩
    have hX : GeneralLinearGroup.homMulEquiv n k (DualNumber k) (p.1 ≫ subgroupSchemeι I) =
        dualUnit (lieToMatrix I x) :=
      Units.ext (by
        rw [lieToMatrix_apply, hp, coe_dualUnit,
          show p.1 ≫ subgroupSchemeι I = (GrpObj.kerPost (subgroupSchemeι I) p).1 from rfl,
          coe_homMulEquiv_tangent])
    rw [← hX, ← SetLike.mem_coe, ← range_homMulEquiv_comp I (DualNumber k)]
    exact Set.mem_range_self p.1
  · intro hX
    set q₀ := zeroLocusMulEquiv I (DualNumber k) ⟨_, hX⟩
    have hq₀ : GeneralLinearGroup.homMulEquiv n k (DualNumber k) (q₀ ≫ subgroupSchemeι I) =
        dualUnit X :=
      homMulEquiv_zeroLocusMulEquiv_comp _
    have hmem : q₀ ∈ GrpObj.pointsKer (subgroupScheme I) (GrpObj.aug₁ (k := k)) := by
      rw [GrpObj.mem_pointsKer]
      apply (cancel_mono (subgroupSchemeι I)).1
      rw [MonObj.one_comp]
      apply (GeneralLinearGroup.homMulEquiv n k k).injective
      change GeneralLinearGroup.homMulEquiv n k k
        (points.map _ (GrpObj.aug₁ (k := k)) (q₀ ≫ subgroupSchemeι I)) = _
      rw [homMulEquiv_points_map, hq₀, map_one]
      exact map_fstHom_dualUnit X
    refine ⟨(GrpObj.lieEquivTangent _).symm ⟨q₀, hmem⟩, ?_⟩
    rw [lieToMatrix_apply, Equiv.apply_symm_apply, tangentMatrix]
    change (((GeneralLinearGroup.homMulEquiv n k (DualNumber k) (q₀ ≫ subgroupSchemeι I)) :
      GL n (DualNumber k)) : Matrix n n (DualNumber k)).map snd = X
    rw [hq₀, coe_dualUnit]
    ext i j
    simp [Matrix.one_apply, apply_ite]

/-- Cartier's theorem, Lie algebra form: over a field of characteristic zero, the Lie algebra of
a closed subgroup scheme `V(I)` has dimension the Krull dimension of its coordinate ring. This is
`AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim` for the affine scheme
`V(I) = Spec (k[GL_n] ⧸ I)`: `Lie(V(I))` is the dual of the cotangent space at the identity, whose
dimension is `dim (k[GL_n] ⧸ I)` by `HopfAlgebra.finrank_cotangent_eq_ringKrullDim`.
(blueprint: `proposition-cartier-s-theorem`) -/
theorem finrank_lie_eq_ringKrullDim [CharZero k] :
    (Module.finrank k (GrpObj.Lie (subgroupScheme I)) : WithBot ℕ∞) =
      ringKrullDim (CoordinateRing n k ⧸ I) := by
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  rw [← LinearMap.finrank_range_of_inj (lieToMatrix_injective I), range_lieToMatrix,
    ← finrank_cotangent_eq_finrank_range_dualCotangentToMatrixₗ]
  exact HopfAlgebra.finrank_cotangent_eq_ringKrullDim k _

/-- A closed subgroup `V(J)` of a connected matrix group `V(I)` with the same Lie algebra is all of
`V(I)`, in characteristic zero: the Lie algebras have the dimensions of the groups
(`finrank_lie_eq_ringKrullDim`), and `V(I)` is irreducible
(`Matrix.GeneralLinearGroup.IsConnected.isPrime`).
(blueprint: `lemma-connected-components-images-homomorphisms--3`, clause (1)) -/
theorem eq_of_le_of_bijective_lieAlgebraMap [IsAlgClosed k] [CharZero k] (hconn : IsConnected I)
    {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (hIJ : I ≤ J)
    (h : Function.Bijective (lieAlgebraMap hIJ)) : J = I := by
  have := hconn.isPrime
  refine eq_of_le_of_ringKrullDim_eq I hIJ ?_
  rw [← finrank_lie_eq_ringKrullDim J, ← finrank_lie_eq_ringKrullDim I,
    (LieEquiv.ofBijective _ h).toLinearEquiv.finrank_eq]

end Cartier

/-! ### Pairs of closed subgroup schemes with commutative quotient

Let `H = V(J) ⊆ G = V(I)` be closed subgroup schemes of `GL_n`, `I ≤ J`, such that the inclusion
`H ⟶ G` contains the commutators of `G` (`AlgebraicGeometry.IsMonHom.ContainsCommutators`), the
scheme-theoretic form of `⁅G, G⁆ ⊆ H`; then `H` is normal in `G`
(`AlgebraicGeometry.IsMonHom.Normal.of_containsCommutators`). The arithmetic and geometric
monodromy groups of a represented degree datum are such a pair, and the statements of the blueprint
about them are instances of the statements of this section. -/

section Pair

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The brackets of the Lie algebra of `G° = V(identityComponent I)` lie in the Lie algebra of
`H° = V(identityComponent J)`, when `H = V(J) ⊆ G = V(I)` contains the commutators of `G`: in
characteristic zero the identity components have the same Lie algebras as `G` and `H`
(`lieAlgebraEquivIdentityComponent`), and the differentials of `H° ⟶ G° ⟶ G` and `H° ⟶ H ⟶ G`
agree. (blueprint: `lemma-restriction-normal-subgroup`) -/
theorem lie_mem_range_lieAlgebraMap_identityComponent [IsAlgClosed k] [CharZero k] (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    (X Y : GrpObj.Lie (subgroupScheme (identityComponent I))) :
    ⁅X, Y⁆ ∈ (lieAlgebraMap (identityComponent_mono I h)).range := by
  have hcomm (w : GrpObj.Lie (subgroupScheme (identityComponent J))) :
      lieAlgebraMap (le_identityComponent I) (lieAlgebraMap (identityComponent_mono I h) w) =
        lieAlgebraMap h (lieAlgebraMap (le_identityComponent J) w) := by
    rw [lieAlgebraMap, lieAlgebraMap, lieAlgebraMap, lieAlgebraMap, ← LieHom.comp_apply,
      ← LieHom.comp_apply, ← GrpObj.differential_comp, ← GrpObj.differential_comp,
      GrpObj.differential_congr (subgroupSchemeHom_comp _ _),
      GrpObj.differential_congr (subgroupSchemeHom_comp _ _)]
  obtain ⟨z, hz⟩ := (LieHom.mem_range _ _).1 (lie_mem_range_lieAlgebraMap h
    (lieAlgebraMap (le_identityComponent I) X) (lieAlgebraMap (le_identityComponent I) Y))
  obtain ⟨w, rfl⟩ := (lieAlgebraMap_identityComponent_bijective J).2 z
  refine (LieHom.mem_range _ _).2 ⟨w, (lieAlgebraMap_identityComponent_bijective I).1 ?_⟩
  rw [hcomm, hz, LieHom.map_lie]

/-- The standard representation of the `k`-points of `V(I)` on `kⁿ`: a point `Spec k ⟶ V(I)` acts
through its image in `GL_n(k)` under the closed immersion `V(I) ⟶ GL_n`: the algebraic-group
module of `V(I) ⟶ GL_n`. (blueprint: `definition-monodromy-groups`,
`def-wf-algebraic-representations`) -/
noncomputable def standardRepresentation (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Representation k (points (subgroupScheme I) k) (n → k) :=
  RationalHom.representation (subgroupSchemeι I)

variable [IsAlgClosed k]

/-- The multiplication morphism `Z(G°)° × H° ⟶ G°` of group schemes, for closed subgroups
`H = V(J) ⊆ G = V(I)` of `GL_n`: the composite of the closed immersions of the two factors into
`G°` with the multiplication of `G°`. (blueprint: `lemma-identity-component`) -/
noncomputable def mulCenterIdentityComponent (h : I ≤ J) :
    subgroupScheme (identityComponent (center (identityComponent I))) ⊗
        subgroupScheme (identityComponent J) ⟶
      subgroupScheme (identityComponent I) :=
  (subgroupSchemeHom ((le_center _).trans (le_identityComponent _)) ⊗ₘ
      subgroupSchemeHom (identityComponent_mono I h)) ≫
    μ[subgroupScheme (identityComponent I)]

end Pair

end AlgebraicGeometry.GeneralLinearGroup
