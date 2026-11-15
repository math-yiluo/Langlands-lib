import Langlands.Algebra.CoinvariantsNormTorsion
import Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityStatement
import Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof
import Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugatorExistence
import Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof
import Langlands.GroupScheme.Torus.InducedBasisTransport
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Mathlib.FieldTheory.Minpoly.Field

/-! # Injectivity of inertia coinvariants for a central induced torus quotient: proof -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section Lattices

variable (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]

/-- Over a separable closure, the Galois group acts on the actual algebraic fundamental
group through finitely many operators. -/
theorem fundamentalGroupGalois_finite_range (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) :
    (Set.range (fundamentalGroupGalois k G E hG)).Finite := by
  classical
  let a := chosenChoice k G hG
  have hs := isSplitTorus_baseChange_of_isSepClosure (E := E) a.torus a.isMaximal.1
  obtain ⟨L, hL, hfix⟩ := torusLatticeGaloisContinuity k E a.torus hs
  have : FiniteDimensional k L := hL
  have htriv : ∀ σ : E ≃ₐ[k] E, (∀ x ∈ L, σ x = x) →
      fundamentalGroupGalois k G E hG σ = 1 := by
    intro σ hσ
    apply LinearMap.ext
    intro x
    obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
    change a.galoisRepresentation E σ (a.projection E ν) = a.projection E ν
    rw [Choice.galoisRepresentation_projection, (hfix σ hσ).2]
    rfl
  let r : (E ≃ₐ[k] E) → (L →ₐ[k] E) := fun σ => (σ : E →ₐ[k] E).comp L.val
  have hr : ∀ σ τ, r σ = r τ →
      fundamentalGroupGalois k G E hG σ = fundamentalGroupGalois k G E hG τ := by
    intro σ τ h
    have h1 : fundamentalGroupGalois k G E hG (τ⁻¹ * σ) = 1 := by
      apply htriv
      intro x hx
      have hx' : σ x = τ x := congrArg (fun φ : L →ₐ[k] E => φ ⟨x, hx⟩) h
      change τ.symm (σ x) = x
      rw [hx']
      exact τ.symm_apply_apply x
    calc fundamentalGroupGalois k G E hG σ =
        fundamentalGroupGalois k G E hG (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
      _ = fundamentalGroupGalois k G E hG τ := by rw [map_mul, h1, mul_one]
  let F : (L →ₐ[k] E) → Module.End ℤ (fundamentalGroup k G E hG) := fun φ =>
    if h : ∃ σ, r σ = φ then fundamentalGroupGalois k G E hG h.choose else 1
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨r σ, ?_⟩
  have h : ∃ τ, r τ = r σ := ⟨σ, rfl⟩
  simp only [F, h, ↓reduceDIte]
  exact hr _ _ h.choose_spec

variable (Z : CommGroupScheme (Spec (CommRingCat.of k)))

/-- An induced torus has a finite integral character basis over the separable closure,
permuted by the whole Galois group. -/
theorem IsInducedTorus.exists_permuted_character_basis_of_isSepClosure
    (hZ : IsInducedTorus Z) :
    ∃ (Idx : Type u) (_ : Finite Idx)
      (b : Module.Basis Idx ℤ
        (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Z))),
      ∀ (σ : E ≃ₐ[k] E) (i : Idx), ∃ j : Idx,
        characterLattice.galoisRepresentation k E Z σ (b i) = b j := by
  classical
  obtain ⟨E', hEF, hEA, hEfin, hEgal, hE', I, b, hb⟩ := hZ
  let : Field E' := hEF
  let : Algebra k E' := hEA
  let : FiniteDimensional k E' := hEfin
  let : IsGalois k E' := hEgal
  have : IsSepClosed E := IsSepClosure.sep_closed k
  let e : E' →ₐ[k] E := IsSepClosed.lift
  let : Algebra E' E := e.toRingHom.toAlgebra
  let : IsScalarTower k E' E := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  let rr := characterLattice.restriction Z (characterLattice.fieldTestMap e)
  have hrr := characterLattice.field_restriction_bijective Z e hE'
  let aE := AddEquiv.ofBijective rr hrr
  refine ⟨I, hE'.finite_character_basis b, b.map aE.toIntLinearEquiv, ?_⟩
  intro τ i
  let σ : E' ≃ₐ[k] E' := τ.restrictNormal E'
  have hτ : ∀ x, τ (e x) = e (σ x) := fun x => (τ.restrictNormal_commutes E' x).symm
  obtain ⟨j, hj⟩ := hb σ i
  refine ⟨j, ?_⟩
  change characterLattice.galoisRepresentation k E Z τ (rr (b i)) = rr (b j)
  rw [← characterLattice.restriction_galois Z e σ τ hτ, hj]

/-- An induced torus has an integral cocharacter basis over the separable closure,
permuted by the whole Galois group: the dual of a permuted character basis. -/
theorem IsInducedTorus.exists_permuted_cocharacter_basis_of_isSepClosure
    (hZ : IsInducedTorus Z) :
    ∃ (Idx : Type u)
      (b : Module.Basis Idx ℤ
        (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Z))),
      ∀ (σ : E ≃ₐ[k] E) (i : Idx), ∃ j : Idx,
        cocharacterLattice.galoisRepresentation k E Z σ (b i) = b j := by
  classical
  obtain ⟨Idx, hIdx, b, hb⟩ :=
    IsInducedTorus.exists_permuted_character_basis_of_isSepClosure k E Z hZ
  have := hIdx
  have hs := isSplitTorus_baseChange_of_isSepClosure (E := E) Z hZ.isTorus
  have : (latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Z)).IsPerfPair :=
    hs.isPerfPair_latticePairing
  let p := (latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Z)).flip
  refine ⟨Idx, Langlands.PermutationBasis.pairedBasis p b, ?_⟩
  intro σ i
  let f : Idx → Idx := fun i => (hb σ i).choose
  have hf : ∀ i, characterLattice.galoisRepresentation k E Z σ (b i) = b (f i) :=
    fun i => (hb σ i).choose_spec
  have hfinj : Function.Injective f := by
    intro i i' h
    have h1 : characterLattice.galoisRepresentation k E Z σ (b i) =
        characterLattice.galoisRepresentation k E Z σ (b i') := by rw [hf, hf, h]
    have h2 := congrArg (characterLattice.galoisRepresentation k E Z σ⁻¹) h1
    rw [Representation.inv_self_apply, Representation.inv_self_apply] at h2
    exact b.injective h2
  let e : Equiv.Perm Idx := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  refine ⟨e i, ?_⟩
  exact Langlands.PermutationBasis.pairedBasis_permutation p b
    (cocharacterLattice.galoisRepresentation k E Z σ)
    (characterLattice.galoisRepresentation k E Z σ) e
    (fun x y => latticePairing_galoisRepresentation k E Z σ y x) hf i

/-- The actual algebraic fundamental group of an induced torus has an integral basis
permuted by the Galois group, transported through the torus comparison `π₁(Z) ≅ X_*(Z)`. -/
theorem IsInducedTorus.exists_permuted_fundamentalGroup_basis (hZ : IsInducedTorus Z) :
    ∃ (Idx : Type u)
      (b : Module.Basis Idx ℤ (fundamentalGroup k Z.toGrp E
        hZ.isTorus.isConnectedReductive_of_fieldSplitting)),
      ∀ (σ : E ≃ₐ[k] E) (i : Idx), ∃ j : Idx,
        fundamentalGroupGalois k Z.toGrp E hZ.isTorus.isConnectedReductive_of_fieldSplitting σ
          (b i) = b j := by
  obtain ⟨Idx, b, hb⟩ :=
    IsInducedTorus.exists_permuted_cocharacter_basis_of_isSepClosure k E Z hZ
  obtain ⟨-, -, hbij, hgal⟩ := torusFundamentalComparison_proof k E Z hZ.isTorus
  let c := LinearEquiv.ofBijective (torusFundamentalComparison k E Z hZ.isTorus) hbij
  have hc : ∀ y, torusFundamentalComparison k E Z hZ.isTorus (c.symm y) = y :=
    fun y => c.apply_symm_apply y
  refine ⟨Idx, b.map c.symm, ?_⟩
  intro σ i
  obtain ⟨j, hj⟩ := hb σ i
  refine ⟨j, hbij.injective ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.map_apply, hgal, hc, hc, hj]

end Lattices

/-- **Injectivity of inertia coinvariants for a central induced torus quotient**
(Kaletha–Prasad, proof of Proposition 11.5.3). The selected map
`π₁(Z)_I → π₁(H)_I` is injective. The proof combines the injectivity of
`π₁(Z) → π₁(H)`, a norm over the finitely many operators by which inertia acts, and the
torsion-freeness of the coinvariants of the permutation lattice `π₁(Z)`. -/
theorem inducedCentralTorusInertiaInjectivity :
    InducedCentralTorusInertiaInjectivityStatement.{u} := by
  intro k K E _ _ _ _ _ _ _ _ _ Z hZ H G hH hG i p hi hc hq
  have : Normal k E := inferInstance
  have hZr := hZ.isTorus.isConnectedReductive_of_fieldSplitting
  have hj : Function.Injective (fundamentalGroupMap k E Z.toGrp H hZr hH i) :=
    (centralTorusFundamentalExactness k E Z hZ.isTorus H G hH hG i p hi hc hq).1
  have heq := (algebraicFundamentalGroupMap k E Z.toGrp H hZr hH
    (chosenChoice k Z.toGrp hZr) (chosenChoice k H hH) i).2.2.1
  have hspec := ((fundamentalInertiaMapStatement k K E).1 Z.toGrp H hZr hH i).2.1
  obtain ⟨Idx, b, hb⟩ := IsInducedTorus.exists_permuted_fundamentalGroup_basis k E Z hZ
  refine Langlands.CoinvariantsNorm.injective_of_finite_range
    ((fundamentalGroupGalois k Z.toGrp E hZr).comp (relativeInertia k K E).subtype)
    ((fundamentalGroupGalois k H E hH).comp (relativeInertia k K E).subtype)
    (fundamentalGroupMap k E Z.toGrp H hZr hH i) hj (fun g x => heq g x) ?_ ?_ _ hspec
  · refine (fundamentalGroupGalois_finite_range k E H hH).subset ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · intro n x hn hx
    exact Langlands.CoinvariantsNorm.eq_zero_of_smul_eq_zero_of_permuted
      ((fundamentalGroupGalois k Z.toGrp E hZr).comp (relativeInertia k K E).subtype) b
      (fun g i => hb g.1 i) hn hx

end Langlands.Geometry.Building.Kottwitz
