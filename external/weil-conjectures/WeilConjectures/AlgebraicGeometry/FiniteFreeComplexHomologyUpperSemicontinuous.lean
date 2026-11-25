/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Semicontinuity.Basic

import Mathlib.RingTheory.TensorProduct.Free
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank

/-! # Upper semicontinuity of fibre homology of finite free complexes

Source: Stacks Project, Derived Categories of Schemes, Lemma jump-loci, Tag 0BDI,
`literature/stacks-project/perfect.tex` (affine finite-free specialization).
(blueprint: lem-sc-finite-free-complex-homology-upper-semicontinuous).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

/-- The source library's tensor/scalar-extension equivalence, generalized to the
module universe of this theorem. See
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`. -/
private noncomputable def tensorEquiv (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{max u v} R) :
    TensorProduct R S N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : TensorProduct R S N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] TensorProduct R S N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.inductionOn with
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

private lemma tensorEquiv_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{max u v} R) (s : S) (n : N) :
    tensorEquiv R S N (TensorProduct.tmul R s n) =
      TensorProduct.tmul R
        (M := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S))
        s n :=
  rfl

private theorem rank_toMatrix {F : Type*} [Field F] {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y] [Module F X] [Module F Y]
    {m n : ℕ} (eX : Module.Basis (Fin m) F X) (eY : Module.Basis (Fin n) F Y)
    (f : X →ₗ[F] Y) :
    (LinearMap.toMatrix eX eY f).rank = Module.finrank F (LinearMap.range f) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ eY eX, Matrix.toLin_toMatrix]

/-- The two adjacent differentials of a finite free complex admit fixed finite matrices
whose residue-field ranks compute the dimension of fibre homology.

Source: Stacks Project, Tag 0BDI, proof of Lemma jump-loci in
`literature/stacks-project/perfect.tex`, affine finite-free specialization.
(blueprint: lem-sc-finite-free-complex-homology-upper-semicontinuous).

Proof: Choose finite bases in degrees `i - 1`, `i`, `i + 1`, with cardinalities
`a`, `c`, `b`, respectively. Let `M` be the matrix of the outgoing differential and
`N` that of the incoming differential. Tensoring the bases with a residue field gives
bases indexed by the same finite sets. In those bases the differentials have matrices
obtained by applying the residue-field map to every entry. In the resulting short
complex the incoming image lies in the outgoing kernel. Rank-nullity for the outgoing
map and for the quotient of its kernel by the incoming image gives
`dim H + rank M + rank N = c`. The categorical homology is isomorphic to this quotient,
so its finrank is the same. This works also with empty bases; no boundedness hypothesis
is needed because only three terms enter the calculation. -/
private theorem finiteFreeComplex_fibre_rank_formula
    (A : Type u) [CommRing A] (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hfree : ∀ n : ℤ, Module.Free A (K.X n) ∧ Module.Finite A (K.X n)) (i : ℤ) :
    ∃ a c b : ℕ, ∃ M : Matrix (Fin b) (Fin c) A, ∃ N : Matrix (Fin c) (Fin a) A,
      ∀ p : PrimeSpectrum A,
        Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars.{u, u, max u v}
            (algebraMap A p.asIdeal.ResidueField)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).homology i) +
          (M.map (algebraMap A p.asIdeal.ResidueField)).rank +
          (N.map (algebraMap A p.asIdeal.ResidueField)).rank = c := by
  classical
  have (n : ℤ) : Module.Free A (K.X n) := (hfree n).1
  have (n : ℤ) : Module.Finite A (K.X n) := (hfree n).2
  let d (n : ℤ) := Fintype.card (Module.Free.ChooseBasisIndex A (K.X n))
  let e (n : ℤ) : Module.Basis (Fin (d n)) A (K.X n) :=
    (Module.Free.chooseBasis A (K.X n)).reindex (Fintype.equivFin _)
  let M := LinearMap.toMatrix (e i) (e (i + 1)) (K.d i (i + 1)).hom
  let N := LinearMap.toMatrix (e (i - 1)) (e i) (K.d (i - 1) i).hom
  refine ⟨d (i - 1), d i, d (i + 1), M, N, ?_⟩
  intro p
  let F := p.asIdeal.ResidueField
  let Q := ((ModuleCat.extendScalars.{u, u, max u v}
    (algebraMap A F)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let E (n : ℤ) := tensorEquiv A F (K.X n)
  let ep (n : ℤ) : Module.Basis (Fin (d n)) F (Q.X n) :=
    (Algebra.TensorProduct.basis F (e n)).map (E n)
  have hmat (n m : ℤ) :
      LinearMap.toMatrix (ep n) (ep m) (Q.d n m).hom =
        (LinearMap.toMatrix (e n) (e m) (K.d n m).hom).map (algebraMap A F) := by
    rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
    have hmap : (E m).symm.toLinearMap ∘ₗ (Q.d n m).hom ∘ₗ (E n).toLinearMap =
        (K.d n m).hom.baseChange F := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s x =>
        apply (E m).injective
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul]
        change ((ModuleCat.extendScalars (algebraMap A F)).map (K.d n m))
          (tensorEquiv A F (K.X n) (TensorProduct.tmul A s x)) =
            tensorEquiv A F (K.X m) (TensorProduct.tmul A s ((K.d n m).hom x))
        rw [tensorEquiv_tmul, tensorEquiv_tmul]
        exact ModuleCat.ExtendScalars.map_tmul _ _ _ _
    rw [hmap]
    exact LinearMap.toMatrix_baseChange F (K.d n m).hom (e n) (e m)
  have : Module.Finite F (Q.X i) := Module.Finite.of_basis (ep i)
  have : Module.Finite F (Q.sc' (i - 1) i (i + 1)).X₂ :=
    inferInstanceAs (Module.Finite F (Q.X i))
  have hdim := (Q.sc' (i - 1) i (i + 1)).finrank_homology_add_finrank_range_add_finrank_range
  have hhom : Module.finrank F (Q.homology i) =
      Module.finrank F (Q.sc' (i - 1) i (i + 1)).homology :=
    (Q.homologyIsoSc' (i - 1) i (i + 1) (by simp) (by simp)).toLinearEquiv.finrank_eq
  have hout := rank_toMatrix (ep i) (ep (i + 1)) (Q.d i (i + 1)).hom
  have hin := rank_toMatrix (ep (i - 1)) (ep i) (Q.d (i - 1) i).hom
  rw [hmat] at hout hin
  have hmiddle : Module.finrank F (Q.X i) = d i := by
    simpa using Module.finrank_eq_card_basis (ep i)
  change Module.finrank F (Q.homology i) + _ + _ = d i
  rw [hhom, hout, hin, ← hmiddle]
  exact hdim

private theorem matrix_rank_locus (A : Type u) [CommRing A] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) A) (r : ℕ) :
    ∃ s : Finset A,
      {p : PrimeSpectrum A | r ≤ (M.map (algebraMap A p.asIdeal.ResidueField)).rank} =
        ⋃ f ∈ (s : Set A), (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
  classical
  let minors : (Fin r → Fin m) × (Fin r → Fin n) → A :=
    fun e ↦ (M.submatrix e.1 e.2).det
  refine ⟨Finset.univ.image minors, ?_⟩
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image,
    Finset.mem_univ, true_and]
  rw [Matrix.le_rank_map_iff]
  simp only [ne_eq, Ideal.algebraMap_residueField_eq_zero]
  constructor
  · rintro ⟨e₁, e₂, h⟩
    exact ⟨minors (e₁, e₂), ⟨(e₁, e₂), rfl⟩, h⟩
  · rintro ⟨f, ⟨e, rfl⟩, h⟩
    exact ⟨e.1, e.2, h⟩

private theorem principal_union_inter (A : Type u) [CommRing A] (s t : Finset A) :
    ∃ w : Finset A,
      (⋃ f ∈ (s : Set A), (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))) ∩
        (⋃ g ∈ (t : Set A), (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A))) =
      ⋃ h ∈ (w : Set A), (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum A)) := by
  classical
  refine ⟨(s ×ˢ t).image (fun fg ↦ fg.1 * fg.2), ?_⟩
  ext p
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨f, hf, hpf⟩, ⟨g, hg, hpg⟩⟩
    refine ⟨f * g, ⟨(f, g), ⟨hf, hg⟩, rfl⟩, ?_⟩
    rw [PrimeSpectrum.basicOpen_mul]
    exact ⟨hpf, hpg⟩
  · rintro ⟨h, ⟨⟨f, g⟩, ⟨hf, hg⟩, rfl⟩, hp⟩
    rw [PrimeSpectrum.basicOpen_mul] at hp
    exact ⟨⟨f, hf, hp.1⟩, ⟨g, hg, hp.2⟩⟩

private theorem principal_finite_union (A : Type u) [CommRing A] {ι : Type*}
    (t : Finset ι) (U : ι → Set (PrimeSpectrum A))
    (hU : ∀ j, ∃ s : Finset A,
      U j = ⋃ f ∈ (s : Set A), (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))) :
    ∃ s : Finset A,
      (⋃ j ∈ (t : Set ι), U j) =
        ⋃ f ∈ (s : Set A), (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
  classical
  choose s hs using hU
  refine ⟨t.biUnion s, ?_⟩
  ext p
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hp⟩
    rw [hs j] at hp
    simp only [Set.mem_iUnion, Finset.mem_coe] at hp
    obtain ⟨f, hf, hpf⟩ := hp
    exact ⟨f, ⟨j, hj, hf⟩, hpf⟩
  · rintro ⟨f, ⟨j, hj, hf⟩, hp⟩
    refine ⟨j, hj, ?_⟩
    rw [hs j]
    exact Set.mem_iUnion.2 ⟨f, Set.mem_iUnion.2 ⟨hf, hp⟩⟩

/-- For a bounded complex of finite free modules over a commutative ring, the dimension of
its homology after extension to each residue field is upper semicontinuous. Every integer
strict sublevel set is a finite union of principal opens, hence open and quasi-compact.

Source: Stacks Project, Derived Categories of Schemes, Lemma jump-loci, Tag 0BDI,
`literature/stacks-project/perfect.tex` (affine finite-free specialization).
(blueprint: lem-sc-finite-free-complex-homology-upper-semicontinuous).

Proof (the three steps of the node):
1. Choose finite bases in degrees `i - 1`, `i`, and `i + 1`. Write the adjacent
   differentials as matrices, with fibre ranks `r₀` and `r₁` (def-weil-matrix-rank).
   Rank-nullity for the outgoing differential, and then for the quotient of its kernel
   by the incoming image (lem-weil-pbc-idempotent-charpoly-rank-nullity), gives the fibre
   homology dimension `c - r₁ - r₀`, where `c` is the rank of the middle term.
2. The locus where a matrix has fibre rank at least `s` is the finite union of `D(Δ)`
   for its `s` by `s` minors (def-weil-matrix-rank). Laplace expansion gives the criterion
   using minors of exactly size `s`; the size-zero minor is `1`. Determinants commute
   with reduction to the residue field, and their reductions are nonzero exactly outside
   the prime. Intersections remain finite unions because `D(f) ∩ D(g) = D(fg)`.
3. For an integer threshold `r`, the inequality on the homology dimension is equivalent
   to `r₁ + r₀ > c - r`, with this comparison made in the integers. Both matrix ranks
   are bounded. Thus the sublevel set is the finite union over bounded pairs `(a, b)`
   satisfying `a + b > c - r` of the intersections of the loci `r₁ ≥ a` and `r₀ ≥ b`.
   Step 2 makes this a finite union of principal opens. Principal opens are open and
   quasi-compact, so these sublevel sets are open and quasi-compact and the dimension
   function is upper semicontinuous. -/
theorem finiteFreeComplex_homology_upperSemicontinuous
    (A : Type u) [CommRing A] (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hbounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free A (K.X n) ∧ Module.Finite A (K.X n)) (i : ℤ) :
    ∃ β : PrimeSpectrum A → ℕ,
      (∀ p : PrimeSpectrum A,
        β p = Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars.{u, u, max u v}
            (algebraMap A p.asIdeal.ResidueField)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).homology i)) ∧
      UpperSemicontinuous β ∧
      (∀ r : ℤ, ∃ s : Finset A,
        {p : PrimeSpectrum A | (β p : ℤ) < r} =
          ⋃ f ∈ (s : Set A), (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))) ∧
      (∀ r : ℤ, IsOpen {p : PrimeSpectrum A | (β p : ℤ) < r} ∧
        IsCompact {p : PrimeSpectrum A | (β p : ℤ) < r}) := by
  classical
  obtain ⟨_, _, _, _⟩ := hbounded
  obtain ⟨a, c, b, M, N, hdim⟩ := finiteFreeComplex_fibre_rank_formula A K hfree i
  let β : PrimeSpectrum A → ℕ := fun p ↦ Module.finrank p.asIdeal.ResidueField
    ((((ModuleCat.extendScalars.{u, u, max u v}
      (algebraMap A p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology i)
  have hlevels (r : ℤ) : ∃ s : Finset A,
      {p : PrimeSpectrum A | (β p : ℤ) < r} =
        ⋃ f ∈ (s : Set A), (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
    let U : ℕ × ℕ → Set (PrimeSpectrum A) := fun q ↦
      {p | q.1 ≤ (M.map (algebraMap A p.asIdeal.ResidueField)).rank} ∩
      {p | q.2 ≤ (N.map (algebraMap A p.asIdeal.ResidueField)).rank}
    let t := ((Finset.range (c + 1)) ×ˢ (Finset.range (c + 1))).filter
      (fun q : ℕ × ℕ ↦ (c : ℤ) < r + q.1 + q.2)
    have hU (q : ℕ × ℕ) : ∃ s : Finset A,
        U q = ⋃ f ∈ (s : Set A),
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
      obtain ⟨s, hs⟩ := matrix_rank_locus A M q.1
      obtain ⟨t, ht⟩ := matrix_rank_locus A N q.2
      dsimp only [U]
      rw [hs, ht]
      exact principal_union_inter A s t
    obtain ⟨s, hs⟩ := principal_finite_union A t U hU
    refine ⟨s, ?_⟩
    rw [← hs]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, t, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range, U, Set.mem_inter_iff]
    have hd := hdim p
    change β p + _ + _ = c at hd
    constructor
    · intro hp
      refine ⟨((M.map (algebraMap A p.asIdeal.ResidueField)).rank,
        (N.map (algebraMap A p.asIdeal.ResidueField)).rank), ?_, le_rfl, le_rfl⟩
      dsimp only
      omega
    · rintro ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxy⟩, hM, hN⟩
      omega
  have hopencompact (r : ℤ) : IsOpen {p : PrimeSpectrum A | (β p : ℤ) < r} ∧
      IsCompact {p : PrimeSpectrum A | (β p : ℤ) < r} := by
    obtain ⟨s, hs⟩ := hlevels r
    rw [hs]
    exact ⟨isOpen_iUnion fun f ↦ isOpen_iUnion fun _ ↦ (PrimeSpectrum.basicOpen f).isOpen,
      s.finite_toSet.isCompact_biUnion fun f _ ↦ PrimeSpectrum.isCompact_basicOpen f⟩
  refine ⟨β, fun _ ↦ rfl, ?_, hlevels, hopencompact⟩
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro r
  convert (hopencompact (r : ℤ)).1 using 1
  ext p
  simp

end ModuleCat
