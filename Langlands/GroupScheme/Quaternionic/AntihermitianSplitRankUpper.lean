import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankUpper
import Langlands.GroupScheme.Quaternionic.SymplecticPoints
import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Langlands.GroupScheme.FactoredKernel
import Mathlib.Algebra.Order.Group.PiLex

/-!
# Upper bound for the split rank of the symplectic group of a form

Let `σ` be an involution of the first kind of a central division algebra `D` over a field
`K`, and `H ∈ M_m(D)` invertible. For a closed split torus `𝔾ₘ^I → σ.symplecticGroup H`,
the inverse of the universal torus point is `∑ₐ Xᵃ ⊗ eₐ`, where the `eₐ` are nonzero
orthogonal idempotents of `M_m(D)` adding up to `1`, indexed by the weights `a ∈ ℤ^I`, and
the weights generate `ℤ^I`. The isometry equation gives `eₐ H ᵗe_b^σ = 0` unless
`a + b = 0`; hence the weights are symmetric, and the weights that are positive for a
lexicographic order give a totally isotropic subspace of dimension at least `|I|`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.AntihermitianSplitRank

set_option backward.isDefEq.respectTransparency false

open Quaternionic

/-! ### Lattices -/

section Lattice

variable {I : Type u} [Fintype I]

/-- A finite generating set of `ℤ^I` has at least `|I|` elements. -/
theorem card_le_card_of_closure_eq_top (P : Finset (I → ℤ))
    (hP : AddSubgroup.closure (P : Set (I → ℤ)) = ⊤) : Fintype.card I ≤ P.card := by
  have hspan : Submodule.span ℤ (P : Set (I → ℤ)) = ⊤ := by
    apply Submodule.toAddSubgroup_injective
    rw [Submodule.span_int_eq_addSubgroupClosure, hP, Submodule.top_toAddSubgroup]
  have h := finrank_span_finset_le_card (R := ℤ) P
  rw [Set.finrank, hspan, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- A finite symmetric generating set of `ℤ^I` contains a subset of at least `|I|` elements,
no two of which (equal or not) add up to zero: its positive elements for a lexicographic
order. -/
theorem exists_positive_half (S : Finset (I → ℤ)) (hS : ∀ a ∈ S, -a ∈ S)
    (hcl : AddSubgroup.closure (S : Set (I → ℤ)) = ⊤) :
    ∃ P ⊆ S, (∀ a ∈ P, ∀ b ∈ P, a + b ≠ 0) ∧ Fintype.card I ≤ P.card := by
  classical
  let _ : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let P := S.filter fun a => 0 < toLex a
  refine ⟨P, Finset.filter_subset _ _, ?_, ?_⟩
  · intro a ha b hb hab
    have h1 : 0 < toLex a := (Finset.mem_filter.1 ha).2
    have h2 : 0 < toLex b := (Finset.mem_filter.1 hb).2
    have h3 := add_pos h1 h2
    rw [← toLex_add, hab, toLex_zero] at h3
    exact lt_irrefl _ h3
  · apply card_le_card_of_closure_eq_top
    rw [eq_top_iff, ← hcl, AddSubgroup.closure_le]
    intro a ha
    rcases lt_trichotomy (toLex a) 0 with h | h | h
    · have hmem : -a ∈ P := by
        refine Finset.mem_filter.2 ⟨hS a ha, ?_⟩
        rw [toLex_neg]
        exact neg_pos.2 h
      have h' := AddSubgroup.neg_mem _ (AddSubgroup.subset_closure hmem)
      rwa [neg_neg] at h'
    · have h0 : a = 0 := by
        rw [← toLex_zero] at h
        exact toLex.injective h
      rw [h0]
      exact AddSubgroup.zero_mem _
    · exact AddSubgroup.subset_closure (Finset.mem_filter.2 ⟨ha, h⟩)

end Lattice

/-! ### Totally isotropic subspaces from orthogonal idempotents -/

section Isotropic

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-- The left `D`-subspace of row vectors fixed by right multiplication by `E`. -/
def fixedRows (E : Matrix n n D) : Submodule D (n → D) where
  carrier := {x | x ᵥ* E = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x ᵥ* E = x at hx
    change y ᵥ* E = y at hy
    change (x + y) ᵥ* E = x + y
    rw [Matrix.add_vecMul, hx, hy]
  smul_mem' := by
    intro c x hx
    change x ᵥ* E = x at hx
    change (c • x) ᵥ* E = c • x
    rw [Matrix.smul_vecMul, hx]

omit [DecidableEq n] in
theorem mem_fixedRows {E : Matrix n n D} {x : n → D} : x ∈ fixedRows E ↔ x ᵥ* E = x :=
  Iff.rfl

/-- If `E H ᵗE^σ = 0`, the rows fixed by `E` form a totally isotropic subspace. -/
theorem isTotallyIsotropic_fixedRows {H E : Matrix n n D} (hE : E * H * σ.matrix n E = 0) :
    σ.IsTotallyIsotropic H (fixedRows E) := by
  intro x hx y hy
  rw [← mem_fixedRows.1 hx, ← mem_fixedRows.1 hy, σ.sesqForm_vecMul, hE]
  simp [FirstKindInvolution.sesqForm]

/-- A finite family of nonzero orthogonal idempotents `eₐ` with `eₐ H ᵗe_b^σ = 0` for all
`a, b` in the family gives Witt index at least the size of the family. -/
theorem card_le_wittIndex_of_idempotents {Λ : Type*} [DecidableEq Λ] {H : Matrix n n D}
    (P : Finset Λ) (e : Λ → Matrix n n D)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (hne : ∀ a ∈ P, e a ≠ 0)
    (hiso : ∀ a ∈ P, ∀ b ∈ P, e a * H * σ.matrix n (e b) = 0) :
    P.card ≤ σ.wittIndex H := by
  classical
  set E := ∑ a ∈ P, e a with hEdef
  have hE : E * H * σ.matrix n E = 0 := by
    rw [hEdef, FirstKindInvolution.map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun b hb => hiso a ha b hb
  have hrow : ∀ a ∈ P, ∃ q, e a q ≠ 0 := by
    intro a ha
    by_contra h
    push Not at h
    exact hne a ha (Matrix.ext fun q j => by rw [h q]; rfl)
  choose q hq using hrow
  let v : P → (n → D) := fun a => e a.1 (q a.1 a.2)
  have hv : ∀ (a : P) (b : Λ), v a ᵥ* e b = if a.1 = b then v a else 0 := by
    intro a b
    have h1 : v a ᵥ* e b = (e a.1 * e b) (q a.1 a.2) := by
      ext j
      simp only [v, Matrix.vecMul, dotProduct, Matrix.mul_apply]
    rw [h1, hmul]
    split_ifs
    · rfl
    · rfl
  have hvW : ∀ a : P, v a ∈ fixedRows E := by
    intro a
    rw [mem_fixedRows, hEdef, Matrix.vecMul_sum]
    simp_rw [hv]
    rw [Finset.sum_ite_eq]
    exact ite_eq_left a.2
  have hli : LinearIndependent D v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have h := congrArg (fun x => x ᵥ* e a.1) hg
    simp only [Matrix.sum_vecMul, Matrix.smul_vecMul, hv, Matrix.zero_vecMul] at h
    rw [Finset.sum_eq_single a] at h
    · rw [ite_eq_left rfl] at h
      exact (smul_eq_zero.1 h).resolve_right (hq a.1 a.2)
    · intro b _ hb
      rw [ite_eq_right (fun h' => hb (Subtype.ext h')), smul_zero]
    · intro h'
      exact absurd (Finset.mem_univ a) h'
  let w : P → fixedRows E := fun a => ⟨v a, hvW a⟩
  have hliw : LinearIndependent D w := LinearIndependent.of_comp (fixedRows E).subtype hli
  have h1 := hliw.fintype_card_le_finrank
  rw [Fintype.card_coe] at h1
  exact h1.trans (σ.finrank_le_wittIndex (isTotallyIsotropic_fixedRows σ hE))

end Isotropic

/-! ### Affine points of the unitary group -/

section Affine

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n D)

/-- An affine point of the unitary group, read as a unit `g` of `R ⊗ M_n(D)`, satisfies
`g (1 ⊗ H) ᵗg^σ = 1 ⊗ H`. -/
theorem affinePoint_isometry (R : CommAlgCat.{u} (CommRingCat.of K))
    (p : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (σ.unitaryGroup H).X) :
    ((FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R
        (p ≫ (σ.unitaryGroupι H).hom.hom) : (R ⊗[K] Matrix n n D)ˣ) : R ⊗[K] Matrix n n D) *
        ((1 : R) ⊗ₜ[K] H) *
        (σ.matrix n).baseChange R
          (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R
            (p ≫ (σ.unitaryGroupι H).hom.hom) : R ⊗[K] Matrix n n D) =
      (1 : R) ⊗ₜ[K] H := by
  let b := Module.finBasis K (Matrix n n D)
  let x := p ≫ (σ.unitaryGroupι H).hom.hom
  have hx := (σ.mem_range_unitaryGroupι_iff H x).mp (SubgroupFunctor.mem_range.mpr ⟨p, rfl⟩)
  let f := (Corepresented.affineSectionsIso R).hom.hom
  have hc := Corepresented.map_affineSectionsIso_pointsEquiv
    (FiniteAlgebraUnits.functor K (Matrix n n D)) (FiniteAlgebraUnits.corepresentableBy b) R x
  change Units.map (Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n D))).toMonoidHom
    (FiniteAlgebraUnits.pointsEquiv b _ x) =
      FiniteAlgebraUnits.affinePointsEquiv b R x at hc
  have hcval := congrArg Units.val hc
  change Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n D))
    (FiniteAlgebraUnits.pointsEquiv b _ x : _) =
      (FiniteAlgebraUnits.affinePointsEquiv b R x : _) at hcval
  have hh := congrArg (Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n D))) hx
  rw [_root_.map_mul, _root_.map_mul, FirstKindInvolution.map_baseChange, hcval,
    Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.id_apply] at hh
  exact hh

end Affine

/-! ### The weight idempotents of a split torus of the symplectic group -/

section Weights

open SplitTorusRepresentationWeights CentralSimpleUnits MatrixNormOneSplitRank

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (σ : FirstKindInvolution K D) {m : ℕ} [NeZero m]
  (H : Matrix (Fin m) (Fin m) D)

/-- The symplectic group of `H` maps to the reduced-norm-one group of `M_m(D)`. -/
def toNormOne : σ.symplecticGroup H ⟶ normOne K (Matrix (Fin m) (Fin m) D) :=
  FactoredKernel.map (σ.unitaryGroupι H ≫ reducedNormHom K (Matrix (Fin m) (Fin m) D))
    (σ.unitaryGroupι H) (reducedNormHom K (Matrix (Fin m) (Fin m) D)) rfl

theorem toNormOne_comp :
    toNormOne σ H ≫ normOneι K (Matrix (Fin m) (Fin m) D) = σ.symplecticAmbientι H :=
  FactoredKernel.map_comp _ _ _ _

variable {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.symplecticGroup H)

/-- The coefficient algebra `K[ℤ^I]` of the universal torus point. -/
local notation "R'" => AddMonoidAlgebra K (I → ℤ)

/-- The matrix algebra. -/
local notation "A" => Matrix (Fin m) (Fin m) D

/-- The inverse-right-regular representation of the unit group of `M_m(D)`. -/
local notation "ρ" => FiniteAlgebraUnits.rightRegularRepresentation (Module.finBasis K A)

/-- The base-changed conjugate transpose on `K[ℤ^I] ⊗ M_m(D)`. -/
local notation "τ" => FirstKindInvolution.baseChange (FirstKindInvolution.matrix σ (Fin m)) R'

/-- The torus, as a torus of the reduced-norm-one group. -/
abbrev normOneTorus : splitTorus (Spec (CommRingCat.of K)) I ⟶ normOne K A :=
  i ≫ toNormOne σ H

omit [DecidableEq I] in
theorem normOneTorus_comp :
    normOneTorus σ H i ≫ normOneι K A = i ≫ σ.symplecticAmbientι H := by
  rw [normOneTorus, Category.assoc, toNormOne_comp]

/-- The universal torus point is an isometry of `H`. -/
theorem universalUnit_isometry :
    ((universalUnit (normOneTorus σ H i) : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) * ((1 : R') ⊗ₜ[K] H) *
        τ (universalUnit (normOneTorus σ H i) : R' ⊗[K] A) =
      (1 : R') ⊗ₜ[K] H := by
  rw [universalUnit_eq]
  have e : (normOneTorus σ H i ≫ normOneι K A).hom.hom =
      (i ≫ σ.symplecticGroupι H).hom.hom ≫ (σ.unitaryGroupι H).hom.hom := by
    rw [normOneTorus_comp, FirstKindInvolution.symplecticAmbientι, ← Category.assoc,
      Grp.comp_hom_hom]
  rw [e, ← Category.assoc]
  exact affinePoint_isometry σ H _ _

/-- So is its inverse. -/
theorem universalUnit_inv_isometry :
    (((universalUnit (normOneTorus σ H i))⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) *
        ((1 : R') ⊗ₜ[K] H) *
        τ (((universalUnit (normOneTorus σ H i))⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) =
      (1 : R') ⊗ₜ[K] H := by
  set g := universalUnit (normOneTorus σ H i)
  have hg := universalUnit_isometry σ H i
  have hτ : τ (g : R' ⊗[K] A) * τ ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) = 1 := by
    rw [← FirstKindInvolution.map_mul, Units.inv_mul, FirstKindInvolution.map_one]
  calc (((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A)) * ((1 : R') ⊗ₜ[K] H) *
          τ ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A)
        = ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) *
            ((g : R' ⊗[K] A) * ((1 : R') ⊗ₜ[K] H) * τ (g : R' ⊗[K] A)) *
            τ ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) := by rw [hg]
      _ = (((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) * (g : R' ⊗[K] A)) * ((1 : R') ⊗ₜ[K] H) *
            (τ (g : R' ⊗[K] A) * τ ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A)) := by
          simp only [mul_assoc]
      _ = (1 : R') ⊗ₜ[K] H := by rw [Units.inv_mul, hτ, one_mul, mul_one]

/-- Multiplying the inverse universal point on the left by `1 ⊗ e_c` isolates `Xᶜ ⊗ e_c`. -/
theorem one_tmul_weightElement_mul_inv (c : I → ℤ) :
    ((1 : R') ⊗ₜ[K] weightElement (normOneTorus σ H i) c) *
        (((universalUnit (normOneTorus σ H i))⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) =
      AddMonoidAlgebra.single c (1 : K) ⊗ₜ[K] weightElement (normOneTorus σ H i) c := by
  rw [universalUnit_inv_eq_sum, Finset.mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, weightElement_mul]
  by_cases hc : c ∈ weightSupport ρ I (normOneTorus σ H i ≫ normOneι K A)
  · rw [Finset.sum_eq_single c]
    · rw [ite_eq_left rfl]
    · intro b _ hb
      rw [ite_eq_right (Ne.symm hb), TensorProduct.tmul_zero]
    · intro h
      exact absurd hc h
  · rw [weightElement_eq_zero _ hc, TensorProduct.tmul_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs <;> exact TensorProduct.tmul_zero _ _

/-- Dually, multiplying `ᵗ(g⁻¹)^σ` on the right by `1 ⊗ ᵗe_d^σ` isolates `X^d ⊗ ᵗe_d^σ`. -/
theorem matrix_inv_mul_one_tmul (d : I → ℤ) :
    τ (((universalUnit (normOneTorus σ H i))⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) *
        ((1 : R') ⊗ₜ[K] σ.matrix (Fin m) (weightElement (normOneTorus σ H i) d)) =
      AddMonoidAlgebra.single d (1 : K) ⊗ₜ[K]
        σ.matrix (Fin m) (weightElement (normOneTorus σ H i) d) := by
  have h := congrArg τ (one_tmul_weightElement_mul_inv σ H i d)
  rw [FirstKindInvolution.map_mul, FirstKindInvolution.baseChange_tmul,
    FirstKindInvolution.baseChange_tmul] at h
  exact h

/-- **Orthogonality of weight spaces.** `e_c H ᵗe_d^σ = 0` unless `c + d = 0`. -/
theorem weightElement_mul_mul_eq_zero {c d : I → ℤ} (hcd : c + d ≠ 0) :
    weightElement (normOneTorus σ H i) c * H *
        σ.matrix (Fin m) (weightElement (normOneTorus σ H i) d) = 0 := by
  set g := universalUnit (normOneTorus σ H i)
  set ec := weightElement (normOneTorus σ H i) c
  set ed := weightElement (normOneTorus σ H i) d
  have hinv := universalUnit_inv_isometry σ H i
  have key : ((1 : R') ⊗ₜ[K] ec * ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A)) * ((1 : R') ⊗ₜ[K] H) *
      (τ ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) * ((1 : R') ⊗ₜ[K] σ.matrix (Fin m) ed)) =
      ((1 : R') ⊗ₜ[K] ec) * ((1 : R') ⊗ₜ[K] H) * ((1 : R') ⊗ₜ[K] σ.matrix (Fin m) ed) := by
    calc _ = ((1 : R') ⊗ₜ[K] ec) * (((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A) * ((1 : R') ⊗ₜ[K] H) *
            τ ((g⁻¹ : (R' ⊗[K] A)ˣ) : R' ⊗[K] A)) * ((1 : R') ⊗ₜ[K] σ.matrix (Fin m) ed) := by
          simp only [mul_assoc]
      _ = _ := by rw [hinv]
  rw [one_tmul_weightElement_mul_inv, matrix_inv_mul_one_tmul] at key
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    AddMonoidAlgebra.single_mul_single] at key
  have h2 := congrArg (coeffTensor (K := K) A (c + d)) key
  rw [coeffTensor_tmul, coeffTensor_tmul, AddMonoidAlgebra.one_def,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    Finsupp.single_apply, ite_eq_left rfl, ite_eq_right (Ne.symm hcd), one_smul, zero_smul] at h2
  exact h2

/-- **Symmetry of the weights.** -/
theorem neg_mem_weightSupport (hu : IsUnit H) {c : I → ℤ}
    (hc : c ∈ weightSupport ρ I (normOneTorus σ H i ≫ normOneι K A)) :
    -c ∈ weightSupport ρ I (normOneTorus σ H i ≫ normOneι K A) := by
  by_contra hneg
  apply weightElement_ne_zero (normOneTorus σ H i) hc
  have h1 : weightElement (normOneTorus σ H i) c * H = 0 := by
    calc weightElement (normOneTorus σ H i) c * H =
          weightElement (normOneTorus σ H i) c * H * σ.matrix (Fin m) 1 := by
          rw [FirstKindInvolution.map_one, mul_one]
      _ = ∑ d ∈ weightSupport ρ I (normOneTorus σ H i ≫ normOneι K A),
            weightElement (normOneTorus σ H i) c * H *
              σ.matrix (Fin m) (weightElement (normOneTorus σ H i) d) := by
          rw [← sum_weightElement (normOneTorus σ H i), FirstKindInvolution.map_sum,
            Finset.mul_sum]
      _ = 0 := by
          refine Finset.sum_eq_zero fun d hd => weightElement_mul_mul_eq_zero σ H i ?_
          intro hcd
          apply hneg
          have : d = -c := eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact hcd)
          rwa [← this]
  calc weightElement (normOneTorus σ H i) c =
        weightElement (normOneTorus σ H i) c * H * ((hu.unit⁻¹ : Aˣ) : A) := by
        rw [mul_assoc, hu.mul_val_inv, mul_one]
    _ = 0 := by rw [h1, zero_mul]

/-- The weights generate `ℤ^I` when the torus is closed. -/
theorem closure_weightSupport_symplectic (hi : IsClosedSubgroup i) :
    AddSubgroup.closure
      (weightSupport ρ I (normOneTorus σ H i ≫ normOneι K A) : Set (I → ℤ)) = ⊤ := by
  have hmono : Mono ((normOneTorus σ H i ≫ normOneι K A).hom.hom ≫ (ρ).hom.hom).left := by
    rw [normOneTorus_comp]
    have : IsClosedImmersion i.hom.hom.left := hi
    have : IsClosedImmersion (σ.symplecticAmbientι H).hom.hom.left :=
      σ.isClosedSubgroup_symplecticAmbientι H
    have h1 : Mono i.hom.hom.left := inferInstance
    have h2 : Mono (σ.symplecticAmbientι H).hom.hom.left := inferInstance
    have h3 : Mono (ρ).hom.hom.left := inferInstance
    show Mono ((i.hom.hom.left ≫ (σ.symplecticAmbientι H).hom.hom.left) ≫ (ρ).hom.hom.left)
    exact mono_comp _ _
  have h := closure_weights_eq_top ρ I (normOneTorus σ H i ≫ normOneι K A) hmono
  have hs : {m : I → ℤ | weight ρ I (normOneTorus σ H i ≫ normOneι K A) m ≠ 0} =
      (weightSupport ρ I (normOneTorus σ H i ≫ normOneι K A) : Set (I → ℤ)) := by
    ext m
    exact (mem_weightSupport _ _ _ m).symm
  rwa [hs] at h

/-- **Upper bound.** A closed split torus `𝔾ₘ^I` of `σ.symplecticGroup H`, `H` invertible, has
`|I|` at most the Witt index of `H`. -/
theorem card_le_wittIndex (hu : IsUnit H) (hi : IsClosedSubgroup i) :
    Fintype.card I ≤ σ.wittIndex H := by
  classical
  obtain ⟨P, hPS, hP, hcard⟩ := exists_positive_half
    (weightSupport ρ I (normOneTorus σ H i ≫ normOneι K A))
    (fun a ha => neg_mem_weightSupport σ H i hu ha)
    (closure_weightSupport_symplectic σ H i hi)
  refine hcard.trans ?_
  exact card_le_wittIndex_of_idempotents σ P (weightElement (normOneTorus σ H i))
    (weightElement_mul (normOneTorus σ H i))
    (fun a ha => weightElement_ne_zero (normOneTorus σ H i) (hPS ha))
    (fun a ha b hb => weightElement_mul_mul_eq_zero σ H i (hP a ha b hb))

end Weights

section SplitRank

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (σ : FirstKindInvolution K D) {m : ℕ} [NeZero m]
  (H : Matrix (Fin m) (Fin m) D)

/-- **Upper bound for the split rank.** -/
theorem splitRank_le_wittIndex (hu : IsUnit H) :
    splitRank (σ.symplecticGroup H) ≤ (σ.wittIndex H : ℕ∞) := by
  refine iSup_le fun I => iSup_le fun hI => iSup_le fun i => iSup_le fun hi => ?_
  classical
  have := Fintype.ofFinite I
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast card_le_wittIndex σ H i hu hi

end SplitRank

end Langlands.GroupScheme.AntihermitianSplitRank
