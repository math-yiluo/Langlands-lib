import Langlands.GroupScheme.EvenOrthogonalForm.AutomorphismCocycle

/-! # The similitudes of the Galois twists form a cocycle up to scalars

Let `ψ_σ` be the Galois twists of local isomorphisms `φ` from `H` to the split `SO_{2n}`
along `Spec N ⟶ Spec K`, and suppose `ψ_σ` is conjugation by an invertible matrix `g_σ`.
Since `ψ_{σσ'}(s) = ψ_{σ'}(s ≫ σ*) ∘ ψ_σ(s)`, the matrix `g_{σσ'}⁻¹ σ(g_{σ'}) g_σ` commutes
with the constant unipotent points of `SO_{2n}`, hence is a scalar when `n ≥ 3`. Consequently
`θ_σ(x) = g_σ⁻¹ σ(x) g_σ` satisfies `θ_σ ∘ θ_{σ'} = θ_{σσ'}` on all matrices.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.EvenOrthogonalForm

open OrthogonalMatrix
open SpecialLinearInnerForm (pointScalars pointScalars_comp_ringTestMap)

section MatrixAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] {l : Type} [Fintype l] [DecidableEq l]

omit [Fintype l] in
theorem altBasis_map (f : R →+* S) (i j : l) :
    (altBasis (R := R) i j).map f = altBasis i j := by
  ext a b
  simp only [altBasis, Matrix.map_apply, Matrix.sub_apply, Matrix.transpose_apply,
    Matrix.single_apply]
  split_ifs <;> simp

variable {m : Type} [Fintype m] [DecidableEq m]

/-- If two conjugations agree on `U` after an injective ring map, the quotient of the
conjugating matrices commutes with `U`. -/
theorem commute_of_conj_map_eq {F : Type*} [Field F] (κ : F →+* R)
    (hκ : Function.Injective κ) {A A' B B' U : Matrix m m F} (hA : A' * A = 1) (hB : B' * B = 1)
    (h : A.map κ * U.map κ * A'.map κ = B.map κ * (U.map κ * B'.map κ)) :
    (A' * B) * U = U * (A' * B) := by
  have h' : A * U * A' = B * U * B' := by
    apply Matrix.map_injective hκ
    simp only [Matrix.map_mul]
    rw [h, Matrix.mul_assoc]
  calc A' * B * U = A' * B * U * (B' * B) := by rw [hB, Matrix.mul_one]
    _ = A' * (B * U * B') * B := by simp only [Matrix.mul_assoc]
    _ = A' * (A * U * A') * B := by rw [h']
    _ = (A' * A) * U * (A' * B) := by simp only [Matrix.mul_assoc]
    _ = U * (A' * B) := by rw [hA, Matrix.one_mul]

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

omit [DecidableEq m] in
theorem map_mul_algEquiv (σ : F ≃ₐ[K] F) (P Q : Matrix m m F) :
    (P * Q).map σ = P.map σ * Q.map σ :=
  Matrix.map_mul (f := (σ : F →+* F))

omit [Fintype m] in
theorem map_one_algEquiv (σ : F ≃ₐ[K] F) : (1 : Matrix m m F).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

/-- A scalar cocycle of invertible matrices gives an action by twisted conjugation. -/
theorem twist_mul_of_scalar (g : (F ≃ₐ[K] F) → GL m F) (σ σ' : F ≃ₐ[K] F)
    (hc : ∃ c : F, (↑(g (σ * σ'))⁻¹ : Matrix m m F) *
        ((g σ' : Matrix m m F).map σ * (g σ : Matrix m m F)) = c • 1)
    (x : Matrix m m F) :
    (↑(g σ)⁻¹ : Matrix m m F) *
        ((↑(g σ')⁻¹ : Matrix m m F) * x.map σ' * (g σ' : Matrix m m F)).map σ *
          (g σ : Matrix m m F) =
      (↑(g (σ * σ'))⁻¹ : Matrix m m F) * x.map (σ * σ') * (g (σ * σ') : Matrix m m F) := by
  obtain ⟨c, hc⟩ := hc
  set A : Matrix m m F := (g (σ * σ') : Matrix m m F)
  set A' : Matrix m m F := (↑(g (σ * σ'))⁻¹ : Matrix m m F)
  set B : Matrix m m F := (g σ' : Matrix m m F).map σ * (g σ : Matrix m m F) with hBdef
  set B' : Matrix m m F := (↑(g σ)⁻¹ : Matrix m m F) * (↑(g σ')⁻¹ : Matrix m m F).map σ
    with hB'def
  have hAA' : A * A' = 1 := Units.mul_inv _
  have hB'B : B' * B = 1 := by
    have h1 : ((↑(g σ')⁻¹ : Matrix m m F) * (g σ' : Matrix m m F)).map σ = 1 := by
      rw [Units.inv_mul]
      exact map_one_algEquiv σ
    calc B' * B = (↑(g σ)⁻¹ : Matrix m m F) *
          (((↑(g σ')⁻¹ : Matrix m m F) * (g σ' : Matrix m m F)).map σ) *
            (g σ : Matrix m m F) := by
          rw [hB'def, hBdef, map_mul_algEquiv]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.inv_mul]
  have hB : B = c • A := by
    calc B = (A * A') * B := by rw [hAA', Matrix.one_mul]
      _ = A * (A' * B) := Matrix.mul_assoc _ _ _
      _ = c • A := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  have hX : (x.map σ').map σ = x.map (σ * σ') := by
    rw [Matrix.map_map]
    rfl
  have hL : (↑(g σ)⁻¹ : Matrix m m F) *
        ((↑(g σ')⁻¹ : Matrix m m F) * x.map σ' * (g σ' : Matrix m m F)).map σ *
          (g σ : Matrix m m F) = B' * x.map (σ * σ') * B := by
    rw [map_mul_algEquiv, map_mul_algEquiv, hX, hB'def, hBdef]
    simp only [Matrix.mul_assoc]
  rw [hL]
  have hcB : c • (B' * A) = 1 := by
    rw [← Matrix.mul_smul, ← hB, hB'B]
  calc B' * x.map (σ * σ') * B = B' * x.map (σ * σ') * (c • A) := by rw [hB]
    _ = B' * ((A * A') * x.map (σ * σ') * (c • A)) := by
        rw [hAA', Matrix.one_mul, Matrix.mul_assoc]
    _ = (c • (B' * A)) * (A' * x.map (σ * σ') * A) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = A' * x.map (σ * σ') * A := by rw [hcB, Matrix.one_mul]

end MatrixAlgebra

section Cocycle

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}

theorem sectionScalars_id_injective :
    Function.Injective (sectionScalars (𝟙 (ringTest K N))) := by
  have key : ∀ a : N, sectionScalars (𝟙 (ringTest K N)) a =
      (Scheme.ΓSpecIso (CommRingCat.of N)).inv.hom a := by
    intro a
    change (𝟙 (ringTest K N) : ringTest K N ⟶ ringTest K N).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of N)).inv.hom a) = _
    rw [Over.id_left, Scheme.Hom.id_appTop]
    rfl
  intro a b h
  rw [key, key] at h
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of N)).hom.hom h
  simpa using h'

/-- The matrix of a constant upper or lower unipotent point of the split `SO_{2n}`. -/
theorem exists_splitMatrix_upper (V : Over (Spec (CommRingCat.of K))) (i j : Fin n) :
    ∃ x : V ⟶ (splitGroup K n).X,
      splitMatrix x = SymplecticMatrix.upper (altBasis i j) := by
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.1
    (constantPoint_upper_mem (l := Fin n) V (isAlt_altBasis (R := K) i j))
  refine ⟨x, ?_⟩
  rw [splitMatrix, hx, pointsEquiv_constantPoint, coe_map]
  change (SymplecticMatrix.upper (altBasis i j)).map _ = _
  rw [SymplecticMatrix.map_upper, altBasis_map]

theorem exists_splitMatrix_lower (V : Over (Spec (CommRingCat.of K))) (i j : Fin n) :
    ∃ x : V ⟶ (splitGroup K n).X,
      splitMatrix x = SymplecticMatrix.lower (altBasis i j) := by
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.1
    (constantPoint_lower_mem (l := Fin n) V (isAlt_altBasis (R := K) i j))
  refine ⟨x, ?_⟩
  rw [splitMatrix, hx, pointsEquiv_constantPoint, coe_map]
  change (SymplecticMatrix.lower (altBasis i j)).map _ = _
  rw [SymplecticMatrix.map_lower, altBasis_map]

theorem exists_ne_ne (hn : 3 ≤ n) (i k : Fin n) : ∃ j, j ≠ i ∧ j ≠ k := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ ({i, k} : Finset (Fin n)) := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h1 : (Finset.univ : Finset (Fin n)) ⊆ {i, k} := fun j _ => h j
    have h2 := Finset.card_le_card h1
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 := Finset.card_insert_le i {k}
    rw [Finset.card_singleton] at h3
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  exact ⟨j, hj⟩

variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (φ : LocalGroupIso H (splitGroup K n) (ringTest K N))

/-- If every Galois twist is conjugation by `g_σ`, the matrices `g_σ` form a cocycle up to
scalars: `g_{σσ'}⁻¹ σ(g_{σ'}) g_σ` is a scalar matrix. -/
theorem exists_scalar_cocycle (hn : 3 ≤ n) (g : (N ≃ₐ[K] N) → GL (Fin n ⊕ Fin n) N)
    (hg : ∀ (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
      (x : V ⟶ (splitGroup K n).X),
      splitMatrix ((galoisTwist φ σ).toFun s x) =
        (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s) *
          splitMatrix x *
            (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s))
    (σ σ' : N ≃ₐ[K] N) :
    ∃ c : N, (↑(g (σ * σ'))⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
        ((g σ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map σ *
          (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)) = c • 1 := by
  have hinj : Function.Injective (sectionScalars (K := K) (𝟙 (ringTest K N))) := sectionScalars_id_injective
  have hs : sectionScalars (𝟙 (ringTest K N) ≫ ringTestMap K σ.toAlgHom) =
      (sectionScalars (K := K) (𝟙 (ringTest K N))).comp (σ : N →+* N) :=
    pointScalars_comp_ringTestMap _ σ
  have key : ∀ (U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)
      (x0 : ringTest K N ⟶ (splitGroup K n).X), splitMatrix x0 = U.map (sectionScalars (K := K) (𝟙 (ringTest K N))) →
      ((↑(g (σ * σ'))⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
        ((g σ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map σ *
          (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N))) * U =
      U * ((↑(g (σ * σ'))⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
        ((g σ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map σ *
          (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N))) := by
    intro U x0 hU
    have e1 := hg (σ * σ') (𝟙 (ringTest K N)) x0
    have e2 := hg σ' (𝟙 (ringTest K N) ≫ ringTestMap K σ.toAlgHom)
      ((galoisTwist φ σ).toFun (𝟙 (ringTest K N)) x0)
    have e3 := hg σ (𝟙 (ringTest K N)) x0
    have h := e1.symm.trans ((congrArg splitMatrix
      (galoisTwist_mul φ σ σ' (𝟙 (ringTest K N)) x0)).trans e2)
    rw [e3, hU, hs] at h
    apply commute_of_conj_map_eq (sectionScalars (K := K) (𝟙 (ringTest K N))) hinj (Units.inv_mul _) (B' := (↑(g σ)⁻¹ :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
        (↑(g σ')⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map σ)
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc
        ((↑(g σ')⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map σ),
        ← map_mul_algEquiv, Units.inv_mul, map_one_algEquiv, Matrix.one_mul, Units.inv_mul]
    · rw [h]
      simp only [Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]
      rfl
  have hl := exists_ne_ne hn
  have h0 : 0 < n := by omega
  refine ⟨_, eq_smul_one_of_commute hl ⟨0, h0⟩ _ (fun i j _ => ?_) (fun i j _ => ?_)⟩
  · obtain ⟨x0, hx0⟩ := exists_splitMatrix_upper (K := K) (ringTest K N) i j
    refine key _ x0 ?_
    rw [hx0, SymplecticMatrix.map_upper, altBasis_map]
  · obtain ⟨x0, hx0⟩ := exists_splitMatrix_lower (K := K) (ringTest K N) i j
    refine key _ x0 ?_
    rw [hx0, SymplecticMatrix.map_lower, altBasis_map]

/-- The similitude cocycle of a form of the split `SO_{2n}`, `n ≥ 3`, given the automorphism
theorem for the split `SO_{2n}`: similitudes `g_σ` whose conjugations are the Galois twists
of `φ` and whose twisted conjugations `x ↦ g_σ⁻¹ σ(x) g_σ` compose as a Galois action. -/
theorem exists_similitude_cocycle (hS : SpecialOrthogonalAutomorphismStatement.{u})
    (hn : 3 ≤ n) :
    ∃ g : (N ≃ₐ[K] N) → GL (Fin n ⊕ Fin n) N,
      (∀ σ, ∃ ν : Nˣ,
        IsAlt ((g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) * formMatrix (Fin n) N *
          (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)ᵀ -
            (ν : N) • formMatrix (Fin n) N)) ∧
      (∀ (σ σ' : N ≃ₐ[K] N) (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N),
        (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
            ((↑(g σ')⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) * x.map σ' *
              (g σ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)).map σ *
            (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) =
          (↑(g (σ * σ'))⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) * x.map (σ * σ') *
            (g (σ * σ') : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)) ∧
      (∀ (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
        (x : V ⟶ (splitGroup K n).X),
        splitMatrix ((galoisTwist φ σ).toFun s x) =
          (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s) *
            splitMatrix x *
              (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s)) := by
  choose g ν hsim hconj using fun σ : N ≃ₐ[K] N =>
    exists_similitude_conj hS (by omega : 2 ≤ n) (galoisTwist φ σ)
  exact ⟨g, fun σ => ⟨ν σ, hsim σ⟩,
    fun σ σ' x => twist_mul_of_scalar g σ σ' (exists_scalar_cocycle φ hn g hconj σ σ') x,
    hconj⟩

end Cocycle

end Langlands.GroupScheme.EvenOrthogonalForm
