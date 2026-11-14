import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqRefine
import Langlands.AbelianScheme.StructureCohomologyKunnethDimension
import Langlands.LinearAlgebra.BoundedExteriorSquareCoproduct
import Langlands.AlgebraicGeometry.Picard.FieldH2ExteriorCoproductComparisonStatement

/-!
# Assembling the degree-two comparison for abelian varieties

For an abelian scheme `A` over a field, this module defines the comparison map
`degreeTwoMap A : H²(A) × (H¹(A) ⊗ H¹(A)) × H²(A) ⟶ H²(A ⨯ A)` built from the canonical
pullbacks along the projections and the mixed cup product. It proves that this map, once
injective, is bijective, and that the mixed cup product does not depend on the chosen product
cover. It then reduces `FieldH2ExteriorCoproductComparisonStatement` to three inputs: injectivity
of `degreeTwoMap A`, alternation of `cupA A`, and a bounded creation-contraction family on
`H*(A, 𝒪)` whose degree-one creations are cup products
(`fieldH2ExteriorCoproductComparison_of_inputs`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  (structureCohomology)

open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

section TensorTwo

variable (K : Type*) [CommRing K] (H : Type*) [AddCommGroup H] [Module K H]

/-- The second tensor power is the binary tensor product: `⨂² H ≃ H ⊗ H`. -/
def tensorPowerTwoEquiv : ⨂[K]^2 H ≃ₗ[K] H ⊗[K] H :=
  (TensorPower.mulEquiv (R := K) (M := H) (n := 1) (m := 1)).symm.trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv 0)
      (PiTensorProduct.subsingletonEquiv 0))

variable {K H}

@[simp]
lemma tensorPowerTwoEquiv_tprod (v : Fin 2 → H) :
    tensorPowerTwoEquiv K H (PiTensorProduct.tprod K v) = v 0 ⊗ₜ v 1 := by
  simp only [tensorPowerTwoEquiv, LinearEquiv.trans_apply, TensorPower.mulEquiv,
    LinearEquiv.trans_symm, PiTensorProduct.reindex_symm]
  erw [PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquiv_symm_apply,
    TensorProduct.congr_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

/-- The antisymmetrization of `v 0 ∧ v 1` is `v 0 ⊗ v 1 - v 1 ⊗ v 0`. -/
lemma tensorPowerTwoEquiv_toTensorPower_ιMulti (v : Fin 2 → H) :
    tensorPowerTwoEquiv K H (exteriorPower.toTensorPower K H 2 (exteriorPower.ιMulti K 2 v)) =
      v 0 ⊗ₜ v 1 - v 1 ⊗ₜ v 0 := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [exteriorPower.toTensorPower_apply_ιMulti, map_sum, huniv,
    Finset.sum_pair (by decide)]
  simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1),
    Units.neg_smul, map_neg, tensorPowerTwoEquiv_tprod, Equiv.Perm.one_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, sub_eq_add_neg]

end TensorTwo

section Abelian

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- **Surjectivity from injectivity in degree two, binary-tensor form.** Any injective `K`-linear
map `H²(A) × (H¹(A) ⊗ H¹(A)) × H²(A) ⟶ H²(A ⨯ A)` is bijective, by the dimension count. -/
theorem bijective_of_injective_degreeTwo_tensor
    (Φ : (structureCohomology A.X 2 ×
      (structureCohomology A.X 1 ⊗[K] structureCohomology A.X 1) ×
      structureCohomology A.X 2) →ₗ[K] structureCohomology (A.X ⨯ A.X) 2)
    (hΦ : Function.Injective Φ) : Function.Bijective Φ := by
  have h : Module.finrank K (structureCohomology A.X 2 ×
      (structureCohomology A.X 1 ⊗[K] structureCohomology A.X 1) ×
      structureCohomology A.X 2) = Module.finrank K (structureCohomology (A.X ⨯ A.X) 2) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_tensorProduct,
      finrank_structureCohomology_prod_two]
    ring
  exact ⟨hΦ, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mp hΦ⟩

/-- The linear equivalence given by an injective binary-tensor degree-two comparison map. -/
def degreeTwoTensorEquivOfInjective
    (Φ : (structureCohomology A.X 2 ×
      (structureCohomology A.X 1 ⊗[K] structureCohomology A.X 1) ×
      structureCohomology A.X 2) →ₗ[K] structureCohomology (A.X ⨯ A.X) 2)
    (hΦ : Function.Injective Φ) :
    (structureCohomology A.X 2 × (structureCohomology A.X 1 ⊗[K] structureCohomology A.X 1) ×
      structureCohomology A.X 2) ≃ₗ[K] structureCohomology (A.X ⨯ A.X) 2 :=
  LinearEquiv.ofBijective Φ (bijective_of_injective_degreeTwo_tensor A Φ hΦ)

@[simp]
lemma degreeTwoTensorEquivOfInjective_apply
    (Φ : (structureCohomology A.X 2 ×
      (structureCohomology A.X 1 ⊗[K] structureCohomology A.X 1) ×
      structureCohomology A.X 2) →ₗ[K] structureCohomology (A.X ⨯ A.X) 2)
    (hΦ : Function.Injective Φ) (z) : degreeTwoTensorEquivOfInjective A Φ hΦ z = Φ z := rfl

/-- The cover `p₁⁻¹ U a ⊓ p₂⁻¹ U b` of `A ⨯ A` by products of members of the chosen cover. -/
abbrev mixedCover : coverIdx A × coverIdx A → (A.X ⨯ A.X).left.Opens :=
  prodCover (prod.fst : A.X ⨯ A.X ⟶ A.X).left (prod.snd : A.X ⨯ A.X ⟶ A.X).left
    (cover A) (cover A)

lemma productCover_le_mixedCover (j : (coverIdx A × coverIdx A) × coverIdx A) :
    productCover A j ≤ mixedCover A j.1 :=
  inf_le_left

lemma mixedCover_top : ⨆ j, mixedCover A j = ⊤ :=
  top_le_iff.mp ((productCover_top A).symm.le.trans
    (iSup_le fun j => (productCover_le_mixedCover A j).trans (le_iSup (mixedCover A) j.1)))

lemma mixedCover_affine (j : coverIdx A × coverIdx A) : IsAffineOpen (mixedCover A j) :=
  isAffineOpen_prodOpen (isPullback_prod A) (cover_affine A _) (cover_affine A _)

/-- **Cover independence for `cupP`.** The cup product on `H¹(A ⨯ A, 𝒪)` computed on
`productCover A` agrees with the one computed on the coarser cover `mixedCover A`. -/
theorem cupP_eq_mixedCover (x y) :
    cupP A x y = AllSeq.cupCanonical (A.X ⨯ A.X).hom (mixedCover A) (mixedCover_top A)
      (mixedCover_affine A) x y :=
  AllSeq.cupCanonical_refine (A.X ⨯ A.X).hom (mixedCover A) (productCover A) Prod.fst
    (productCover_le_mixedCover A) (mixedCover_top A) (productCover_top A)
    (mixedCover_affine A) (productCover_affine A) x y

/-- The mixed cup tensor map `H¹(A) ⊗ H¹(A) ⟶ H²(A ⨯ A)`, `x ⊗ y ↦ p₁^* x ∪ p₂^* y`. -/
def mixedTensorA :
    structureCohomology A.X 1 ⊗[K] structureCohomology A.X 1 →ₗ[K]
      structureCohomology (A.X ⨯ A.X) 2 :=
  TensorProduct.lift ((cupP A).compl₁₂ (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1)
    (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1))

lemma mixedTensorA_tmul (x y) :
    mixedTensorA A (x ⊗ₜ y) = cupP A (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 x)
      (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 y) := rfl

/-- On pure tensors, `mixedTensorA` is the cup product computed on `mixedCover A`. -/
lemma mixedTensorA_tmul_eq_mixedCover (x y) :
    mixedTensorA A (x ⊗ₜ y) = AllSeq.cupCanonical (A.X ⨯ A.X).hom (mixedCover A)
      (mixedCover_top A) (mixedCover_affine A)
        (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 x)
        (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 y) := by
  rw [mixedTensorA_tmul, cupP_eq_mixedCover]

/-- The degree-two comparison map `(a, t, b) ↦ p₁^* a + mixedTensorA t + p₂^* b`. -/
def degreeTwoMap :
    (structureCohomology A.X 2 × (structureCohomology A.X 1 ⊗[K] structureCohomology A.X 1) ×
      structureCohomology A.X 2) →ₗ[K] structureCohomology (A.X ⨯ A.X) 2 :=
  (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2).coprod
    ((mixedTensorA A).coprod (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2))

lemma degreeTwoMap_apply (a t b) :
    degreeTwoMap A (a, t, b) = pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 a +
      (mixedTensorA A t + pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2 b) := rfl

end Abelian

section Assembly

open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The cup product `H¹(A) × H¹(A) ⟶ H²(A)` as an alternating map, given `x ∪ x = 0`. -/
def cupAlt (halt : ∀ x, cupA A x x = 0) :
    (structureCohomology A.X 1) [⋀^Fin 2]→ₗ[K] structureCohomology A.X 2 where
  toFun v := cupA A (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [map_add, LinearMap.add_apply]
  map_update_smul' v i c x := by
    fin_cases i <;> simp [map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change cupA A (v 0) (v 1) = 0
      rw [show v 0 = v 1 from hv]
      exact halt _
    · change cupA A (v 0) (v 1) = 0
      rw [show v 1 = v 0 from hv]
      exact halt _
    · exact absurd rfl hij

lemma cupAlt_apply (halt : ∀ x, cupA A x x = 0) (v : Fin 2 → structureCohomology A.X 1) :
    cupAlt A halt v = cupA A (v 0) (v 1) := rfl

/-- **Conditional assembly of the degree-two comparison.** Suppose that

* `degreeTwoMap A` (`(a, t, b) ↦ p₁^* a + (p₁^* ∪ p₂^*)(t) + p₂^* b`) is injective,
* the cup product `cupA` on `H¹(A, 𝒪)` is alternating, and
* `Hⁿ(A, 𝒪)` carries a bounded creation-contraction family whose degree-one creation operators
  are cup products with vectors `v i`.

Then the conclusion of `FieldH2ExteriorCoproductComparisonStatement` holds for `A`. -/
theorem exists_comparison_of_inputs
    (hinj : Function.Injective (degreeTwoMap A))
    (halt : ∀ x, cupA A x x = 0)
    {I : Type*} [Fintype I] [DecidableEq I]
    (c : ∀ (_ : I) (n : ℕ), structureCohomology A.X n →ₗ[K] structureCohomology A.X (n + 1))
    (d : ∀ (_ : I) (n : ℕ), structureCohomology A.X (n + 1) →ₗ[K] structureCohomology A.X n)
    (hrel : ∀ i j n, (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
      if i = j then LinearMap.id else 0)
    (hbound : ∀ n, Fintype.card I < n → Subsingleton (structureCohomology A.X n))
    (v : I → structureCohomology A.X 1)
    (hcup : ∀ i x, c i 1 x = cupA A (v i) x) :
    ∃ (e : structureCohomology A.X 2 ≃ₗ[K] ⋀[K]^2 (structureCohomology A.X 1))
      (κ : structureCohomology (A.X ⨯ A.X) 2 ≃ₗ[K]
        structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
          structureCohomology A.X 2),
      (∀ x, κ (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 x) = (x, 0, 0)) ∧
      (∀ x, κ (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2 x) = (0, 0, x)) ∧
      (∀ x, κ (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * (prod.snd : A.X ⨯ A.X ⟶ A.X)) 2 x) =
        (x, exteriorPower.toTensorPower K _ 2 (e x), x)) := by
  let D := degreeTwoTensorEquivOfInjective A (degreeTwoMap A) hinj
  let κ : structureCohomology (A.X ⨯ A.X) 2 ≃ₗ[K]
      structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
        structureCohomology A.X 2 :=
    D.symm.trans (LinearEquiv.prodCongr (LinearEquiv.refl K _)
      (LinearEquiv.prodCongr (tensorPowerTwoEquiv K _).symm (LinearEquiv.refl K _)))
  have hκ : ∀ y a t b, y = degreeTwoMap A (a, tensorPowerTwoEquiv K _ t, b) →
      κ y = (a, t, b) := by
    intro y a t b h
    have hD : D.symm y = (a, tensorPowerTwoEquiv K _ t, b) := by
      rw [LinearEquiv.symm_apply_eq, h]
      rfl
    change LinearEquiv.prodCongr (LinearEquiv.refl K _)
      (LinearEquiv.prodCongr (tensorPowerTwoEquiv K _).symm (LinearEquiv.refl K _))
        (D.symm y) = _
    rw [hD]
    simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply]
  obtain ⟨e, h1, h2, hm⟩ := Langlands.LinearAlgebra.BoundedExteriorSquareCoproduct.exists_comparison
    (M := fun n => (structureCohomology A.X n : Type u)) c d hrel hbound (cupAlt A halt) v
    hcup κ (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2)
    (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2)
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * (prod.snd : A.X ⨯ A.X ⟶ A.X)) 2)
    (fun w => hκ _ _ _ _ (by
      rw [map_zero, degreeTwoMap_apply, map_zero, map_zero, add_zero, add_zero]))
    (fun w => hκ _ _ _ _ (by
      rw [map_zero, degreeTwoMap_apply, map_zero, map_zero, zero_add, zero_add]))
    (fun w => hκ _ _ _ _ (by
      rw [tensorPowerTwoEquiv_toTensorPower_ιMulti, degreeTwoMap_apply, map_sub,
        mixedTensorA_tmul, mixedTensorA_tmul, cupAlt_apply, pullStructure_mul_cupA]
      abel))
  exact ⟨e, κ, h1, h2, hm⟩

/-- **The target from the remaining inputs.** If, for every abelian scheme `A` over a field,
`degreeTwoMap A` is injective, `cupA A` is alternating, and `Hⁿ(A, 𝒪)` carries a bounded
creation-contraction family whose degree-one creations are cup products, then
`FieldH2ExteriorCoproductComparisonStatement` holds. -/
theorem fieldH2ExteriorCoproductComparison_of_inputs
    (h : ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
      Function.Injective (degreeTwoMap A) ∧ (∀ x, cupA A x x = 0) ∧
      ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
        (c : ∀ (_ : I) (n : ℕ),
          structureCohomology A.X n →ₗ[K] structureCohomology A.X (n + 1))
        (d : ∀ (_ : I) (n : ℕ),
          structureCohomology A.X (n + 1) →ₗ[K] structureCohomology A.X n),
        (∀ i j n, (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
          if i = j then LinearMap.id else 0) ∧
        (∀ n, Fintype.card I < n → Subsingleton (structureCohomology A.X n)) ∧
        ∃ v : I → structureCohomology A.X 1, ∀ i x, c i 1 x = cupA A (v i) x) :
    FieldH2ExteriorCoproductComparisonStatement.{u} := by
  intro K _ A
  obtain ⟨hinj, halt, I, _, _, c, d, hrel, hbound, v, hcup⟩ := h K A
  exact exists_comparison_of_inputs A hinj halt c d hrel hbound v hcup

end Assembly

end Langlands.AbelianScheme
