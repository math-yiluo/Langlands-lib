import Langlands.GroupScheme.Reductive.LinearlyReductiveIntegral
import Langlands.GroupScheme.Reductive.LinearlyReductiveFieldExtensionStatement
import Langlands.GroupScheme.Descent.TensorCoordinates
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Lie.AffineCoordinates

/-! # Proof: linear reductivity is invariant under extension of the base field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearReductivity

open AffineLinearEmbedding
open Algebra.TensorProduct (includeLeft includeRight)

section BaseChange

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  {B : CommAlgCat.{u} (CommRingCat.of k)} (ψ : (algSpec (CommRingCat.of k)).obj (op B) ≅ G.X)

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- The tensor coordinate presentation `Spec (K ⊗ B) ≅ G_K` of the base change. -/
def baseChangePresentation :
    (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K (K ⊗[k] B))) ≅ (G_K).X :=
  Over.isoMk (Descent.TensorCoordinates.baseChangeIso k K B G.X ψ)
    (Descent.TensorCoordinates.baseChangeIso_hom_snd k K B G.X ψ)

variable {k K G}

set_option backward.isDefEq.respectTransparency false in
/-- The pullback comparison of points sends the point classified by a `K`-algebra map
`f : K ⊗ B → A` to the point classified by its restriction `b ↦ f (1 ⊗ b)`. -/
theorem affineBaseChangeEquiv_pt (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] (f : K ⊗[k] B →ₐ[K] A) :
    Lie.affineBaseChangeEquiv k K G A
        (pt (corepresentableBy G_K (baseChangePresentation k K G ψ)) (A := CommAlgCat.of K A) f) =
      pt (corepresentableBy G ψ) (A := CommAlgCat.of k A)
        ((f.restrictScalars k).comp includeRight) := by
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left]
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (Descent.TensorCoordinates.baseChangeIso k K B G.X ψ).hom) ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom ((f.restrictScalars k).comp includeRight).toRingHom) ≫ ψ.hom.left
  rw [Category.assoc, Descent.TensorCoordinates.baseChangeIso_hom_fst, ← Category.assoc,
    ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comultiplication of `K ⊗ B`, restricted to `B`, is the comultiplication of `B` followed
by the inclusion `B ⊗ B → (K ⊗ B) ⊗_K (K ⊗ B)`, `x ⊗ y ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`. -/
theorem comul_baseChange_comp_includeRight :
    ((comul (corepresentableBy G_K (baseChangePresentation k K G ψ))).restrictScalars k).comp
        (includeRight : B →ₐ[k] K ⊗[k] B) =
      (Algebra.TensorProduct.productMap
        (((includeLeft : K ⊗[k] B →ₐ[K] (K ⊗[k] B) ⊗[K] (K ⊗[k] B)).restrictScalars k).comp
          includeRight)
        (((includeRight : K ⊗[k] B →ₐ[K] (K ⊗[k] B) ⊗[K] (K ⊗[k] B)).restrictScalars k).comp
          includeRight)).comp
        (comul (corepresentableBy G ψ)) := by
  apply pt_injective (corepresentableBy G ψ) (A := CommAlgCat.of k ((K ⊗[k] B) ⊗[K] (K ⊗[k] B)))
  rw [pt_productMap_comp_comul, ← affineBaseChangeEquiv_pt, ← affineBaseChangeEquiv_pt,
    ← affineBaseChangeEquiv_pt]
  exact (congrArg (Lie.affineBaseChangeEquiv k K G _) (pt_comul _)).trans (map_mul _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Contracting the comultiplication of `K ⊗ B` at `1 ⊗ b` with a `K`-linear functional `g`
only involves the comultiplication of `B` and the restriction `x ↦ g (1 ⊗ x)` of `g`. -/
theorem contract_comul_baseChange (g : Module.Dual K (K ⊗[k] B)) (b : B) :
    contract (B := CommAlgCat.of K (K ⊗[k] B)) g
        (comul (corepresentableBy G_K (baseChangePresentation k K G ψ)) ((1 : K) ⊗ₜ[k] b)) =
      TensorProduct.map
        ((g.restrictScalars k) ∘ₗ (includeRight : B →ₐ[k] K ⊗[k] B).toLinearMap)
        LinearMap.id (comul (corepresentableBy G ψ) b) := by
  have h := DFunLike.congr_fun (comul_baseChange_comp_includeRight (K := K) ψ) b
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply] at h
  rw [h]
  generalize comul (corepresentableBy G ψ) b = t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.map_tmul]
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      AlgHom.toLinearMap_apply, LinearMap.id_coe, id]
    erw [contract_tmul]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- Every element of `K ⊗ B` lies in the `K`-span of finitely many elements `1 ⊗ b`. -/
theorem exists_finset_mem_span (y : K ⊗[k] B) :
    ∃ S : Finset B, y ∈ Submodule.span K ((fun b : B => (1 : K) ⊗ₜ[k] b) '' (S : Set B)) := by
  classical
  induction y using TensorProduct.inductionOn with
  | tmul c b =>
    refine ⟨{b}, ?_⟩
    have hc : c ⊗ₜ[k] b = c • ((1 : K) ⊗ₜ[k] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, by simp, rfl⟩)
  | add x y hx hy =>
    obtain ⟨S, hS⟩ := hx
    obtain ⟨T, hT⟩ := hy
    refine ⟨S ∪ T, Submodule.add_mem _ (Submodule.span_mono ?_ hS) (Submodule.span_mono ?_ hT)⟩
    · exact Set.image_mono (by simp)
    · exact Set.image_mono (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Local right integrals on `B` extend `K`-linearly to local right integrals on `K ⊗ B`. -/
theorem hasLocalRightIntegrals_baseChange (h : HasLocalRightIntegrals ψ) :
    HasLocalRightIntegrals (baseChangePresentation k K G ψ) := by
  classical
  dsimp only [HasLocalRightIntegrals] at h ⊢
  intro T
  choose S hS using fun y : K ⊗[k] B => exists_finset_mem_span (k := k) (K := K) (B := B) y
  obtain ⟨r, hr1, hr⟩ := h (T.biUnion S)
  let rK : Module.Dual K (K ⊗[k] B) := ((Algebra.linearMap k K) ∘ₗ r).liftBaseChange K
  have hrK : ∀ x : B, rK ((1 : K) ⊗ₜ[k] x) = algebraMap k K (r x) := fun x => by
    simp [rK]
  refine ⟨rK, ?_, fun y hy => ?_⟩
  · rw [Algebra.TensorProduct.one_def, hrK, hr1, map_one]
  have hsub : ∀ b ∈ S y, b ∈ T.biUnion S := fun b hb => Finset.mem_biUnion.mpr ⟨y, hy, hb⟩
  have hspan := hS y
  generalize S y = S0 at hsub hspan
  clear hy
  induction hspan using Submodule.span_induction with
  | zero => rw [map_zero, map_zero, zero_smul]
  | add x z _ _ hx hz => rw [map_add, map_add, hx, hz, add_smul]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_assoc]
  | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      have hbT := hsub b hb
      change contract (B := CommAlgCat.of K (K ⊗[k] B)) rK
        (comul (corepresentableBy G_K (baseChangePresentation k K G ψ)) ((1 : K) ⊗ₜ[k] b)) = _
      rw [contract_comul_baseChange]
      have hmap : ∀ t : B ⊗[k] B, TensorProduct.map
          ((rK.restrictScalars k) ∘ₗ (includeRight : B →ₐ[k] K ⊗[k] B).toLinearMap)
          LinearMap.id t = (1 : K) ⊗ₜ[k] contract r t := by
        intro t
        induction t using TensorProduct.inductionOn with
        | tmul x z =>
          rw [TensorProduct.map_tmul, contract_tmul]
          change rK ((1 : K) ⊗ₜ[k] x) ⊗ₜ[k] z = _
          rw [hrK, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
        | add x z hx hz => rw [map_add, map_add, hx, hz, TensorProduct.tmul_add]
      have hrb : contract r (comul (corepresentableBy G ψ) b) = r b • 1 := hr b hbT
      rw [hmap, hrb, hrK, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
        ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one]

set_option backward.isDefEq.respectTransparency false in
/-- Local right integrals on `K ⊗ B` descend to `B`: restrict to `1 ⊗ B` and compose with a
`k`-linear functional `φ : K → k` with `φ 1 = 1`. -/
theorem hasLocalRightIntegrals_of_baseChange
    (h : HasLocalRightIntegrals (baseChangePresentation k K G ψ)) :
    HasLocalRightIntegrals ψ := by
  classical
  dsimp only [HasLocalRightIntegrals] at h ⊢
  intro T
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : K) ≠ 0)
  obtain ⟨g, hg1, hg⟩ := h (T.image fun b : B => (1 : K) ⊗ₜ[k] b)
  let g₀ : B →ₗ[k] K := (g.restrictScalars k) ∘ₗ (includeRight : B →ₐ[k] K ⊗[k] B).toLinearMap
  let r : Module.Dual k B := φ ∘ₗ g₀
  have hr : ∀ x : B, r x = φ (g ((1 : K) ⊗ₜ[k] x)) := fun x => rfl
  refine ⟨r, ?_, fun b hb => ?_⟩
  · rw [hr, ← Algebra.TensorProduct.one_def, hg1, hφ]
  -- the `k`-linear projection `K ⊗ B → B`, `c ⊗ x ↦ φ c • x`
  let π : K ⊗[k] B →ₗ[k] B := TensorProduct.lid k B ∘ₗ φ.rTensor B
  have hπ : ∀ t : B ⊗[k] B, π (TensorProduct.map g₀ LinearMap.id t) = contract r t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x z => simp [π, r, contract_tmul]
    | add x z hx hz => rw [map_add, map_add, hx, hz, map_add]
  have hgb := hg ((1 : K) ⊗ₜ[k] b) (Finset.mem_image_of_mem _ hb)
  change contract (B := CommAlgCat.of K (K ⊗[k] B)) g
    (comul (corepresentableBy G_K (baseChangePresentation k K G ψ)) ((1 : K) ⊗ₜ[k] b)) = _
    at hgb
  rw [contract_comul_baseChange] at hgb
  change contract r (comul (corepresentableBy G ψ) b) = _
  rw [← hπ, hgb, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [π, hr]

end BaseChange

/-! ### The theorem -/

/-- **Linear reductivity is invariant under extension of the base field.** -/
theorem linearlyReductiveFieldExtension : LinearlyReductiveFieldExtensionStatement.{u} := by
  intro k K _ _ _ G _ _
  change (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), sSup (simpleStable ρ) = ⊤) ↔
    ∀ (n : ℕ) (ρ : MatrixRepresentation
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)), sSup (simpleStable ρ) = ⊤
  rw [linearlyReductive_iff_hasLocalRightIntegrals (Lie.coordinateIso G),
    linearlyReductive_iff_hasLocalRightIntegrals
      (baseChangePresentation k K G (Lie.coordinateIso G))]
  exact ⟨hasLocalRightIntegrals_baseChange _, hasLocalRightIntegrals_of_baseChange _⟩

end Langlands.GroupScheme.LinearReductivity
