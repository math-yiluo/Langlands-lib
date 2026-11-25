/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveSystemData
import WeilConjectures.AlgebraicGeometry.EtaleCoefficientProductEmbeddingCompatibility

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem etaleCoefficientProductEmbedding_mono
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (i : I) : Mono (etaleCoefficientProductEmbedding D F φ i) := by
  have : IsIso (D.map (𝟙 i).op) := by
    have h : D.map (𝟙 i).op = 𝟙 (D.obj (op i)) := D.map_id (op i)
    rw [h]
    infer_instance
  have : Mono (φ (𝟙 i) ≫ Injective.ι (F i)) := by
    rw [hidentity]
    infer_instance
  have : Mono (etaleCoefficientProductEmbedding D F φ i ≫ Pi.π _ ⟨i, 𝟙 i⟩) := by
    dsimp [etaleCoefficientProductEmbedding]
    rw [Pi.lift_comp_π]
    infer_instance
  exact mono_of_mono (etaleCoefficientProductEmbedding D F φ i) (Pi.π _ ⟨i, 𝟙 i⟩)

set_option linter.unusedVariables false in
/-- The explicit outgoing-arrow product admits compatible transitions and embeddings.
Source: Stacks Project, Tag 0EXZ, product/direct-image construction.
(blueprint: lem-weil-pbc-etale-coefficient-injective-system-embedding).

Proof: write J_k = Injective.under (F k), with canonical mono e_k. For each
arrow h : i to k, the h-component of a_i is the adjoint transpose of phi_h
followed by e_k. For f : i to j and g : j to k, project FI_i to the factor
indexed by f followed by g. Transport that factor through direct-image
composition, apply inverse image along f, then its adjunction counit. This
gives a map into the g-factor of FI_j; the universal property of the product
defines psi_f. Check each product projection: naturality and the triangle
identities of the adjunction and the inverse/direct-image composition
comparisons give the identity and composition laws for psi. Transposing the
same projected equations identifies a_j after phi_f with psi_f after inverse
image of a_i, using hcomposition. At the identity arrow the adjunction identity
comparison identifies the projection of a_i with e_i, using hidentity. Since
e_i is mono, a_i is mono. All products are small: the arrows form a sigma
type indexed by I in universe u, inside the universe u+1 sheaf category. -/
theorem etale_coefficient_injective_system_embedding
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
 :
    let FI := etaleCoefficientInjectiveTarget D F
    ∃ (ψ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FI i) ⟶ FI j)
    (hidentityI : ∀ i : I, ψ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FI i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FI i))
    (hcompositionI : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ψ f) ≫ ψ g)
    (ai : ∀ i : I, F i ⟶ FI i),
      (∀ i : I, Mono (ai i)) ∧
      (∀ (i j : I) (f : i ⟶ j),
        φ f ≫ ai j = (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).map (ai i) ≫ ψ f)
    := by
  obtain ⟨hid, hcomp⟩ := etale_coefficient_product_transition_laws D F
  exact ⟨etaleCoefficientProductTransition D F, hid, hcomp,
    etaleCoefficientProductEmbedding D F φ, etaleCoefficientProductEmbedding_mono D F φ hidentity,
    etale_coefficient_product_embedding_compatibility D F φ hcomposition⟩

end AlgebraicGeometry.Etale
