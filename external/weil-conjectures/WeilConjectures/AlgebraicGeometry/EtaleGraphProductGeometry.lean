/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
public import WeilConjectures.AlgebraicGeometry.EtalePairwiseProductGraphNormalization

/-! # The products in the graph interchange grid

Source: Stacks Project, Tag 0F7J, product-graph extension of the A--F diagram
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

namespace EtaleGraphInterchangeDiagram

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g)

/-- The product of the two open-then-proper presentations. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev productG := EtaleGraphPresentation.PairwiseProduct.presentation
  (EtaleGraphPresentation.ofCompactification d₁.compactification)
  (EtaleGraphPresentation.ofCompactification d₂.compactification)

/-- The product presentation over the middle scheme. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev productF := EtaleGraphPresentation.PairwiseProduct.presentation
  d₁.sourcePresentation d₂.sourcePresentation

/-- The product presentation over the final scheme. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev productH := EtaleGraphPresentation.PairwiseProduct.presentation
  d₁.compositePresentation d₂.compositePresentation

/-- The ambient product before imposing equality in the middle scheme.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev productV := pullback (d₁.k ≫ d₁.p ≫ d₁.q) (d₂.k ≫ d₂.p ≫ d₂.q)

/-- The product of the two supplied open immersions k. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def productK : d₁.productV d₂ ⟶ pullback (d₁.p ≫ d₁.q) (d₂.p ≫ d₂.q) :=
  pullback.map _ _ _ _ d₁.k d₂.k (𝟙 Z) (by simp) (by simp)

/-- The product of the proper maps p. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def productP : pullback (d₁.p ≫ d₁.q) (d₂.p ≫ d₂.q) ⟶ pullback d₁.q d₂.q :=
  pullback.map _ _ _ _ d₁.p d₂.p (𝟙 Z) (by simp) (by simp)

/-- The product of the proper maps r into Y times Y over Z. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def productR : d₁.productV d₂ ⟶ pullback (d₁.i ≫ d₁.q) (d₂.i ≫ d₂.q) :=
  pullback.map _ _ _ _ d₁.r d₂.r (𝟙 Z)
    (by simpa only [Category.comp_id, Category.assoc] using
      congrArg (· ≫ d₁.q) d₁.square.w)
    (by simpa only [Category.comp_id, Category.assoc] using
      congrArg (· ≫ d₂.q) d₂.square.w)

/-- Product open e. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def productE :
    pullback ((d₁.e ≫ d₁.k) ≫ (d₁.p ≫ d₁.q))
      ((d₂.e ≫ d₂.k) ≫ (d₂.p ≫ d₂.q)) ⟶ d₁.productV d₂ :=
  pullback.map _ _ _ _ d₁.e d₂.e (𝟙 Z) (by simp [Category.assoc])
    (by simp [Category.assoc])

/-- Product k is open. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
instance productK_open : IsOpenImmersion (d₁.productK d₂) := by
  apply MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance <;>
    simp only [Category.assoc, d₁.square.w_assoc, d₂.square.w_assoc]

/-- Product p is proper. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
instance productP_proper : IsProper (d₁.productP d₂) := by
  apply MorphismProperty.pullbackMap (P := @IsProper) inferInstance inferInstance <;>
    simp only [Category.assoc, d₁.square.w_assoc, d₂.square.w_assoc]

/-- Product r is proper. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
instance productR_proper : IsProper (d₁.productR d₂) := by
  apply MorphismProperty.pullbackMap (P := @IsProper) inferInstance inferInstance <;>
    simp only [Category.assoc, d₁.square.w_assoc, d₂.square.w_assoc]

/-- Product e is open. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
instance productE_open : IsOpenImmersion (d₁.productE d₂) := by
  apply MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance <;>
    simp only [Category.assoc, d₁.square.w_assoc, d₂.square.w_assoc]

/-- The product proper/open square commutes. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node).
Proof: project to T₁ and T₂, and use the two given commutative squares. -/
theorem product_square :
    CommSq (d₁.productK d₂) (d₁.productR d₂) (d₁.productP d₂)
      (d₁.productG d₂).e := by
  constructor
  dsimp only [productK, productP, productR, productG,
    EtaleGraphPresentation.PairwiseProduct.presentation,
    EtaleGraphPresentation.PairwiseProduct.b, compactification,
    EtaleGraphPresentation.ofCompactification]
  rw [pullback.map_comp, pullback.map_comp]
  congr 1
  · exact d₁.square.w
  · exact d₂.square.w

/-- The product of e followed by the product of k is the product of e k.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node).
Proof: compare the two projections to P₁ and P₂. -/
theorem productE_productK :
    d₁.productE d₂ ≫ d₁.productK d₂ = (d₁.productH d₂).e := by
  dsimp only [productE, productK, productH, EtaleGraphPresentation.PairwiseProduct.presentation,
      EtaleGraphPresentation.PairwiseProduct.b, compositePresentation, sourcePresentation,
      compactification, EtaleGraphPresentation.ofCompactification, pullback.mapDesc,
        pullback.congrHom_hom, pullback.map]
  apply pullback.hom_ext <;>
    simp only [pullback.congrHom_hom, pullback.mapDesc, pullback.map,
      Category.assoc, Category.comp_id, Category.id_comp,
      pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The product of p followed by q is the structural map of the product H.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node).
Proof: use the first projection equation and associativity. -/
theorem productP_productQ :
    d₁.productP d₂ ≫ (d₁.productG d₂).p = (d₁.productH d₂).p := by
  dsimp only [productP, productG, productH, EtaleGraphPresentation.PairwiseProduct.presentation,
    EtaleGraphPresentation.PairwiseProduct.p, compositePresentation, sourcePresentation,
    compactification, EtaleGraphPresentation.ofCompactification]
  simp only [Category.assoc, pullback.map, pullback.mapDesc, pullback.congrHom_hom,
      pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

/-- The supplied square identifies the two structural maps to Z. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
theorem productR_to_base (d : EtaleGraphInterchangeDiagram f g) :
    d.r ≫ g = d.k ≫ d.p ≫ d.q := by
  calc
    d.r ≫ g = d.r ≫ (d.i ≫ d.q) := congrArg (d.r ≫ ·) d.facG.symm
    _ = d.k ≫ d.p ≫ d.q := by rw [← Category.assoc, ← d.square.w, Category.assoc]

/-- The supporting open has the same structural map by either factorization.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
theorem productW_to_base (d : EtaleGraphInterchangeDiagram f g) :
    (d.e ≫ d.r) ≫ g = (d.e ≫ d.k) ≫ (d.p ≫ d.q) := by
  rw [Category.assoc, productR_to_base]
  simp only [Category.assoc]

/-- The middle structural map is separated, being open then proper.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
theorem productG_separated (d : EtaleGraphInterchangeDiagram f g) : IsSeparated g := by
  rw [← d.facG]
  infer_instance

/-- Impose equality over Y on the product V over Z. It is defined by its two projections
and identified below with the pullback of the diagonal of g, followed by equality
transport on the structural maps.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def productBV : pullback d₁.r d₂.r ⟶ d₁.productV d₂ :=
  pullback.lift (pullback.fst d₁.r d₂.r) (pullback.snd d₁.r d₂.r) (by
    rw [← productR_to_base d₁, ← productR_to_base d₂,
      ← Category.assoc, ← Category.assoc,
      pullback.condition (f := d₁.r) (g := d₂.r)])

/-- Impose equality over Y on the product W over Z. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def productBW :
    pullback (d₁.e ≫ d₁.r) (d₂.e ≫ d₂.r) ⟶
      pullback ((d₁.e ≫ d₁.k) ≫ (d₁.p ≫ d₁.q))
        ((d₂.e ≫ d₂.k) ≫ (d₂.p ≫ d₂.q)) :=
  pullback.lift (pullback.fst (d₁.e ≫ d₁.r) (d₂.e ≫ d₂.r))
    (pullback.snd (d₁.e ≫ d₁.r) (d₂.e ≫ d₂.r)) (by
      rw [← productW_to_base d₁, ← productW_to_base d₂]
      simpa only [Category.assoc] using congrArg (· ≫ g)
        (pullback.condition (f := d₁.e ≫ d₁.r) (g := d₂.e ≫ d₂.r)))

/-- The inclusion V_c into V₀ is proper, since g is separated.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance productBV_proper : IsProper (d₁.productBV d₂) := by
  have := productG_separated d₁
  have he : d₁.productBV d₂ = pullback.mapDesc d₁.r d₂.r g ≫
      (pullback.congrHom (productR_to_base d₁) (productR_to_base d₂)).hom := by
    dsimp only [productBV, productV, productF, sourcePresentation,
      EtaleGraphPresentation.PairwiseProduct.presentation]
    apply pullback.hom_ext <;>
      simp only [pullback.congrHom_hom, pullback.mapDesc, pullback.map, Category.assoc,
        pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]
  rw [he]
  infer_instance

/-- The inclusion W_c into W₀ is proper, since g is separated.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance productBW_proper : IsProper (d₁.productBW d₂) := by
  have := productG_separated d₁
  have he : d₁.productBW d₂ =
      pullback.mapDesc (d₁.e ≫ d₁.r) (d₂.e ≫ d₂.r) g ≫
        (pullback.congrHom (productW_to_base d₁) (productW_to_base d₂)).hom := by
    dsimp only [productBW, productH, productF, sourcePresentation, compositePresentation,
      EtaleGraphPresentation.PairwiseProduct.presentation]
    apply pullback.hom_ext <;>
      simp only [pullback.congrHom_hom, pullback.mapDesc, pullback.map, Category.assoc,
        pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]
  rw [he]
  infer_instance

/-- The two graph maps agree under the inclusion of the products.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node).
Proof: equality of both coordinates a₁ and a₂. -/
theorem productA_productBW :
    (d₁.productF d₂).a ≫ d₁.productBW d₂ = (d₁.productH d₂).a := by
  dsimp only [productF, productH, productBW, sourcePresentation, compositePresentation,
      EtaleGraphPresentation.PairwiseProduct.presentation,
      EtaleGraphPresentation.PairwiseProduct.a, pullback.mapDesc, pullback.congrHom_hom,
        pullback.map]
  apply pullback.hom_ext <;>
    simp only [pullback.congrHom_hom, pullback.mapDesc, pullback.map,
      Category.assoc, Category.comp_id, Category.id_comp,
      pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- Equality over Y gives the diagonal of g after applying the two r maps.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node).
Proof: the two coordinates agree by the defining condition for V_c. -/
theorem productBV_productR :
    d₁.productBV d₂ ≫ d₁.productR d₂ =
      (d₁.productF d₂).p ≫ (d₁.productG d₂).a := by
  dsimp only [productBV, productR, productF, productG,
    EtaleGraphPresentation.PairwiseProduct.presentation,
    EtaleGraphPresentation.PairwiseProduct.a, EtaleGraphPresentation.PairwiseProduct.p,
    sourcePresentation, compactification, EtaleGraphPresentation.ofCompactification]
  apply pullback.hom_ext
  · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      Category.comp_id, Category.id_comp]
  · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      Category.comp_id, Category.id_comp]
    exact (pullback.condition (f := d₁.r) (g := d₂.r)).symm

/-- The square comparing the two products of e commutes.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node).
Proof: compare its two projections to V₁ and V₂. -/
theorem productB_square :
    CommSq (d₁.productF d₂).e (d₁.productBW d₂) (d₁.productBV d₂) (d₁.productE d₂) := by
  dsimp only [productBW, productBV, productE, productF, productH,
    EtaleGraphPresentation.PairwiseProduct.presentation,
    EtaleGraphPresentation.PairwiseProduct.b, compositePresentation, sourcePresentation,
    compactification, EtaleGraphPresentation.ofCompactification]
  constructor
  apply pullback.hom_ext <;>
    simp only [pullback.map, Category.assoc, Category.comp_id, Category.id_comp,
      pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

end EtaleGraphInterchangeDiagram

end AlgebraicGeometry.Etale
