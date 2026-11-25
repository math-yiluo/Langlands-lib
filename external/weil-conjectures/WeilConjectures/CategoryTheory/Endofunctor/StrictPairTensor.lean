/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Tensoring strict pairs

Source: the tensor formula in the latest blueprint's Tate compatibility lemma.
(blueprint: lem-wf-strict-pair-tensor)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v u' v'
open CategoryTheory MonoidalCategory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (P : C ⥤ C) [P.Monoidal] {L : C} (τ : P.obj L ≅ L)

/-- Tensor with a fixed strict pair, using the inverse tensorator.
Source: latest blueprint, Tate twist formula (blueprint: lem-wf-strict-pair-tensor).
The morphism equation follows by tensorator naturality and the original strict
morphism equation; tensor bifunctoriality gives the identity and composition laws. -/
def tensorWith : IsoAlgebra P ⥤ IsoAlgebra P where
  obj K := mk (K.carrier ⊗ L) ((Functor.Monoidal.μIso P _ _).symm ≪≫ tensorIso K.str τ)
  map {K K'} f := ObjectProperty.homMk {
    f := f.hom.f ⊗ₘ 𝟙 L
    h := by
      have hf : P.map f.hom.f ≫ K'.str.hom = K.str.hom ≫ f.hom.f := f.hom.h
      change P.map (f.hom.f ⊗ₘ 𝟙 L) ≫
        (Functor.OplaxMonoidal.δ P _ _ ≫ (K'.str.hom ⊗ₘ τ.hom)) =
          (Functor.OplaxMonoidal.δ P _ _ ≫ (K.str.hom ⊗ₘ τ.hom)) ≫
            (f.hom.f ⊗ₘ 𝟙 L)
      rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural, Category.assoc,
        tensorHom_comp_tensorHom, P.map_id, Category.id_comp,
        hf]
      simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id] }
  map_id K := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by simp))
  map_comp f g := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by
    change (f.hom.f ≫ g.hom.f) ⊗ₘ 𝟙 L =
      (f.hom.f ⊗ₘ 𝟙 L) ≫ (g.hom.f ⊗ₘ 𝟙 L)
    rw [tensorHom_comp_tensorHom, Category.comp_id]))

@[simp]
lemma tensorRight_obj_carrier (K : IsoAlgebra P) :
    ((tensorWith P τ).obj K).carrier = K.carrier ⊗ L := rfl

@[simp]
lemma tensorRight_obj_str (K : IsoAlgebra P) :
    ((tensorWith P τ).obj K).str =
      (Functor.Monoidal.μIso P _ _).symm ≪≫ tensorIso K.str τ := mk_str _ _

@[simp]
lemma tensorRight_map {K K' : IsoAlgebra P} (f : K ⟶ K') :
    ((tensorWith P τ).map f).hom.f = f.hom.f ⊗ₘ 𝟙 L := rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {P : C ⥤ C} [P.Monoidal] {Q : D ⥤ D} [Q.Monoidal]
  (B : C ⥤ D) [B.Monoidal] (c : B ⋙ Q ≅ P ⋙ B) [c.hom.IsMonoidal]

/-- The cotensor square associated to a monoidal commuting comparison.
Source: latest blueprint, monoidality used in the beta square
(blueprint: lem-wf-strict-pair-tensor).
Proof: precompose with the composite tensorator, apply the monoidal equation for
c, and cancel each tensorator with its inverse. -/
lemma scalar_cotensor_square (K L : C) :
    Q.map (Functor.OplaxMonoidal.δ B K L) ≫
        Functor.OplaxMonoidal.δ Q (B.obj K) (B.obj L) ≫
          (c.hom.app K ⊗ₘ c.hom.app L) =
      c.hom.app (K ⊗ L) ≫ B.map (Functor.OplaxMonoidal.δ P K L) ≫
        Functor.OplaxMonoidal.δ B (P.obj K) (P.obj L) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ Q (B.obj K) (B.obj L) ≫
    Q.map (Functor.LaxMonoidal.μ B K L))).mp
  simp only [Category.assoc, ← Q.map_comp_assoc, Functor.Monoidal.μ_δ, Q.map_id,
    Category.id_comp, Functor.Monoidal.μ_δ_assoc]
  have h := NatTrans.IsMonoidal.tensor (τ := c.hom) K L
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj] at h
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, ← B.map_comp_assoc, Functor.Monoidal.μ_δ, B.map_id,
    Category.id_comp, Category.comp_id]

/-- A monoidal scalar comparison and an equivariant line isomorphism induce a
natural isomorphism between the corresponding strict tensor functors.
Source: latest blueprint, beta_K=(1 tensor b)t_B
(blueprint: lem-wf-strict-pair-tensor).
Proof: inverse tensorators are natural. The monoidal square for c identifies their
composites on the two sides; the line equation replaces Q(b) followed by sigma.
Bifunctoriality and naturality of B's tensorator then give the strict morphism
square for beta. The inverse is inherited from its underlying isomorphism, and
naturality follows from tensorator naturality. -/
def tensorRightScalarIso {L : C} {M : D} (τ : P.obj L ≅ L) (σ : Q.obj M ≅ M)
    (b : B.obj L ≅ M)
    (hb : Q.map b.hom ≫ σ.hom = c.hom.app L ≫ B.map τ.hom ≫ b.hom) :
    tensorWith P τ ⋙ mapOfNatIso c ≅ mapOfNatIso c ⋙ tensorWith Q σ := by
  let β : MonoidalCategory.tensorRight L ⋙ B ≅ B ⋙ MonoidalCategory.tensorRight M :=
    NatIso.ofComponents
      (fun K ↦ (Functor.Monoidal.μIso B K L).symm ≪≫ tensorIso (Iso.refl _) b)
      (by
        intro K K' f
        change B.map (f ▷ L) ≫
            (Functor.OplaxMonoidal.δ B K' L ≫ (𝟙 _ ⊗ₘ b.hom)) =
          (Functor.OplaxMonoidal.δ B K L ≫ (𝟙 _ ⊗ₘ b.hom)) ≫
            (B.map f ▷ M)
        simp only [← tensorHom_id]
        rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural]
        simp only [B.map_id, Category.assoc, tensorHom_comp_tensorHom,
          Category.comp_id, Category.id_comp])
  refine NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (β.app K.carrier) ?_)) ?_
  · change Q.map (Functor.OplaxMonoidal.δ B K.carrier L ≫ (𝟙 _ ⊗ₘ b.hom)) ≫
        (Functor.OplaxMonoidal.δ Q _ _ ≫
          ((c.hom.app K.carrier ≫ B.map K.str.hom) ⊗ₘ σ.hom)) =
      (c.hom.app (K.carrier ⊗ L) ≫
        B.map (Functor.OplaxMonoidal.δ P _ _ ≫ (K.str.hom ⊗ₘ τ.hom))) ≫
          (Functor.OplaxMonoidal.δ B _ _ ≫ (𝟙 _ ⊗ₘ b.hom))
    rw [Q.map_comp, Category.assoc, ← Category.assoc (Q.map (𝟙 _ ⊗ₘ b.hom)),
      ← Functor.OplaxMonoidal.δ_natural]
    simp only [Q.map_id, Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp, hb]
    rw [← tensorHom_comp_tensorHom]
    have ht : (B.map K.str.hom ⊗ₘ B.map τ.hom ≫ b.hom) =
        (B.map K.str.hom ⊗ₘ B.map τ.hom) ≫ (𝟙 _ ⊗ₘ b.hom) := by
      rw [tensorHom_comp_tensorHom, Category.comp_id]
    rw [ht]
    rw [reassoc_of% (scalar_cotensor_square B c K.carrier L)]
    simp only [Category.assoc, B.map_comp]
    rw [Functor.OplaxMonoidal.δ_natural_assoc]
  · intro K K' f
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    change B.map (f.hom.f ⊗ₘ 𝟙 L) ≫ β.hom.app K'.carrier =
      β.hom.app K.carrier ≫ (B.map f.hom.f ⊗ₘ 𝟙 M)
    have h := β.hom.naturality f.hom.f
    change B.map (f.hom.f ▷ L) ≫ β.hom.app K'.carrier =
      β.hom.app K.carrier ≫ (B.map f.hom.f ▷ M) at h
    simpa only [tensorHom_id] using h

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {P : C ⥤ C} [P.Monoidal] {Q : D ⥤ D} [Q.Monoidal]

/-- Existential monoidal and line data suffice to construct the strict comparison.
Source: Tate compatibility, the beta square (blueprint: lem-wf-strict-pair-tensor).
Proof: eliminate the two witnesses and use tensorRightScalarIso. This elimination
is performed for abstract monoidal categories, so applications need not expand
monoidal structures in the concrete derived category. -/
theorem tensorRightScalarIso_nonempty (B : C ⥤ D) (c : B ⋙ Q ≅ P ⋙ B)
    {L : C} {M : D} (τ : P.obj L ≅ L) (σ : Q.obj M ≅ M)
    (h : ∃ hB : B.Monoidal, letI := hB
      NatTrans.IsMonoidal c.hom ∧ ∃ b : B.obj L ≅ M,
        Q.map b.hom ≫ σ.hom = c.hom.app L ≫ B.map τ.hom ≫ b.hom) :
    Nonempty (tensorWith P τ ⋙ mapOfNatIso c ≅ mapOfNatIso c ⋙ tensorWith Q σ) := by
  obtain ⟨hB, hc, b, hb⟩ := h
  let := hB
  let := hc
  exact ⟨tensorRightScalarIso B c τ σ b hb⟩


end CategoryTheory.Endofunctor.IsoAlgebra
