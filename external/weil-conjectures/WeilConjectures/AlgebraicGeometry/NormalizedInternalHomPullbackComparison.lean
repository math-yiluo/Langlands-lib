/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Evaluation mates of normalized derived internal Hom
Source: Stacks, Tags 08I3, 08DJ and 079U.
(blueprint: lem-pc-normalized-internal-hom-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w vC vD uC uD
open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
section EvaluationMate
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]
  (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
  (F : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R)
  (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
  (ex : ∀ A K L : C, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
  (ey : ∀ A K L : D, (A ⟶ J.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
  (hx : ∀ (A A' K K' L L' : C) (p : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
    (f : A ⟶ H.obj (op K, L)),
    ex A' K' L' (p ≫ f ≫ H.map (b.op, c)) = (p ⊗ₘ b) ≫ ex A K L f ≫ c)
  (hy : ∀ (A A' K K' L L' : D) (p : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
    (f : A ⟶ J.obj (op K, L)),
    ey A' K' L' (p ≫ f ≫ J.map (b.op, c)) = (p ⊗ₘ b) ≫ ey A K L f ≫ c)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include hx hy in
/-- Transpose pulled-back evaluation in both Hom variables.
Source: Stacks, Remark 08I3. -/
private theorem evaluationMate_exists :
    ∃ γ : H ⟶ F.op.prod F ⋙ J ⋙ R,
      ∀ K L : C,
        (a.homEquiv _ _).symm (γ.app (op K, L)) =
          (ey _ _ _).symm
            (t.inv.app (H.obj (op K, L), K) ≫ F.map (ex _ K L (𝟙 _))) := by
  let δ (K L : C) : F.obj (H.obj (op K, L)) ⟶ J.obj (op (F.obj K), F.obj L) :=
    (ey _ _ _).symm (t.inv.app (H.obj (op K, L), K) ≫ F.map (ex _ K L (𝟙 _)))
  have eval_nat (K K' L L' : C) (b : K' ⟶ K) (c : L ⟶ L') :
      (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c) ⊗ₘ 𝟙 K') ≫
          ex _ K' L' (𝟙 _) =
        (𝟙 (H.obj (op K, L)) ⊗ₘ b) ≫ ex _ K L (𝟙 _) ≫ c := by
    have h₁ := hx _ _ _ _ _ _
      (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c)) (𝟙 K') (𝟙 L') (𝟙 _)
    have h₂ := hx _ _ _ _ _ _ (𝟙 (H.obj (op K, L))) b c (𝟙 _)
    change ex _ _ _ (_ ≫ _ ≫ H.map (𝟙 _)) = _ at h₁
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h₁
    simp only [Category.id_comp] at h₂
    exact h₁.symm.trans h₂
  have δnat (K K' L L' : C) (b : K' ⟶ K) (c : L ⟶ L') :
      F.map (H.map (X := (op K, L)) (Y := (op K', L'))
        (b.op, c)) ≫
          δ K' L' =
        δ K L ≫ J.map ((F.map b).op, F.map c) := by
    apply (ey _ _ _).injective
    have h₁ := hy _ _ _ _ _ _
      (F.map (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c)))
      (𝟙 _) (𝟙 _) (δ K' L')
    change ey _ _ _ (_ ≫ _ ≫ J.map (𝟙 _)) = _ at h₁
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h₁
    have h₂ := hy _ _ _ _ _ _ (𝟙 _) (F.map b) (F.map c) (δ K L)
    simp only [Category.id_comp] at h₂
    rw [h₁, h₂]
    dsimp only [δ]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have ht₁ := t.inv.naturality (X := (H.obj (op K, L), K'))
      (Y := (H.obj (op K', L'), K')) (H.map (X := (op K, L)) (Y := (op K', L')) (b.op, c), 𝟙 K')
    have ht₂ := t.inv.naturality (X := (H.obj (op K, L), K'))
      (Y := (H.obj (op K, L), K)) (𝟙 _, b)
    dsimp at ht₁ ht₂
    simp only [CategoryTheory.Functor.map_id] at ht₁ ht₂
    rw [← Category.assoc, ht₁, Category.assoc, ← F.map_comp, eval_nat]
    rw [F.map_comp, F.map_comp, ← Category.assoc, ← ht₂]
    simp only [Category.assoc]
  refine ⟨{ app := fun P => a.homEquiv _ _ (δ P.1.unop P.2)
            naturality := ?_ }, ?_⟩
  · intro P Q h
    obtain ⟨K, L⟩ := P
    obtain ⟨K', L'⟩ := Q
    obtain ⟨b, c⟩ := h
    dsimp
    rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right]
    apply congrArg (a.homEquiv _ _)
    exact δnat K.unop K'.unop L L' b.unop c
  · intro K L
    exact (a.homEquiv _ _).symm_apply_apply _
end EvaluationMate

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The natural evaluation mate for fixed pullback and tensor-Hom adjunctions.
This statement concerns only sheaf internal Hom, with no global sections or base rings.
Source: Stacks, Remark 08I3, Lemmas 08DJ and 079U
(blueprint: lem-pc-normalized-internal-hom-pullback-comparison).
Proof: use K-flat resolutions of both tensor inputs and the canonical degreewise
pullback tensor isomorphism. The left-derived counits and localization tensor maps
transport this to an invertible comparison on derived objects. Comparisons between
K-flat resolutions give independence and naturality, hence a natural isomorphism t
whose hom satisfies IsCanonicalPullbackTensorComparison. For each (K,L), precompose
pullback of the evaluation counit by t.inv, transpose by bT, and then transpose by a.
The displayed mate equation follows by cancellation of the Hom equivalences.
For naturality, apply the inverse equivalence of a to the naturality square and
uncurry by bT. Naturality of t and the three-variable naturality supplied by hS
and hT reduce both sides to pullback of the same evaluation square. Injectivity
of those equivalences gives equality of the two composites, defining gamma. -/
theorem exists_normalizedInternalHomPullbackComparison
    {T S : Scheme.{u}} (g : T ⟶ S)
    (a : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (bS : ∀ K : schemeDerivedCategory S, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf)).obj
            (op K))
      (bT : ∀ K : schemeDerivedCategory T, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
            T.toRingedSpace.sheaf)).obj
            (op K))
    [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (hS : IsCanonicalDerivedTensorHom S (fun A K L => ((bS K).homEquiv A L).symm))
    (hT : IsCanonicalDerivedTensorHom T (fun A K L => ((bT K).homEquiv A L).symm)) :
    ∃ (t : tensor (schemeDerivedCategory S) ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor
          (schemeDerivedCategory T))
      (γ : derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf ⟶
        (derivedPullback g).op.prod (derivedPullback g) ⋙
          derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace) T.toRingedSpace.sheaf ⋙
            schemeDerivedDirectImage g),
      IsCanonicalPullbackTensorComparison g
        (fun E K => t.hom.app (E, K)) ∧
      (∀ K L : schemeDerivedCategory S,
        (a.homEquiv
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op K, L))
            ((derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
              T.toRingedSpace.sheaf).obj
                (op ((derivedPullback g).obj K), (derivedPullback g).obj L))).symm
            (γ.app (op K, L)) =
          (bT ((derivedPullback g).obj K)).homEquiv
            ((derivedPullback g).obj
              ((derivedInternalHom (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).obj (op K, L))) ((derivedPullback g).obj L)
            (t.inv.app
                ((derivedInternalHom (Opens.grothendieckTopology S)
                  S.toRingedSpace.sheaf).obj (op K, L), K) ≫
              (derivedPullback g).map ((bS K).counit.app L))) := by
  have h := exists_mixedHomTensorPullbackIso.{u, w} g
  obtain ⟨t, ht⟩ := h
  have hmate := evaluationMate_exists
    (C := schemeDerivedCategory S) (D := schemeDerivedCategory T)
    (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf)
    (derivedInternalHom (Opens.grothendieckTopology T) T.sheaf)
    (derivedPullback g) (schemeDerivedDirectImage g) a t
    (fun A K L => ((bS K).homEquiv A L).symm)
    (fun A K L => ((bT K).homEquiv A L).symm) hS.1 hT.1
  obtain ⟨γ, hγ⟩ := hmate
  refine ⟨t, γ, ht, ?_⟩
  intro K L
  have h := hγ K L
  dsimp only [Functor.prod_obj, Functor.op_obj, Functor.comp_obj, Equiv.symm_symm] at h
  refine h.trans ?_
  exact congrArg
    (fun e ↦ (bT ((derivedPullback g).obj K)).homEquiv _ _
      (t.inv.app
          ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op K, L), K) ≫
        (derivedPullback g).map e))
    ((bS K).homEquiv_symm_id L)

end AlgebraicGeometry
