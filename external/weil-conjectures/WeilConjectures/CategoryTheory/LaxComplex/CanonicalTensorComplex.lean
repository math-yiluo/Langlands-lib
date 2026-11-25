/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Additive lax monoidal functors on cochain complexes

Define the termwise tensorator by descending its homogeneous summand maps to the
signed total tensor. Naturality preserves the two differential terms, and additivity
preserves their Koszul signs. Associativity and the two unit diagrams reduce to
homogeneous summands. No preservation of coproducts by the functor is required.

The coherence proofs adapt the strong monoidal implementation in
`WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`; the differential
calculation follows the explicit totalization in `CochainCoefficientArrows`.
Source: blueprint local boundary duality, Step 5, signed totalization of section pairings.
(blueprint: lem-a1-canonical-lax-totalization)
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.CanonicalLaxTotal
universe uA vA uB vB

section

variable {A : Type uA} [Category.{vA} A] [Abelian A] [MonoidalCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj X ⊗ L.obj Y ⟶ L.obj (X ⊗ Y))


noncomputable def laxTotalComponent (P Q : CochainComplex A ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).X n ⟶
        L.obj ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun a b h ↦
    e (P.X a) (Q.X b) ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n h))


theorem laxTotalComponent_comm
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      e X Y ≫ L.map (f ⊗ₘ g) = (L.map f ⊗ₘ L.map g) ≫ e X' Y')
    (P Q : CochainComplex A ℤ) (n m : ℤ) :
    laxTotalComponent L e P Q n ≫
        L.map ((CochainComplex.mapBifunctor P Q (curriedTensor A)).d n m) =
      (CochainComplex.mapBifunctor
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).d n m ≫
          laxTotalComponent L e P Q m := by
  by_cases hnm : (ComplexShape.up ℤ).Rel n m
  · change n + 1 = m at hnm
    subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    change a + b = n at hab
    simp only [laxTotalComponent,
      HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      Preadditive.add_comp, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    simp only [L.map_add, Preadditive.comp_add, Category.assoc]
    rw [← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₁,
      ← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq P Q _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P Q _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₁_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega)]
    simp only [
      ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
      one_smul, Functor.map_units_smul, Functor.map_comp,
      Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    simp only [curriedTensor_map_app, curriedTensor_obj_map,
      Functor.mapHomologicalComplex_obj_d, ← tensorHom_id, ← id_tensorHom]
    dsimp only [Functor.mapHomologicalComplex, curriedTensor_obj_obj]
    apply congrArg₂ (· + ·)
    · simpa only [L.map_id, Category.assoc] using
        congrArg (fun f ↦ f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            (a + 1) b (n + 1) (by omega))) (he (P.d a (a + 1)) (𝟙 (Q.X b)))
    · simpa only [L.map_id, Category.assoc, Linear.units_smul_comp,
        Linear.comp_units_smul] using
        congrArg (fun f ↦ a.negOnePow • (f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            a (b + 1) (n + 1) (by omega)))) (he (𝟙 (P.X a)) (Q.d b (b + 1)))
  · rw [HomologicalComplex.shape _ n m hnm, HomologicalComplex.shape _ n m hnm,
      L.map_zero, comp_zero, zero_comp]

end

end CategoryTheory.CanonicalLaxTotal

namespace CategoryTheory.Functor.LaxComplex

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] [Abelian C] [Abelian D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.LaxMonoidal]
def chainTensor (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj K ⊗ (G.mapHomologicalComplex (.up ℤ)).obj L ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L) where
  f n := CategoryTheory.CanonicalLaxTotal.laxTotalComponent G
    (LaxMonoidal.μ G) K L n
  comm' n m _ := CategoryTheory.CanonicalLaxTotal.laxTotalComponent_comm G
    (LaxMonoidal.μ G) (fun f g => (LaxMonoidal.μ_natural G f g).symm) K L n m

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
@[reassoc]
lemma ιTensorObj_chainTensor_f (K L : CochainComplex C ℤ) (p q n : ℤ)
    (h : p + q = n) :
    ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫
      (chainTensor G K L).f n =
    LaxMonoidal.μ G (K.X p) (L.X q) ≫ G.map (ιTensorObj K L p q n h) := by
  change HomologicalComplex.ιMapBifunctor _ _ _ (.up ℤ) _ _ _ h ≫
    CategoryTheory.CanonicalLaxTotal.laxTotalComponent G _ K L n = _
  simp [CategoryTheory.CanonicalLaxTotal.laxTotalComponent]

/-- The unit map of cochain complexes, induced by the lax unit of `G`. -/
def chainUnit :
    𝟙_ (CochainComplex D ℤ) ⟶ (G.mapHomologicalComplex (.up ℤ)).obj
      (𝟙_ (CochainComplex C ℤ)) :=
  (single D (.up ℤ) 0).map (LaxMonoidal.ε G) ≫
    ((singleMapHomologicalComplex G (.up ℤ) 0).app (𝟙_ C)).inv

omit [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
lemma chainUnit_f_zero :
    (chainUnit G).f 0 =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ D)).hom ≫ LaxMonoidal.ε G ≫
        G.map (singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv := by
  simp [chainUnit, single_map_f_self]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
@[reassoc]
lemma chainTensor_naturality_left {K K' : CochainComplex C ℤ} (f : K ⟶ K')
    (L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map f ▷ (G.mapHomologicalComplex (.up ℤ)).obj L ≫
      (chainTensor G K' L) =
    (chainTensor G K L) ≫ (G.mapHomologicalComplex (.up ℤ)).map (f ▷ L) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc, ιTensorObj_chainTensor_f,
    ιTensorObj_chainTensor_f_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  erw [LaxMonoidal.μ_natural_left_assoc]
  rw [← G.map_comp, ← G.map_comp, CochainComplex.Monoidal.ι_whiskerRight]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
@[reassoc]
lemma chainTensor_naturality_right (K : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} (f : L ⟶ L') :
    (G.mapHomologicalComplex (.up ℤ)).obj K ◁ (G.mapHomologicalComplex (.up ℤ)).map f ≫
      (chainTensor G K L') =
    (chainTensor G K L) ≫ (G.mapHomologicalComplex (.up ℤ)).map (K ◁ f) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc, ιTensorObj_chainTensor_f,
    ιTensorObj_chainTensor_f_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  erw [LaxMonoidal.μ_natural_right_assoc]
  rw [← G.map_comp, ← G.map_comp, CochainComplex.ιTensorObj_whiskerLeft_f]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
@[reassoc]
lemma whiskerLeft_ιTensorObj_chainTensor_f (X : D) (K L : CochainComplex C ℤ)
    (p q n : ℤ) (h : p + q = n) :
    X ◁ ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫
      X ◁ (chainTensor G K L).f n =
    X ◁ LaxMonoidal.μ G (K.X p) (L.X q) ≫ X ◁ G.map (ιTensorObj K L p q n h) := by
  rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
  erw [ιTensorObj_chainTensor_f]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
@[reassoc]
lemma ιTensorObj_chainTensor_f_whiskerRight (X : D) (K L : CochainComplex C ℤ)
    (p q n : ℤ) (h : p + q = n) :
    ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ▷ X ≫
      (chainTensor G K L).f n ▷ X =
    LaxMonoidal.μ G (K.X p) (L.X q) ▷ X ≫ G.map (ιTensorObj K L p q n h) ▷ X := by
  have := congrArg (· ▷ X) (ιTensorObj_chainTensor_f G K L p q n h)
  simp only [comp_whiskerRight] at this
  exact this

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
lemma chainTensor_associativity (K L M : CochainComplex C ℤ) :
    (chainTensor G K L) ▷ (G.mapHomologicalComplex (.up ℤ)).obj M ≫
      (chainTensor G (K ⊗ L) M) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (α_ K L M).hom =
    (α_ ((G.mapHomologicalComplex (.up ℤ)).obj K) ((G.mapHomologicalComplex (.up ℤ)).obj L)
        ((G.mapHomologicalComplex (.up ℤ)).obj M)).hom ≫
      (G.mapHomologicalComplex (.up ℤ)).obj K ◁ (chainTensor G L M) ≫
        (chainTensor G K (L ⊗ M)) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = n := h
  have h'' : p + (q + r) = n := by rw [← h', add_assoc]
  have key : (ιTensorObj K L p q (p + q) rfl ▷ M.X r) ≫
      ιTensorObj (K ⊗ L) M (p + q) r n h' ≫
      (α_ K L M).hom.f n =
      (α_ (K.X p) (L.X q) (M.X r)).hom ≫ (K.X p ◁ ιTensorObj L M q r (q + r) rfl) ≫
        ιTensorObj K (L ⊗ M) p (q + r) n h'' := by
    rw [← CochainComplex.Monoidal.ι₂₃_eq _ _ _ p q r (q + r) n rfl h'',
      ← CochainComplex.Monoidal.ι₁₂_associator_hom _ _ _ p q r n h',
      CochainComplex.Monoidal.ι₁₂_eq _ _ _ p q r (p + q) n rfl h', assoc]
  have key' := congrArg G.map key
  simp only [Functor.map_comp] at key'
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [CochainComplex.Monoidal.ι₁₂_eq _ _ _ p q r (p + q) n rfl h',
    CochainComplex.Monoidal.ι₁₂_associator_hom_assoc,
    CochainComplex.Monoidal.ι₂₃_eq _ _ _ p q r (q + r) n rfl h'']
  on_goal 2 => exact h'
  simp only [assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    ιTensorObj_chainTensor_f_whiskerRight_assoc,
    whiskerLeft_ιTensorObj_chainTensor_f_assoc,
    ιTensorObj_chainTensor_f_assoc, ιTensorObj_chainTensor_f]
  erw [LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.μ_natural_right_assoc, key']
  exact LaxMonoidal.associativity_assoc G _ _ _ _

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
lemma mapCochainComplex_leftUnitor_inv (K : CochainComplex C ℤ) :
    (λ_ ((G.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      (chainUnit G) ▷ (G.mapHomologicalComplex (.up ℤ)).obj K ≫
        (chainTensor G (𝟙_ _) K) =
    (G.mapHomologicalComplex (.up ℤ)).map (λ_ K).inv := by
  ext i
  have e : ∀ (X : CochainComplex D ℤ), (λ_ X).inv.f i = (leftUnitor' X).inv i := fun _ ↦ rfl
  have e' : ∀ (X : CochainComplex C ℤ), (λ_ X).inv.f i = (leftUnitor' X).inv i := fun _ ↦ rfl
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, e, e']
  erw [leftUnitor'_inv, leftUnitor'_inv]
  simp only [assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc, ιTensorObj_chainTensor_f]
  rw [chainUnit_f_zero]
  simp only [comp_whiskerRight, assoc, Functor.map_comp, inv_hom_whiskerRight_assoc]
  erw [LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.left_unitality_inv_assoc]
  rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
lemma mapCochainComplex_rightUnitor_inv (K : CochainComplex C ℤ) :
    (ρ_ ((G.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      (G.mapHomologicalComplex (.up ℤ)).obj K ◁ (chainUnit G) ≫
        (chainTensor G K (𝟙_ _)) =
    (G.mapHomologicalComplex (.up ℤ)).map (ρ_ K).inv := by
  ext i
  have e : ∀ (X : CochainComplex D ℤ), (ρ_ X).inv.f i = (rightUnitor' X).inv i := fun _ ↦ rfl
  have e' : ∀ (X : CochainComplex C ℤ), (ρ_ X).inv.f i = (rightUnitor' X).inv i :=
    fun _ ↦ rfl
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, e, e']
  erw [rightUnitor'_inv, rightUnitor'_inv]
  simp only [assoc]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc, ιTensorObj_chainTensor_f]
  rw [chainUnit_f_zero]
  erw [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  simp only [assoc, Functor.map_comp, MonoidalCategory.whiskerLeft_inv_hom_assoc]
  erw [LaxMonoidal.μ_natural_right_assoc, LaxMonoidal.right_unitality_inv_assoc]
  rfl

/-- The signed-total lax monoidal structure on the termwise functor.

Proof: the summand formula defines a chain map by additivity and naturality of the
ordinary tensorator. Its naturality follows on double summands, associativity on
triple summands, and the two unit identities on the degree-zero summands of the unit.
Source: blueprint local boundary duality, Step 5, totalization of section tensor.
(blueprint: lem-a1-canonical-lax-totalization) -/
@[instance_reducible]
def mapCochainComplexLax : (G.mapHomologicalComplex (.up ℤ)).LaxMonoidal where
  ε := chainUnit G
  μ := chainTensor G
  μ_natural_left := chainTensor_naturality_left G
  μ_natural_right K f := chainTensor_naturality_right G K f
  associativity := chainTensor_associativity G
  left_unitality K := by
    rw [← cancel_epi (λ_ _).inv, Iso.inv_hom_id,
      reassoc_of% mapCochainComplex_leftUnitor_inv G,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  right_unitality K := by
    rw [← cancel_epi (ρ_ _).inv, Iso.inv_hom_id,
      reassoc_of% mapCochainComplex_rightUnitor_inv G,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]

end CategoryTheory.Functor.LaxComplex
