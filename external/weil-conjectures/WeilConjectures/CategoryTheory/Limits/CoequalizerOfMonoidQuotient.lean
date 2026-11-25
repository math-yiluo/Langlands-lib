/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.SingleObj

/-!
# Coequalizers as quotients by a monoid action

Let `a, b : P ⟶ Q` be morphisms in a category with binary coproducts. The finite monoid
`CategoryTheory.Limits.CoequalizerMonoid = {1, l, r}`, with `x * y = y` for `y ≠ 1`, acts on
`Q ⨿ P` by the endomorphisms `σₗ = [inl, a ≫ inl]` and `σᵣ = [inl, b ≫ inl]`. A morphism
`h : Q ⨿ P ⟶ Z` is invariant under this action if and only if `h = [k, a ≫ k] = [k, b ≫ k]` for
`k = inl ≫ h` with `a ≫ k = b ≫ k`. Hence the quotient of `Q ⨿ P` by the action, composed with
`inl`, is a coequalizer of `a` and `b`.

This reduces the existence and preservation of coequalizers to that of binary coproducts and of
quotients by a finite monoid.

## Main statements

- `CategoryTheory.Limits.isColimitCoforkOfCocone`: the quotient by the action is a coequalizer.
- `CategoryTheory.Limits.hasCoequalizers_of_hasColimitsOfShape_singleObj`: a category with
  binary coproducts and quotients by `CoequalizerMonoid` has coequalizers.
- `CategoryTheory.Limits.preservesCoequalizers_of_preservesColimitsOfShape_singleObj`: a functor
  preserving binary coproducts and quotients by `CoequalizerMonoid` preserves coequalizers.
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.Limits

/-- The monoid `{1, l, r}` in which `x * y = y` for `y ≠ 1`: the right zero semigroup on two
elements with an identity adjoined. -/
inductive CoequalizerMonoid : Type w
  | one
  | left
  | right
  deriving DecidableEq

namespace CoequalizerMonoid

/-- The multiplication of `CoequalizerMonoid`: `x * 1 = x` and `x * y = y` otherwise. -/
def mul : CoequalizerMonoid.{w} → CoequalizerMonoid.{w} → CoequalizerMonoid.{w}
  | x, one => x
  | _, left => left
  | _, right => right

instance : Monoid CoequalizerMonoid.{w} where
  one := one
  mul := mul
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl

instance : Fintype CoequalizerMonoid.{w} where
  elems := {one, left, right}
  complete x := by cases x <;> simp

instance : Finite CoequalizerMonoid.{w} := inferInstance

end CoequalizerMonoid

open CoequalizerMonoid

variable {C : Type u} [Category.{v} C] {P Q : C} (a b : P ⟶ Q) {W : BinaryCofan Q P}
  (hW : IsColimit W)

/-- The endomorphism of `W = Q ⨿ P` attached to an element of `CoequalizerMonoid`. -/
def coequalizerMonoidEnd : CoequalizerMonoid.{w} → (W.pt ⟶ W.pt)
  | one => 𝟙 _
  | left => hW.desc (BinaryCofan.mk W.inl (a ≫ W.inl))
  | right => hW.desc (BinaryCofan.mk W.inl (b ≫ W.inl))

lemma inl_coequalizerMonoidEnd (m : CoequalizerMonoid.{w}) :
    W.inl ≫ coequalizerMonoidEnd a b hW m = W.inl := by
  cases m
  · exact Category.comp_id _
  · exact hW.fac _ ⟨.left⟩
  · exact hW.fac _ ⟨.left⟩

lemma inr_coequalizerMonoidEnd_left :
    W.inr ≫ coequalizerMonoidEnd.{w} a b hW left = a ≫ W.inl :=
  hW.fac _ ⟨.right⟩

lemma inr_coequalizerMonoidEnd_right :
    W.inr ≫ coequalizerMonoidEnd.{w} a b hW right = b ≫ W.inl :=
  hW.fac _ ⟨.right⟩

lemma mk_inl_coequalizerMonoidEnd {X : C} {ι₁ : Q ⟶ X} {ι₂ : P ⟶ X}
    (hW : IsColimit (BinaryCofan.mk ι₁ ι₂)) (m : CoequalizerMonoid.{w}) :
    ι₁ ≫ coequalizerMonoidEnd a b hW m = ι₁ :=
  inl_coequalizerMonoidEnd a b hW m

lemma mk_inr_coequalizerMonoidEnd_left {X : C} {ι₁ : Q ⟶ X} {ι₂ : P ⟶ X}
    (hW : IsColimit (BinaryCofan.mk ι₁ ι₂)) :
    ι₂ ≫ coequalizerMonoidEnd.{w} a b hW left = a ≫ ι₁ :=
  inr_coequalizerMonoidEnd_left a b hW

lemma mk_inr_coequalizerMonoidEnd_right {X : C} {ι₁ : Q ⟶ X} {ι₂ : P ⟶ X}
    (hW : IsColimit (BinaryCofan.mk ι₁ ι₂)) :
    ι₂ ≫ coequalizerMonoidEnd.{w} a b hW right = b ≫ ι₁ :=
  inr_coequalizerMonoidEnd_right a b hW

/-- The action of `CoequalizerMonoid` on `Q ⨿ P` by `σₗ = [inl, a ≫ inl]` and
`σᵣ = [inl, b ≫ inl]`. -/
def coequalizerDiagram : SingleObj CoequalizerMonoid.{w} ⥤ C where
  obj _ := W.pt
  map m := coequalizerMonoidEnd a b hW m
  map_id _ := rfl
  map_comp {_ _ _} m n := by
    rw [SingleObj.comp_as_mul]
    apply BinaryCofan.IsColimit.hom_ext hW
    · rw [← Category.assoc, inl_coequalizerMonoidEnd, inl_coequalizerMonoidEnd,
        inl_coequalizerMonoidEnd]
    · rw [← Category.assoc]
      cases m
      · change W.inr ≫ coequalizerMonoidEnd a b hW n = (W.inr ≫ 𝟙 _) ≫ _
        rw [Category.comp_id]
      · change W.inr ≫ coequalizerMonoidEnd a b hW left = _
        rw [inr_coequalizerMonoidEnd_left, Category.assoc, inl_coequalizerMonoidEnd]
      · change W.inr ≫ coequalizerMonoidEnd a b hW right = _
        rw [inr_coequalizerMonoidEnd_right, Category.assoc, inl_coequalizerMonoidEnd]

@[simp]
lemma coequalizerDiagram_map (m : CoequalizerMonoid.{w}) :
    (coequalizerDiagram a b hW).map (X := SingleObj.star _) (Y := SingleObj.star _) m =
      coequalizerMonoidEnd a b hW m :=
  rfl

variable {a b hW}

/-- The cofork of `a` and `b` attached to a cocone over the action on `Q ⨿ P`. -/
def coforkOfCocone (c : Cocone (coequalizerDiagram.{w} a b hW)) : Cofork a b :=
  Cofork.ofπ (W.inl ≫ c.ι.app (SingleObj.star _)) (by
    have hl := c.w (j := SingleObj.star _) (j' := SingleObj.star _) left
    have hr := c.w (j := SingleObj.star _) (j' := SingleObj.star _) right
    rw [coequalizerDiagram_map] at hl hr
    rw [← Category.assoc, ← inr_coequalizerMonoidEnd_left (hW := hW), Category.assoc, hl,
      ← Category.assoc, ← inr_coequalizerMonoidEnd_right (hW := hW), Category.assoc, hr])

/-- The cocone over the action on `Q ⨿ P` attached to a cofork of `a` and `b`. -/
def coconeOfCofork (s : Cofork a b) : Cocone (coequalizerDiagram.{w} a b hW) where
  pt := s.pt
  ι :=
    { app _ := hW.desc (BinaryCofan.mk s.π (a ≫ s.π))
      naturality _ _ m := by
        refine Eq.trans ?_ (Category.comp_id _).symm
        apply BinaryCofan.IsColimit.hom_ext hW
        · rw [← Category.assoc, coequalizerDiagram_map, inl_coequalizerMonoidEnd]
        · have h₁ : W.inr ≫ hW.desc (BinaryCofan.mk s.π (a ≫ s.π)) = a ≫ s.π :=
            hW.fac _ ⟨.right⟩
          have h₂ : W.inl ≫ hW.desc (BinaryCofan.mk s.π (a ≫ s.π)) = s.π := hW.fac _ ⟨.left⟩
          cases m
          · change W.inr ≫ 𝟙 _ ≫ _ = _
            rw [Category.id_comp]
          · rw [coequalizerDiagram_map, ← Category.assoc, inr_coequalizerMonoidEnd_left,
              Category.assoc, h₂, h₁]
          · rw [coequalizerDiagram_map, ← Category.assoc, inr_coequalizerMonoidEnd_right,
              Category.assoc, h₂, h₁, s.condition] }

/-- **The quotient of `Q ⨿ P` by the action of `CoequalizerMonoid` is a coequalizer of `a` and
`b`.** -/
def isColimitCoforkOfCocone {c : Cocone (coequalizerDiagram.{w} a b hW)} (hc : IsColimit c) :
    IsColimit (coforkOfCocone c) :=
  Cofork.IsColimit.mk _ (fun s ↦ hc.desc (coconeOfCofork s))
    (fun s ↦ by
      change (W.inl ≫ c.ι.app _) ≫ _ = _
      rw [Category.assoc, hc.fac]
      exact hW.fac _ ⟨.left⟩)
    (fun s m hm ↦ by
      apply hc.hom_ext
      rintro ⟨⟩
      rw [hc.fac]
      have hm' : W.inl ≫ c.ι.app (SingleObj.star _) ≫ m = s.π := by
        rw [← Category.assoc]
        exact hm
      apply BinaryCofan.IsColimit.hom_ext hW
      · change W.inl ≫ c.ι.app (SingleObj.star _) ≫ m =
          W.inl ≫ hW.desc (BinaryCofan.mk s.π (a ≫ s.π))
        exact hm'.trans (hW.fac (BinaryCofan.mk s.π (a ≫ s.π)) ⟨.left⟩).symm
      · have hl := c.w (j := SingleObj.star _) (j' := SingleObj.star _) left
        rw [coequalizerDiagram_map] at hl
        have hl' : W.inr ≫ c.ι.app (SingleObj.star _) =
            a ≫ W.inl ≫ c.ι.app (SingleObj.star _) := by
          conv_lhs => rw [← hl]
          rw [← Category.assoc, inr_coequalizerMonoidEnd_left, Category.assoc]
        change W.inr ≫ c.ι.app (SingleObj.star _) ≫ m =
          W.inr ≫ hW.desc (BinaryCofan.mk s.π (a ≫ s.π))
        rw [hW.fac (BinaryCofan.mk s.π (a ≫ s.π)) ⟨.right⟩, reassoc_of% hl', hm']
        rfl)

variable (C) in
/-- A category with binary coproducts and quotients by `CoequalizerMonoid` has coequalizers. -/
theorem hasCoequalizers_of_hasColimitsOfShape_singleObj [HasBinaryCoproducts C]
    [HasColimitsOfShape (SingleObj CoequalizerMonoid.{w}) C] : HasCoequalizers C :=
  ⟨fun K ↦ by
    let a := K.map WalkingParallelPairHom.left
    let b := K.map WalkingParallelPairHom.right
    let hW := coprodIsCoprod (K.obj WalkingParallelPair.one) (K.obj WalkingParallelPair.zero)
    have := HasColimit.mk ⟨_, isColimitCoforkOfCocone
      (colimit.isColimit (coequalizerDiagram.{w} a b hW))⟩
    exact hasColimit_of_iso (diagramIsoParallelPair K)⟩

/-- A functor preserving binary coproducts and quotients by `CoequalizerMonoid`, from a category
in which these exist, preserves coequalizers. -/
theorem preservesCoequalizers_of_preservesColimitsOfShape_singleObj {D : Type u'}
    [Category.{v'} D] [HasBinaryCoproducts C]
    [HasColimitsOfShape (SingleObj CoequalizerMonoid.{w}) C] (F : C ⥤ D)
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesColimitsOfShape (SingleObj CoequalizerMonoid.{w}) F] :
    PreservesColimitsOfShape WalkingParallelPair F := by
  have : ∀ {P Q : C} (a b : P ⟶ Q), PreservesColimit (parallelPair a b) F := fun {P Q} a b ↦ by
    let hW := coprodIsCoprod Q P
    let c := colimit.cocone (coequalizerDiagram.{w} a b hW)
    let hc := colimit.isColimit (coequalizerDiagram.{w} a b hW)
    let W' : BinaryCofan (F.obj Q) (F.obj P) := BinaryCofan.mk (F.map coprod.inl) (F.map coprod.inr)
    have hW' : IsColimit W' :=
      (isColimitMapCoconeBinaryCofanEquiv F _ _).1 (isColimitOfPreserves F hW)
    let e : coequalizerDiagram.{w} a b hW ⋙ F ≅ coequalizerDiagram.{w} (F.map a) (F.map b) hW' :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} m ↦ by
        change F.map (coequalizerMonoidEnd a b hW m) ≫ 𝟙 _ =
          𝟙 _ ≫ coequalizerMonoidEnd (F.map a) (F.map b) hW' m
        rw [Category.comp_id, Category.id_comp]
        apply BinaryCofan.IsColimit.hom_ext hW'
        · change F.map coprod.inl ≫ _ = F.map coprod.inl ≫ _
          rw [← F.map_comp, mk_inl_coequalizerMonoidEnd, mk_inl_coequalizerMonoidEnd]
        · change F.map coprod.inr ≫ _ = F.map coprod.inr ≫ _
          rw [← F.map_comp]
          cases m
          · change F.map (coprod.inr ≫ 𝟙 _) = F.map coprod.inr ≫ 𝟙 _
            rw [Category.comp_id, Category.comp_id]
          · rw [mk_inr_coequalizerMonoidEnd_left, mk_inr_coequalizerMonoidEnd_left, F.map_comp]
          · rw [mk_inr_coequalizerMonoidEnd_right, mk_inr_coequalizerMonoidEnd_right,
              F.map_comp])
    let hFc : IsColimit ((Cocone.precompose e.inv).obj (F.mapCocone c)) :=
      (IsColimit.precomposeInvEquiv e _).2 (isColimitOfPreserves F hc)
    refine preservesColimit_of_preserves_colimit_cocone (isColimitCoforkOfCocone hc) ?_
    refine (isColimitMapCoconeCoforkEquiv F _).2 ?_
    refine (isColimitCoforkOfCocone hFc).ofIsoColimit (Cofork.ext (Iso.refl _) ?_)
    change (F.map coprod.inl ≫ (𝟙 _ ≫ F.map (c.ι.app _))) ≫ 𝟙 _ = F.map (coprod.inl ≫ _)
    rw [Category.id_comp, Category.comp_id, F.map_comp]
  exact ⟨fun {K} ↦ preservesColimit_of_iso_diagram F (diagramIsoParallelPair K).symm⟩

end CategoryTheory.Limits
