/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Unit-normalized reflection of coefficient squares

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/prop-weil-pbc-scalar-extension.md, coherent comparisons;
Stacks Tags 0037, 07A7, 0DV0, 0E46 and 0E47.
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares).

The structures below only package the specified reflective subcategories,
adjunctions and coefficient squares. All constructions use Mathlib's full
subcategories, reflectors and mate correspondence. In particular, the mate is
never required to be invertible.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CategoryTheory.ReflectedCoefficient

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

/-- The specified full reflective, isomorphism-closed subcategory of local objects.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Context (C : Type u₀) [Category.{v₀} C] where
  /-- The local objects. -/
  localObjects : ObjectProperty C
  /-- Locality is invariant under isomorphism. -/
  closed : localObjects.IsClosedUnderIsomorphisms
  /-- The specified reflector and its adjunction to the full inclusion. -/
  reflective : Reflective localObjects.ι

attribute [instance] Context.closed Context.reflective

variable {C₀ : Type u₀} [Category.{v₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
  {C₅ : Type u₅} [Category.{v₅} C₅]

private theorem mate_formula {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀}
    {L' : C₂ ⥤ C₃} {R' : C₃ ⥤ C₂}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C₀ ⥤ C₂} {H : C₁ ⥤ C₃}
    (α : G ⋙ L' ⟶ L ⋙ H) (Z : C₁) :
    (mateEquiv adj adj' α).app Z =
      adj'.homEquiv _ _ (α.app (R.obj Z) ≫ H.map (adj.counit.app Z)) := by
  simp [mateEquiv, Adjunction.homEquiv_unit, Functor.map_comp]

/-- The specified reflector followed by the inclusion, denoted Λ in the node.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Context.completion (A : Context C₀) : C₀ ⥤ C₀ :=
  reflector A.localObjects.ι ⋙ A.localObjects.ι

/-- The unit η of the specified reflection.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Context.unit (A : Context C₀) : 𝟭 C₀ ⟶ A.completion :=
  (reflectorAdjunction A.localObjects.ι).unit

private theorem cancel_unit (A : Context C₀) (X : C₀)
    (Y : A.localObjects.FullSubcategory)
    {f g : A.completion.obj X ⟶ Y.obj}
    (h : A.unit.app X ≫ f = A.unit.app X ≫ g) : f = g := by
  dsimp only [Context.completion, Context.unit] at *
  exact (unitCompPartialBijectiveAux (i := A.localObjects.ι) X Y).symm.injective (by
    simpa only [unitCompPartialBijectiveAux_symm_apply] using h)

/-- An adjunction with a local-object-preserving right adjoint and normalized γ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Arrow (A : Context C₀) (B : Context C₁) where
  /-- The specified left adjoint. -/
  F : C₀ ⥤ C₁
  /-- The specified right adjoint. -/
  G : C₁ ⥤ C₀
  /-- The specified adjunction. -/
  adj : F ⊣ G
  /-- The right adjoint preserves local objects. -/
  preserves : ∀ Y, B.localObjects Y → A.localObjects (G.obj Y)
  /-- The specified completion comparison. -/
  gamma : G ⋙ A.completion ≅ B.completion ⋙ G
  /-- Normalization by the reflection units. -/
  gamma_unit : ∀ Y, A.unit.app (G.obj Y) ≫ gamma.hom.app Y = G.map (B.unit.app Y)

/-- Coefficient change with its specified unit-normalized comparison κ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Change (A : Context C₀) (B : Context C₁) where
  /-- The ambient coefficient functor. -/
  F : C₀ ⥤ C₁
  /-- The specified coefficient/reflection comparison. -/
  kappa : A.completion ⋙ F ≅ F ⋙ B.completion
  /-- Its reflection-unit normalization. -/
  kappa_unit : ∀ X, F.map (A.unit.app X) ≫ kappa.hom.app X = B.unit.app (F.obj X)

/-- Coefficient functors preserve local objects.

Proof: step 1. Locality is equivalent to invertibility of the unit. The
normalized κ expresses the target unit as a composite of isomorphisms.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Change.preserves {A : Context C₀} {B : Context C₁} (c : Change A B)
    (X : C₀) (hX : A.localObjects X) : B.localObjects (c.F.obj X) := by
  have hη : IsIso (A.unit.app X) :=
    Functor.essImage.unit_isIso (A.localObjects.ι.obj_mem_essImage ⟨X, hX⟩)
  have : IsIso (B.unit.app (c.F.obj X)) := by
    rw [← c.kappa_unit X]
    infer_instance
  exact B.localObjects.prop_of_iso (asIso (B.unit.app (c.F.obj X))).symm
    ((reflector B.localObjects.ι).obj (c.F.obj X)).property

/-- The restriction of a coefficient change, using its proved locality clause.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Change.restrict {A : Context C₀} {B : Context C₁} (c : Change A B) :
    A.localObjects.FullSubcategory ⥤ B.localObjects.FullSubcategory :=
  B.localObjects.lift (A.localObjects.ι ⋙ c.F) (fun X ↦ c.preserves X.obj X.property)

/-- The left adjoint on local inputs, followed by reflection in the target.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
abbrev Arrow.left {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    A.localObjects.FullSubcategory ⥤ B.localObjects.FullSubcategory :=
  A.localObjects.ι ⋙ a.F ⋙ reflector B.localObjects.ι

/-- The restriction of the right adjoint to the full local subcategories.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
abbrev Arrow.right {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    B.localObjects.FullSubcategory ⥤ A.localObjects.FullSubcategory :=
  A.localObjects.lift (B.localObjects.ι ⋙ a.G)
    (fun Y ↦ a.preserves Y.obj Y.property)

/-- Existence of the reflected adjunction with its specified Hom bijection.

Proof: step 2. Compose the fully faithful inclusion Hom bijections,
precomposition by the reflection unit, and the original adjunct. Reflection
into a local target makes the middle operation bijective. Naturality follows
from naturality of the unit and the original Hom bijection. Apply
Adjunction.mkOfHomEquiv (the natural-bijection dependency).

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.adjunction_exists {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    ∃ h : a.left ⊣ a.right, ∀ (X : A.localObjects.FullSubcategory)
      (Y : B.localObjects.FullSubcategory) (t : a.left.obj X ⟶ Y),
      A.localObjects.ι.map (h.homEquiv X Y t) =
        a.adj.homEquiv X.obj Y.obj
          (B.unit.app (a.F.obj X.obj) ≫ B.localObjects.ι.map t) := by
  let h : a.left ⊣ a.right :=
    (a.adj.comp (reflectorAdjunction B.localObjects.ι)).restrictFullyFaithful
      A.localObjects.fullyFaithfulι (Functor.FullyFaithful.id _)
      (Iso.refl _) (Iso.refl _)
  refine ⟨h, ?_⟩
  intro X Y t
  simp [h, Adjunction.restrictFullyFaithful, Adjunction.comp_homEquiv,
    Functor.FullyFaithful.homEquiv, Context.unit]
  rfl

/-- The adjunction determined uniquely by the displayed Hom bijections.
The postponed existence theorem determines the entire adjunction, rather than
choosing arbitrary data from a mere existence assertion.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.reflectedAdjunction {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    a.left ⊣ a.right :=
  Classical.choose a.adjunction_exists

private theorem reflected_hom {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    (X : A.localObjects.FullSubcategory) (Y : B.localObjects.FullSubcategory)
    (t : a.left.obj X ⟶ Y) :
    A.localObjects.ι.map (a.reflectedAdjunction.homEquiv X Y t) =
      a.adj.homEquiv X.obj Y.obj
        (B.unit.app (a.F.obj X.obj) ≫ B.localObjects.ι.map t) :=
  Classical.choose_spec a.adjunction_exists X Y t

private theorem reflected_unit {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    (X : A.localObjects.FullSubcategory) :
    A.localObjects.ι.map (a.reflectedAdjunction.unit.app X) =
      a.adj.unit.app X.obj ≫ a.G.map (B.unit.app (a.F.obj X.obj)) := by
  have h := reflected_hom a X (a.left.obj X) (𝟙 _)
  rw [Adjunction.homEquiv_id] at h
  change A.localObjects.ι.map (a.reflectedAdjunction.unit.app X) =
    a.adj.homEquiv X.obj (a.left.obj X).obj (B.unit.app _ ≫ 𝟙 _) at h
  simpa only [Category.comp_id, Adjunction.homEquiv_unit] using h

private theorem reflected_counit {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    (Y : B.localObjects.FullSubcategory) :
    B.unit.app (a.F.obj (a.G.obj Y.obj)) ≫
      B.localObjects.ι.map (a.reflectedAdjunction.counit.app Y) =
        a.adj.counit.app Y.obj := by
  have he : a.reflectedAdjunction.homEquiv (a.right.obj Y) Y
      (a.reflectedAdjunction.counit.app Y) = 𝟙 _ := by
    rw [← a.reflectedAdjunction.homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  have he' : a.adj.homEquiv (a.G.obj Y.obj) Y.obj (a.adj.counit.app Y.obj) = 𝟙 _ := by
    rw [← a.adj.homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  apply (a.adj.homEquiv _ _).injective
  exact (reflected_hom a (a.right.obj Y) Y
    (a.reflectedAdjunction.counit.app Y)).symm.trans
      ((congrArg A.localObjects.ι.map he).trans
        ((A.localObjects.ι.map_id _).trans he'.symm))

private theorem kappa_unit_inv {A : Context C₀} {B : Context C₁} (c : Change A B)
    (X : C₀) :
    B.unit.app (c.F.obj X) ≫ c.kappa.inv.app X = c.F.map (A.unit.app X) := by
  rw [← c.kappa_unit]
  simp

/-- A coefficient square of the two specified left adjoints.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Square {A₀ : Context C₀} {B₀ : Context C₁}
    {A₁ : Context C₂} {B₁ : Context C₃}
    (a₀ : Arrow A₀ B₀) (a₁ : Arrow A₁ B₁)
    (cA : Change A₀ A₁) (cB : Change B₀ B₁) where
  /-- The specified left comparison δ. -/
  delta : cA.F ⋙ a₁.F ≅ a₀.F ⋙ cB.F

variable {A₀ : Context C₀} {B₀ : Context C₁}
  {A₁ : Context C₂} {B₁ : Context C₃}
  {a₀ : Arrow A₀ B₀} {a₁ : Arrow A₁ B₁}
  {cA : Change A₀ A₁} {cB : Change B₀ B₁}

/-- The ambient right mate β, using the dependency CategoryTheory.mateEquiv.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.beta (s : Square a₀ a₁ cA cB) : a₀.G ⋙ cA.F ⟶ cB.F ⋙ a₁.G :=
  mateEquiv a₀.adj a₁.adj s.delta.hom

/-- The ambient formula κ_B⁻¹ Λ_B(δ) whose restriction is the reflected square.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.comparison (s : Square a₀ a₁ cA cB) :
    cA.F ⋙ a₁.F ⋙ B₁.completion ≅ a₀.F ⋙ B₀.completion ⋙ cB.F :=
  isoWhiskerRight s.delta B₁.completion ≪≫ isoWhiskerLeft a₀.F cB.kappa.symm

private theorem comparison_unit (s : Square a₀ a₁ cA cB) (X : C₀) :
    B₁.unit.app (a₁.F.obj (cA.F.obj X)) ≫ s.comparison.hom.app X =
      s.delta.hom.app X ≫ cB.F.map (B₀.unit.app (a₀.F.obj X)) := by
  change B₁.unit.app _ ≫ B₁.completion.map (s.delta.hom.app X) ≫
    cB.kappa.inv.app _ = _
  rw [← Category.assoc, ← B₁.unit.naturality, Category.assoc]
  exact congrArg (s.delta.hom.app X ≫ ·) (kappa_unit_inv cB _)

/-- Naturality needed to construct the local comparison from its ambient formula.

Proof: step 3. Both components are lifted by the full inclusion; apply
faithfulness to the ambient comparison naturality equation.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.comparison_naturality (s : Square a₀ a₁ cA cB)
    (X Y : A₀.localObjects.FullSubcategory) (f : X ⟶ Y) :
    (cA.restrict ⋙ a₁.left).map f ≫
        (B₁.localObjects.isoMk (s.comparison.app Y.obj)).hom =
      (B₁.localObjects.isoMk (s.comparison.app X.obj)).hom ≫
        (a₀.left ⋙ cB.restrict).map f := by
  apply B₁.localObjects.ι.map_injective
  exact s.comparison.hom.naturality (A₀.localObjects.ι.map f)

/-- The canonical comparison on local objects, with actual isomorphism data.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.localComparison (s : Square a₀ a₁ cA cB) :
    cA.restrict ⋙ a₁.left ≅ a₀.left ⋙ cB.restrict :=
  NatIso.ofComponents (fun X ↦ B₁.localObjects.isoMk (s.comparison.app X.obj))
    (fun {X Y} f ↦ s.comparison_naturality X Y f)

/-- The reflected coefficient square has exactly the restricted ambient right mate.

Proof: steps 3 and 4. The comparison satisfies δhat k₁=C_B(k₀)δ by
naturality of η and normalization of κ. The reflected counit satisfies
ehat k=e by the specified Hom bijection. Thus the reflected transpose, after
precomposition by k₁, is C_B(e₀)δ, whose ordinary adjunct is β. The Hom
bijection defining the reflected adjunction proves the claimed equality;
no invertibility of β is used.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.mate (s : Square a₀ a₁ cA cB)
    (Y : B₀.localObjects.FullSubcategory) :
    A₁.localObjects.ι.map
        ((mateEquiv a₀.reflectedAdjunction a₁.reflectedAdjunction
          s.localComparison.hom).app Y) = s.beta.app Y.obj := by
  have hm := reflected_hom a₁ (cA.restrict.obj (a₀.right.obj Y))
    (cB.restrict.obj Y)
    (s.localComparison.hom.app (a₀.right.obj Y) ≫
      cB.restrict.map (a₀.reflectedAdjunction.counit.app Y))
  rw [mate_formula]
  refine hm.trans ?_
  unfold Square.beta
  rw [mate_formula]
  congr 1
  change B₁.unit.app _ ≫ s.comparison.hom.app _ ≫
    cB.F.map (B₀.localObjects.ι.map (a₀.reflectedAdjunction.counit.app Y)) = _
  rw [← Category.assoc, comparison_unit, Category.assoc, ← cB.F.map_comp]
  exact congrArg (fun f ↦ s.delta.hom.app (a₀.G.obj Y.obj) ≫ cB.F.map f)
    (reflected_counit a₀ Y)

/-- The ambient γ/κ normalization equation, including nonlocal inputs.

Proof: step 5. Both sides target the local object G₁C_BΛ₀M.
Precomposition with C_A(η₀) is injective by κ_A and reflection. After
precomposition, γ₀ normalization and β naturality give G₁C_B(η₀)β
on the left. On the right use κ_A normalization, η₁ naturality, γ₁
normalization, then κ_B normalization to obtain the same map.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.normalization (s : Square a₀ a₁ cA cB) (M : C₁) :
    cA.F.map (a₀.gamma.hom.app M) ≫ s.beta.app (B₀.completion.obj M) =
      cA.kappa.hom.app (a₀.G.obj M) ≫ A₁.completion.map (s.beta.app M) ≫
        a₁.gamma.hom.app (cB.F.obj M) ≫ a₁.G.map (cB.kappa.inv.app M) := by
  apply (cancel_epi (cA.kappa.inv.app (a₀.G.obj M))).mp
  apply cancel_unit A₁ _
    ⟨_, a₁.preserves _ (cB.preserves _ ((reflector B₀.localObjects.ι).obj M).property)⟩
  simp only [← Category.assoc, kappa_unit_inv]
  rw [← cA.F.map_comp, a₀.gamma_unit]
  rw [show cA.F.map (a₀.G.map (B₀.unit.app M)) ≫
      s.beta.app (B₀.completion.obj M) =
      s.beta.app M ≫ a₁.G.map (cB.F.map (B₀.unit.app M)) from
    s.beta.naturality (B₀.unit.app M)]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, cA.kappa_unit]
  simp only [Category.assoc]
  rw [← A₁.unit.naturality_assoc]
  dsimp only [Functor.comp_obj, Functor.id_map]
  rw [reassoc_of% (a₁.gamma_unit (cB.F.obj M))]
  rw [← a₁.G.map_comp, kappa_unit_inv]

variable {A₂ : Context C₄} {B₂ : Context C₅}
  {a₂ : Arrow A₂ B₂} {dA : Change A₁ A₂} {dB : Change B₁ B₂}

/-- The composite coefficient comparison is unit-normalized.

Proof: step 6. Apply D to the normalization for C, and then use the
normalization for D at C X. Functoriality gives the stated equation.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Change.comp_kappa_unit
    {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (c : Change A B) (d : Change B D) (X : C₀) :
    d.F.map (c.F.map (A.unit.app X)) ≫
      d.F.map (c.kappa.hom.app X) ≫ d.kappa.hom.app (c.F.obj X) =
        D.unit.app (d.F.obj (c.F.obj X)) := by
  rw [← d.F.map_comp_assoc, c.kappa_unit, d.kappa_unit]

/-- The specified composite coefficient data: κ_DC=κ_D D(κ_C).

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Change.comp {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (c : Change A B) (d : Change B D) : Change A D where
  F := c.F ⋙ d.F
  kappa := isoWhiskerRight c.kappa d.F ≪≫ isoWhiskerLeft c.F d.kappa
  kappa_unit := c.comp_kappa_unit d

/-- The specified coefficient squares paste by whiskering their δ isomorphisms.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.coefficientComp (s : Square a₀ a₁ cA cB)
    (t : Square a₁ a₂ dA dB) : Square a₀ a₂ (cA.comp dA) (cB.comp dB) where
  delta := isoWhiskerLeft cA.F t.delta ≪≫ isoWhiskerRight s.delta dB.F

/-- The composite completion comparison has the required unit normalization.

Proof: step 9. Substitute γ_G η_A=G(η_B), then naturality and
γ_J η_B=J(η_D). Functoriality gives GJ(η_D).

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.comp_gamma_unit {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D) (M : C₂) :
    A.unit.app (a.G.obj (h.G.obj M)) ≫
      a.gamma.hom.app (h.G.obj M) ≫ a.G.map (h.gamma.hom.app M) =
        a.G.map (h.G.map (D.unit.app M)) := by
  rw [← Category.assoc, a.gamma_unit, ← a.G.map_comp, h.gamma_unit]

/-- The specified composite adjunction and normalized completion comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.comp {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D) : Arrow A D where
  F := a.F ⋙ h.F
  G := h.G ⋙ a.G
  adj := a.adj.comp h.adj
  preserves Y hY := a.preserves _ (h.preserves Y hY)
  gamma := isoWhiskerLeft h.G a.gamma ≪≫ isoWhiskerRight h.gamma a.G
  gamma_unit := a.comp_gamma_unit h

/-- The comparison q=Λ_D H(η_B F) between reflecting before and after
composition. This is actual canonical morphism data, not an arbitrary iso.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.compositionComparison {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D) :
    a.F ⋙ h.F ⋙ D.completion ⟶ a.F ⋙ B.completion ⋙ h.F ⋙ D.completion :=
  whiskerRight (whiskerLeft a.F B.unit) (h.F ⋙ D.completion)

/-- Repeated coefficient composition is associative with its specified κ.

Proof: step 9. Expand the composite κ formula. Functoriality and
associativity of morphism composition give the same iterated product.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Change.associativity
    {A : Context C₀} {B : Context C₁} {D : Context C₂} {E : Context C₃}
    (c : Change A B) (d : Change B D) (e : Change D E) (X : C₀) :
    ((c.comp d).comp e).kappa.hom.app X = (c.comp (d.comp e)).kappa.hom.app X := by
  simp [Change.comp]

/-- Repeated adjunction pasting gives the same normalized comparisons and
Hom bijections for either parenthesization.

Proof: steps 7 and 9. Naturality of the D reflection unit applied to
H(k) proves the q equality, or equivalently test both sides by their
composite Hom bijections. Expansion and functoriality prove the γ
equality. Adjunction.comp has Hom bijection the composite of functions,
which is associative. These normalizations together with the two binary
pasting theorems give the asserted iterated square coherence.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.associativity
    {A : Context C₀} {B : Context C₁} {D : Context C₂} {E : Context C₃}
    (a : Arrow A B) (h : Arrow B D) (k : Arrow D E)
    (X : A.localObjects.FullSubcategory) (Y : C₃) :
    (((a.comp h).compositionComparison k).app X.obj ≫
      E.completion.map (k.F.map ((a.compositionComparison h).app X.obj)) =
        (a.compositionComparison (h.comp k)).app X.obj ≫
          (h.compositionComparison k).app (B.completion.obj (a.F.obj X.obj))) ∧
    (((a.comp h).comp k).gamma.hom.app Y = (a.comp (h.comp k)).gamma.hom.app Y) ∧
    ∀ (t : k.F.obj (h.F.obj (a.F.obj X.obj)) ⟶ Y),
      ((a.comp h).comp k).adj.homEquiv X.obj Y t =
        (a.comp (h.comp k)).adj.homEquiv X.obj Y t := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Arrow.compositionComparison, Arrow.comp]
    rw [← E.completion.map_comp, ← k.F.map_comp]
    rw [← D.unit.naturality]
    simp only [Functor.id_map, Functor.map_comp]
  · simp [Arrow.comp]
  · intro t
    simp only [Arrow.comp, Adjunction.comp_homEquiv]
    rfl

/-- The identity coefficient data, with literal identity functor.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Change.id (A : Context C₀) : Change A A where
  F := 𝟭 C₀
  kappa := Iso.refl A.completion
  kappa_unit X := Category.comp_id (A.unit.app X)

/-- The identity coefficient square of a specified adjunction.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.id {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    Square a a (Change.id A) (Change.id B) where
  delta := Iso.refl a.F

/-- Identity coefficient squares give identity comparisons on both sides.

Proof: step 9. The comparison precomposed with k is k, so reflection
uniqueness gives the identity. The identity clause of mate-pasting gives
the identity right mate. The same unit test proves iterated identity laws.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.identity {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    (X : A.localObjects.FullSubcategory) (Y : C₁) :
    (Square.id a).comparison.hom.app X.obj = 𝟙 _ ∧
      (Square.id a).beta.app Y = 𝟙 _ := by
  constructor
  · simp [Square.id, Square.comparison, Change.id]
  · simp [Square.beta, Square.id, Change.id, mateEquiv]

/-- The identity adjunction with its literal functors and normalized γ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.id (A : Context C₀) : Arrow A A where
  F := 𝟭 C₀
  G := 𝟭 C₀
  adj := Adjunction.id
  preserves _ h := h
  gamma := Iso.refl A.completion
  gamma_unit X := Category.comp_id (A.unit.app X)

/-- The identity adjunction reflects to the identity under η_X⁻¹.

Proof: step 9. Locality makes η_X invertible. The reflected identity
Hom bijection is precomposition by η_X, so its unit is η_X and its
counit is its inverse; this gives the normalized identity comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.identity {A : Context C₀} (X : A.localObjects.FullSubcategory) :
    IsIso (A.unit.app X.obj) ∧
    A.localObjects.ι.map ((Arrow.id A).reflectedAdjunction.unit.app X) =
      A.unit.app X.obj ∧
    A.unit.app X.obj ≫
      A.localObjects.ι.map ((Arrow.id A).reflectedAdjunction.counit.app X) = 𝟙 _ := by
  refine ⟨?_, ?_, ?_⟩
  · exact Functor.essImage.unit_isIso (A.localObjects.ι.obj_mem_essImage X)
  · simpa [Arrow.id] using reflected_unit (Arrow.id A) X
  · simpa [Arrow.id] using reflected_counit (Arrow.id A) X

/-- Local objects are stable under all specified shifts.

Proof: step 10. The shift comparison of Λ and compatibility of η
identify η_(X[a]) with the shifted invertible unit η_X. Thus X[a] is
local by the locality criterion from step 1.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Context.stableUnderShift (A : Context C₀) [HasShift C₀ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ] :
    A.localObjects.IsStableUnderShift ℤ := by
  constructor
  intro n
  constructor
  intro X hX
  have : IsIso (A.unit.app X) :=
    Functor.essImage.unit_isIso (A.localObjects.ι.obj_mem_essImage ⟨X, hX⟩)
  have hn : A.unit.app (X⟦n⟧) =
      (A.unit.app X)⟦n⟧' ≫ (A.completion.commShiftIso n).inv.app X := by
    simpa using NatTrans.app_shift A.unit n X
  have : IsIso (A.unit.app (X⟦n⟧)) := by
    rw [hn]
    infer_instance
  exact A.localObjects.prop_of_iso (asIso (A.unit.app (X⟦n⟧))).symm
    ((reflector A.localObjects.ι).obj (X⟦n⟧)).property

attribute [instance] Context.stableUnderShift

/-- The reflector commutes with shifts by fully faithful transport from Λ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Context.reflectorCommShift (A : Context C₀) [HasShift C₀ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ] :
    (reflector A.localObjects.ι).CommShift ℤ :=
  Functor.CommShift.ofComp (Iso.refl A.completion) ℤ

/-- The reflected left functor has the composite specified shift comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Arrow.leftCommShift {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] [a.F.CommShift ℤ] :
    a.left.CommShift ℤ :=
  inferInstanceAs ((A.localObjects.ι ⋙ a.F ⋙ reflector B.localObjects.ι).CommShift ℤ)

/-- The restricted right functor carries the shift comparison induced by G.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Arrow.rightCommShift {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] [a.G.CommShift ℤ] :
    a.right.CommShift ℤ :=
  inferInstanceAs ((A.localObjects.lift (B.localObjects.ι ⋙ a.G)
    (fun Y ↦ a.preserves Y.obj Y.property)).CommShift ℤ)

/-- Restricted coefficient changes carry the specified composite shift comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Change.restrictCommShift {A : Context C₀} {B : Context C₁} (c : Change A B)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] [c.F.CommShift ℤ] :
    c.restrict.CommShift ℤ :=
  inferInstanceAs ((B.localObjects.lift (A.localObjects.ι ⋙ c.F)
    (fun X ↦ c.preserves X.obj X.property)).CommShift ℤ)

private theorem commShift_of_whiskerRight
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} [I.Faithful]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [I.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift (whiskerRight τ I) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  ext X
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app (G.obj X))).mp
  have ht := NatTrans.shift_app_comm (whiskerRight τ I) n X
  simpa only [Functor.commShiftIso_comp_hom_app, whiskerRight_app,
    NatTrans.comp_app, whiskerLeft_app, Functor.map_comp, Category.assoc,
    ← Functor.commShiftIso_hom_naturality] using ht

private theorem commShift_of_comparison
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} [I.Faithful] {F' G' : C₀ ⥤ C₂}
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [I.CommShift ℤ]
    [F'.CommShift ℤ] [G'.CommShift ℤ]
    (τ : F ⟶ G) (eF : F ⋙ I ≅ F') (eG : G ⋙ I ≅ G')
    [NatTrans.CommShift eF.hom ℤ] [NatTrans.CommShift eG.hom ℤ]
    (σ : F' ⟶ G') [NatTrans.CommShift σ ℤ]
    (h : whiskerRight τ I = eF.hom ≫ σ ≫ eG.inv) : NatTrans.CommShift τ ℤ := by
  have : NatTrans.CommShift (whiskerRight τ I) ℤ := by
    rw [h]
    infer_instance
  exact commShift_of_whiskerRight (I := I) τ

private def completionInclusion (A : Context C₀) :
    reflector A.localObjects.ι ⋙ A.localObjects.ι ≅ A.completion := Iso.refl _

private def leftInclusion {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    a.left ⋙ B.localObjects.ι ≅ A.localObjects.ι ⋙ a.F ⋙ B.completion :=
  associator A.localObjects.ι (a.F ⋙ reflector B.localObjects.ι) B.localObjects.ι ≪≫
    isoWhiskerLeft A.localObjects.ι
      (associator a.F (reflector B.localObjects.ι) B.localObjects.ι ≪≫
        isoWhiskerLeft a.F (completionInclusion B))

private theorem leftInclusion_shift {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] [a.F.CommShift ℤ] :
    NatTrans.CommShift (leftInclusion a).hom ℤ := by
  have : NatTrans.CommShift (completionInclusion B).hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := reflector B.localObjects.ι)
      (G := B.localObjects.ι) (completionInclusion B) ℤ
  dsimp only [leftInclusion, Iso.trans_hom, isoWhiskerLeft_hom]
  simp only [whiskerLeft_comp]
  infer_instance

private def rightInclusion {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    a.right ⋙ A.localObjects.ι ≅ B.localObjects.ι ⋙ a.G :=
  A.localObjects.liftCompιIso (B.localObjects.ι ⋙ a.G)
    (fun Y ↦ a.preserves Y.obj Y.property)

private def changeInclusion {A : Context C₀} {B : Context C₁} (c : Change A B) :
    c.restrict ⋙ B.localObjects.ι ≅ A.localObjects.ι ⋙ c.F :=
  B.localObjects.liftCompιIso (A.localObjects.ι ⋙ c.F)
    (fun X ↦ c.preserves X.obj X.property)

/-- The reflected adjunction respects the specified shifts.

Proof: step 10. Its unit is G(k)u, which commutes with shifts by the
closure dependency. The adjunction-shift dependency, clause (i), gives
compatibility of the counit from that of the unit.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.reflectedAdjunction_commShift {A : Context C₀} {B : Context C₁}
    (a : Arrow A B) [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ]
    [a.F.CommShift ℤ] [a.G.CommShift ℤ] [a.adj.CommShift ℤ] :
    a.reflectedAdjunction.CommShift ℤ := by
  have hl := leftInclusion_shift a
  have hr : NatTrans.CommShift (rightInclusion a).hom ℤ := by
    dsimp [rightInclusion]
    infer_instance
  let e := associator a.left a.right A.localObjects.ι ≪≫
    isoWhiskerLeft a.left (rightInclusion a) ≪≫
    (associator a.left B.localObjects.ι a.G).symm ≪≫
    isoWhiskerRight (leftInclusion a) a.G
  have he : NatTrans.CommShift e.hom ℤ := by
    dsimp only [e, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  let σ := A.localObjects.ι.rightUnitor.inv ≫
    whiskerLeft A.localObjects.ι a.adj.unit ≫
    (associator A.localObjects.ι a.F a.G).inv ≫
    whiskerRight (A.localObjects.ι ⋙ a.F).rightUnitor.inv a.G ≫
    whiskerRight (whiskerLeft (A.localObjects.ι ⋙ a.F) B.unit) a.G ≫
    whiskerRight (associator A.localObjects.ι a.F B.completion).hom a.G
  have hσ : NatTrans.CommShift σ ℤ := by
    dsimp only [σ]
    infer_instance
  apply Adjunction.CommShift.mk'
  apply commShift_of_comparison a.reflectedAdjunction.unit
    A.localObjects.ι.leftUnitor e σ
  ext X
  suffices ht : (a.reflectedAdjunction.unit.app X).hom =
      a.adj.unit.app X.obj ≫ a.G.map (B.unit.app (a.F.obj X.obj)) ≫
        a.G.map (𝟙 (B.completion.obj (a.F.obj X.obj))) by
    simpa [e, σ, leftInclusion, rightInclusion, completionInclusion,
      ObjectProperty.liftCompιIso, Context.completion] using ht
  rw [a.G.map_id, Category.comp_id]
  exact reflected_unit a X

private theorem mate_shift {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀}
    {L' : C₂ ⥤ C₃} {R' : C₃ ⥤ C₂}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C₀ ⥤ C₂} {H : C₁ ⥤ C₃}
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
    [G.CommShift ℤ] [H.CommShift ℤ] [adj.CommShift ℤ] [adj'.CommShift ℤ]
    (δ : G ⋙ L' ⟶ L ⋙ H) [NatTrans.CommShift δ ℤ] :
    NatTrans.CommShift (mateEquiv adj adj' δ) ℤ := by
  dsimp only [mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk]
  infer_instance

/-- The reflected coefficient comparison and its right mate respect shifts.

Proof: step 10. Inverses of shift-compatible isomorphisms are compatible
by cancelling the isomorphism in the shift square. Composition and
whiskering preserve compatibility. Apply these rules to κ_B⁻¹Λ_Bδ
and to the unit-square-counit formula defining β. Fully faithful
restriction gives the same conclusion for the local comparison and its
mate, since the reflected adjunctions commute with shifts.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.commShift (s : Square a₀ a₁ cA cB)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    [A₀.completion.CommShift ℤ] [NatTrans.CommShift A₀.unit ℤ]
    [B₀.completion.CommShift ℤ] [NatTrans.CommShift B₀.unit ℤ]
    [A₁.completion.CommShift ℤ] [NatTrans.CommShift A₁.unit ℤ]
    [B₁.completion.CommShift ℤ] [NatTrans.CommShift B₁.unit ℤ]
    [a₀.F.CommShift ℤ] [a₀.G.CommShift ℤ] [a₀.adj.CommShift ℤ]
    [a₁.F.CommShift ℤ] [a₁.G.CommShift ℤ] [a₁.adj.CommShift ℤ]
    [cA.F.CommShift ℤ] [cB.F.CommShift ℤ]
    [NatTrans.CommShift cA.kappa.hom ℤ] [NatTrans.CommShift cB.kappa.hom ℤ]
    [NatTrans.CommShift a₀.gamma.hom ℤ] [NatTrans.CommShift a₁.gamma.hom ℤ]
    [NatTrans.CommShift s.delta.hom ℤ] :
    NatTrans.CommShift s.comparison.hom ℤ ∧ NatTrans.CommShift s.beta ℤ ∧
      NatTrans.CommShift s.localComparison.hom ℤ ∧
      NatTrans.CommShift
        (mateEquiv a₀.reflectedAdjunction a₁.reflectedAdjunction
          s.localComparison.hom) ℤ := by
  let τ := (associator cA.F a₁.F B₁.completion).inv ≫
    whiskerRight s.delta.hom B₁.completion ≫
    (associator a₀.F cB.F B₁.completion).hom ≫ whiskerLeft a₀.F cB.kappa.inv
  have hτ : NatTrans.CommShift τ ℤ := by
    dsimp only [τ]
    infer_instance
  have hc : NatTrans.CommShift s.comparison.hom ℤ := by
    convert hτ using 1
    ext X
    simp [τ, Square.comparison]
  have hb : NatTrans.CommShift s.beta ℤ := mate_shift a₀.adj a₁.adj s.delta.hom
  have hl₀ := leftInclusion_shift a₀
  have hl₁ := leftInclusion_shift a₁
  have hA : NatTrans.CommShift (changeInclusion cA).hom ℤ := by
    dsimp [changeInclusion]
    infer_instance
  have hB : NatTrans.CommShift (changeInclusion cB).hom ℤ := by
    dsimp [changeInclusion]
    infer_instance
  let e₁ := associator cA.restrict a₁.left B₁.localObjects.ι ≪≫
    isoWhiskerLeft cA.restrict (leftInclusion a₁) ≪≫
    (associator cA.restrict A₁.localObjects.ι (a₁.F ⋙ B₁.completion)).symm ≪≫
    isoWhiskerRight (changeInclusion cA) (a₁.F ⋙ B₁.completion) ≪≫
    associator A₀.localObjects.ι cA.F (a₁.F ⋙ B₁.completion)
  let e₀ := associator a₀.left cB.restrict B₁.localObjects.ι ≪≫
    isoWhiskerLeft a₀.left (changeInclusion cB) ≪≫
    (associator a₀.left B₀.localObjects.ι cB.F).symm ≪≫
    isoWhiskerRight (leftInclusion a₀) cB.F ≪≫
    associator A₀.localObjects.ι (a₀.F ⋙ B₀.completion) cB.F ≪≫
    isoWhiskerLeft A₀.localObjects.ι (associator a₀.F B₀.completion cB.F)
  have he₁ : NatTrans.CommShift e₁.hom ℤ := by
    dsimp only [e₁, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  have he₀ : NatTrans.CommShift e₀.hom ℤ := by
    dsimp only [e₀, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  have hl : NatTrans.CommShift s.localComparison.hom ℤ := by
    apply commShift_of_comparison s.localComparison.hom e₁ e₀
      (whiskerLeft A₀.localObjects.ι s.comparison.hom)
    ext X
    simp [e₁, e₀, leftInclusion, changeInclusion, completionInclusion,
      ObjectProperty.liftCompιIso, Square.localComparison, Context.completion,
      Change.restrict]
  have := a₀.reflectedAdjunction_commShift
  have := a₁.reflectedAdjunction_commShift
  exact ⟨hc, hb, hl, mate_shift a₀.reflectedAdjunction a₁.reflectedAdjunction
    s.localComparison.hom⟩

end CategoryTheory.ReflectedCoefficient
