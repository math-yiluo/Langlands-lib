/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.LinearScalarLocalization

/-!
# Scalar localization of a linear category

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi`, displayed Hom formula
(blueprint: def-weil-linear-scalar-localization).

The scalar-first tensor order agrees with `LinearMap.baseChange`; `TensorProduct.comm`
identifies it with the Hom-first order in the source. Objects are wrapped only to keep
this category's instances separate from the original category's instances.
Composition is selected from the unique bilinear extension in
`exists_linear_scalarLocalization_category`, not from its unspecified category witness.
-/

@[expose] public section

universe r u v

open TensorProduct

namespace CategoryTheory

variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (p : R)

/-- The unchanged objects of the raw scalar localization. Source: blueprint
`def-weil-rationalization-karoubi` (blueprint: def-weil-linear-scalar-localization). -/
structure ScalarLocalization (R : Type r) (C : Type u) (p : R) where
  /-- The corresponding original object. -/
  obj : C

namespace ScalarLocalization

/-- The unique extended bilinear composition. Source: blueprint
`def-weil-rationalization-karoubi` (blueprint: def-weil-linear-scalar-localization).
Its defining pure-tensor formula determines the entire linear map uniquely. -/
noncomputable def composition (K L M : C) :
    (Localization.Away p ⊗[R] (L ⟶ M)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (K ⟶ M)) :=
  Classical.choose ((exists_linear_scalarLocalization_category R C p).1 K L M).exists

/-- Composition has the specified pure-tensor formula. Source: blueprint
`def-weil-rationalization-karoubi` (blueprint: def-weil-linear-scalar-localization).
Proof: apply the specification of the unique bilinear extension in
`lem-weil-linear-scalar-localization-category` to the chosen composition. -/
theorem composition_tmul (K L M : C) (f : L ⟶ M) (g : K ⟶ L)
    (a b : Localization.Away p) :
    composition R C p K L M (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) =
      (a * b) ⊗ₜ[R] (g ≫ f) := by
  exact Classical.choose_spec
    ((exists_linear_scalarLocalization_category R C p).1 K L M).exists f g a b

/-- Associativity and identity laws for the uniquely specified composition.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization).
Proof: use `composition_tmul` on pure tensors. The two identity equations reduce to
identity laws in C and multiplication by one. Associativity reduces to associativity
in C and the localized ring. Extend each equation to sums of pure tensors using the
bilinearity from `lem-weil-linear-scalar-localization-category`. -/
theorem composition_laws :
    (∀ (K L : C) (f : Localization.Away p ⊗[R] (K ⟶ L)),
      composition R C p K K L f ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) = f) ∧
    (∀ (K L : C) (f : Localization.Away p ⊗[R] (K ⟶ L)),
      composition R C p K L L ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 L) f = f) ∧
    (∀ (K L M N : C) (f : Localization.Away p ⊗[R] (K ⟶ L))
        (g : Localization.Away p ⊗[R] (L ⟶ M))
        (h : Localization.Away p ⊗[R] (M ⟶ N)),
      composition R C p K M N h (composition R C p K L M g f) =
        composition R C p K L N (composition R C p L M N h g) f) := by
  constructor
  · intro K L f
    induction f using TensorProduct.inductionOn with
    | tmul a f => simp [composition_tmul]
    | add f g hf hg => simp [map_add, hf, hg]
  constructor
  · intro K L f
    induction f using TensorProduct.inductionOn with
    | tmul a f => simp [composition_tmul]
    | add f g hf hg => simp [map_add, hf, hg]
  · intro K L M N f g h
    induction h using TensorProduct.inductionOn with
    | tmul c h =>
      induction g using TensorProduct.inductionOn with
      | tmul b g =>
        induction f using TensorProduct.inductionOn with
        | tmul a f => simp [composition_tmul, Category.assoc, mul_assoc]
        | add f f' hf hf' => simp [map_add, hf, hf']
      | add g g' hg hg' => simp [map_add, hg, hg']
    | add h h' hh hh' => simp [map_add, hh, hh']

/-- The tensor Hom type, named before the category instance to share its reduction.
Source: the displayed Hom formula of `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
@[reducible] def tensorHom (K L : ScalarLocalization R C p) : Type (max r v) :=
  Localization.Away p ⊗[R] (K.obj ⟶ L.obj)

/-- The tensor-Hom category, with identities tensored with one and extended composition.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance category : Category.{max r v} (ScalarLocalization R C p) where
  Hom K L := tensorHom R C p K L
  id K := (1 : Localization.Away p) ⊗ₜ[R] 𝟙 K.obj
  comp {K L M} f g := composition R C p K.obj L.obj M.obj g f
  id_comp {K L} f := (composition_laws R C p).1 K.obj L.obj f
  comp_id {K L} f := (composition_laws R C p).2.1 K.obj L.obj f
  assoc {K L M N} f g h := (composition_laws R C p).2.2 K.obj L.obj M.obj N.obj f g h

/-- The tensor-module abelian groups and bilinear composition give preadditivity.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance preadditive : Preadditive (ScalarLocalization R C p) where
  homGroup K L := inferInstanceAs (AddCommGroup (Localization.Away p ⊗[R] (K.obj ⟶ L.obj)))
  add_comp K L M f f' g := (composition R C p K.obj L.obj M.obj g).map_add f f'
  comp_add K L M f g g' := congrArg (fun β ↦ β f)
    ((composition R C p K.obj L.obj M.obj).map_add g g')

/-- The localized-ring linear structure on the tensor Hom modules.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance linear : Linear (Localization.Away p) (ScalarLocalization R C p) where
  homModule K L := inferInstanceAs
    (Module (Localization.Away p) (Localization.Away p ⊗[R] (K.obj ⟶ L.obj)))
  smul_comp K L M a f g := (composition R C p K.obj L.obj M.obj g).map_smul a f
  comp_smul K L M f a g := congrArg (fun β ↦ β f)
    ((composition R C p K.obj L.obj M.obj).map_smul a g)

/-- The R-linear structure obtained by restricting the localized-ring tensor action.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance linearOriginal : Linear R (ScalarLocalization R C p) where
  homModule K L := inferInstanceAs
    (Module R (Localization.Away p ⊗[R] (K.obj ⟶ L.obj)))
  smul_comp K L M a f g :=
    ((composition R C p K.obj L.obj M.obj g).restrictScalars R).map_smul a f
  comp_smul K L M f a g := congrArg (fun β ↦ β f)
    (((composition R C p K.obj L.obj M.obj).restrictScalars R).map_smul a g)

/-- The tensor-with-one maps preserve identities and composition.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization).
Proof: identities hold by definition; composition follows from `composition_tmul`
and `1 * 1 = 1`, as in `lem-weil-linear-scalar-localization-category`. -/
theorem localization_laws (K L M : C) (f : K ⟶ L) (g : L ⟶ M) :
    ((1 : Localization.Away p) ⊗ₜ[R] (f ≫ g)) =
      composition R C p K L M ((1 : Localization.Away p) ⊗ₜ[R] g)
        ((1 : Localization.Away p) ⊗ₜ[R] f) := by
  simp [composition_tmul]

/-- The localization functor: identity on objects, tensor with one on morphisms.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable def localization : C ⥤ ScalarLocalization R C p where
  obj K := ⟨K⟩
  map f := (1 : Localization.Away p) ⊗ₜ[R] f
  map_id _ := rfl
  map_comp f g := localization_laws R C p _ _ _ f g

/-- The localization functor is R-linear (including additivity).
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization).
Proof: the tensor-with-one map is additive by the tensor relations; its R-homogeneity
is the balancing relation and restriction along the localization ring map. This is
clause (3) of `lem-weil-linear-scalar-localization-category`. -/
theorem localization_linear :
    (localization R C p).Additive ∧ (localization R C p).Linear R := by
  constructor
  · exact ⟨fun {K L} {f g} ↦ TensorProduct.tmul_add _ _ _⟩
  · exact ⟨fun {K L} f a ↦ TensorProduct.tmul_smul _ _ _⟩

/-- Additivity of Q. Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance localizationAdditive : (localization R C p).Additive :=
  (localization_linear R C p).1

/-- R-linearity of Q. Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance localizationLinear : (localization R C p).Linear R :=
  (localization_linear R C p).2

variable (T : C ⥤ C) [T.Additive] [T.Linear R]

/-- The extended Hom map of an R-linear endofunctor is localized-ring linear.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable def mapHom (K L : C) :
    (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (T.obj K ⟶ T.obj L)) :=
  (T.mapLinearMap R).baseChange (Localization.Away p)

/-- Extended Hom maps preserve identities and composition.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization).
Proof: on pure tensors use `LinearMap.baseChange_tmul`, functoriality of T, and
`composition_tmul`. Extend the composition identity by additivity in both variables,
as in clause (4) of `lem-weil-linear-scalar-localization-category`. -/
theorem map_laws :
    (∀ K : C, mapHom R C p T K K ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (T.obj K)) ∧
    (∀ (K L M : C) (f : Localization.Away p ⊗[R] (K ⟶ L))
        (g : Localization.Away p ⊗[R] (L ⟶ M)),
      mapHom R C p T K M (composition R C p K L M g f) =
        composition R C p (T.obj K) (T.obj L) (T.obj M)
          (mapHom R C p T L M g) (mapHom R C p T K L f)) := by
  constructor
  · intro K
    simp [mapHom]
  · intro K L M f g
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f => simp [mapHom, composition_tmul]
      | add f f' hf hf' => simp [map_add, hf, hf']
    | add g g' hg hg' => simp [map_add, hg, hg']

/-- The induced shift/endofunctor, sending `a ⊗ f` to `a ⊗ T.map f`.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable def map : ScalarLocalization R C p ⥤ ScalarLocalization R C p where
  obj K := ⟨T.obj K.obj⟩
  map {K L} f := mapHom R C p T K.obj L.obj f
  map_id K := (map_laws R C p T).1 K.obj
  map_comp {K L M} f g := (map_laws R C p T).2 K.obj L.obj M.obj f g

/-- The extended shift is additive. Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance mapAdditive : (map R C p T).Additive where
  map_add {K L} {f g} := (mapHom R C p T K.obj L.obj).map_add f g

/-- The extended shift is linear over the localized ring.
Source: blueprint `def-weil-rationalization-karoubi`
(blueprint: def-weil-linear-scalar-localization). -/
noncomputable instance mapLinear : (map R C p T).Linear (Localization.Away p) where
  map_smul {K L} f a := (mapHom R C p T K.obj L.obj).map_smul a f

private theorem map_comp (U : C ⥤ C) [U.Additive] [U.Linear R] :
    map R C p T ⋙ map R C p U = map R C p (T ⋙ U) := by
  refine Functor.ext (F := map R C p T ⋙ map R C p U)
    (G := map R C p (T ⋙ U)) (fun _ ↦ rfl) ?_
  intro K L f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change mapHom R C p U _ _ (mapHom R C p T _ _ f) =
    mapHom R C p (T ⋙ U) _ _ f
  dsimp only [mapHom]
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]

private theorem map_identity : map R C p (𝟭 C) = 𝟭 (ScalarLocalization R C p) := by
  refine Functor.ext (F := map R C p (𝟭 C))
    (G := 𝟭 (ScalarLocalization R C p)) (fun _ ↦ rfl) ?_
  intro K L f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change mapHom R C p (𝟭 C) _ _ f = f
  dsimp only [mapHom]
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]

end ScalarLocalization
end CategoryTheory
