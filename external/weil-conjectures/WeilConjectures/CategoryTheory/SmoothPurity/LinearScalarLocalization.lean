/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Category laws for raw scalar localization

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi` (blueprint: lem-weil-linear-scalar-localization-category).
The scalar-first tensor order is the convention of `LinearMap.baseChange`.
`ULift.{0} C` is only a wrapper for the unchanged objects, with no new objects adjoined.
-/

@[expose] public section

set_option linter.unusedVariables false

universe r u v

open CategoryTheory TensorProduct

namespace CategoryTheory

namespace LinearScalarConstruction

variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (p : R)

private noncomputable def composition (K L M : C) :
    (Localization.Away p ⊗[R] (L ⟶ M)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (K ⟶ M)) :=
  TensorProduct.curry
    (((TensorProduct.lift (LinearMap.flip (Linear.comp (S := R) K L M))).baseChange
      (Localization.Away p)).comp
        (AlgebraTensorModule.distribBaseChange R (Localization.Away p)
          (L ⟶ M) (K ⟶ L)).symm.toLinearMap)

-- This is the explicit construction above, not ScalarLocalization.composition, whose
-- definition uses exists_linear_scalarLocalization_category and cannot be imported here.
private theorem composition_tmul
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R)
    (K L M : C) (f : L ⟶ M) (g : K ⟶ L)
    (a b : Localization.Away p) :
    LinearScalarConstruction.composition R C p K L M (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) =
      (a * b) ⊗ₜ[R] (g ≫ f) := by
  simp [composition, TensorProduct.curry_apply]

private theorem composition_unique (K L M : C)
    (β : (Localization.Away p ⊗[R] (L ⟶ M)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (K ⟶ M)))
    (hβ : ∀ (f : L ⟶ M) (g : K ⟶ L) (a b : Localization.Away p),
      β (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f)) :
    β = composition R C p K L M := by
  ext f g
  exact (hβ f g 1 1).trans (composition_tmul R C p K L M f g 1 1).symm

private theorem composition_id_comp (K L : C)
    (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    composition R C p K K L f (1 ⊗ₜ[R] 𝟙 K) = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [composition_tmul]
  | add f g hf hg => simp [hf, hg]

private theorem composition_comp_id (K L : C)
    (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    composition R C p K L L (1 ⊗ₜ[R] 𝟙 L) f = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [composition_tmul]
  | add f g hf hg => simp [hf, hg]

private theorem composition_assoc (K L M N : C)
    (f : Localization.Away p ⊗[R] (K ⟶ L))
    (g : Localization.Away p ⊗[R] (L ⟶ M))
    (h : Localization.Away p ⊗[R] (M ⟶ N)) :
    composition R C p K M N h (composition R C p K L M g f) =
      composition R C p K L N (composition R C p L M N h g) f := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [hf, hf']
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [hg, hg']
    | tmul b g =>
      induction h using TensorProduct.inductionOn with
      | add h h' hh hh' => simp [hh, hh']
      | tmul c h => simp [composition_tmul, Category.assoc, mul_assoc]

private theorem map_composition (T : C ⥤ C) [T.Additive] [T.Linear R]
    (K L M : C) (f : Localization.Away p ⊗[R] (K ⟶ L))
    (g : Localization.Away p ⊗[R] (L ⟶ M)) :
    (T.mapLinearMap R).baseChange (Localization.Away p)
        (composition R C p K L M g f) =
      composition R C p (T.obj K) (T.obj L) (T.obj M)
        ((T.mapLinearMap R).baseChange (Localization.Away p) g)
        ((T.mapLinearMap R).baseChange (Localization.Away p) f) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [hf, hf']
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [hg, hg']
    | tmul b g => simp [composition_tmul]

@[instance_reducible]
private noncomputable def category : Category.{max r v} (ULift.{0} C) where
  Hom K L := Localization.Away p ⊗[R] (K.down ⟶ L.down)
  id K := (1 : Localization.Away p) ⊗ₜ[R] 𝟙 K.down
  comp {K L M} f g := composition R C p K.down L.down M.down g f
  id_comp {K L} f := composition_id_comp R C p K.down L.down f
  comp_id {K L} f := composition_comp_id R C p K.down L.down f
  assoc {K L M N} f g h := composition_assoc R C p K.down L.down M.down N.down f g h

end LinearScalarConstruction

open LinearScalarConstruction

/-- The raw tensor-Hom localization is a linear category, with a linear localization functor
and induced strict automorphisms.
Source: the Weil conjectures blueprint, `def-weil-rationalization-karoubi`
(blueprint: lem-weil-linear-scalar-localization-category).

Proof plan:
1. Extend the bilinear composition of the original category by the unique bilinear extension
of module base change (Stacks 00CV, 00CX, 05G4).
2. Every tensor is a finite sum of pure tensors. On three pure tensors associativity is the
associativity of the original composition and of scalar multiplication; extend by additivity.
The original identities tensored with one give the two identity laws in the same way.
3. The maps `f ↦ 1 ⊗ f` are R-linear, preserve identities by construction, and preserve
composition because `1 * 1 = 1`. They therefore define the linear functor Q.
4. Base change the linear Hom maps of T. These preserve composition and identities on pure
tensors, hence on finite sums, and give an A-linear functor T'.
5. The strict inverse S of T is linear: apply the bijective Hom maps of T to the additivity
and scalar equations for S. Its base change gives S'. The inverse equations hold on objects
and on pure tensors and therefore on all morphisms. The two composites with Q agree on
objects and on `1 ⊗ f`, giving the strict commuting square.

The linear Hom equivalences below give tensor coordinates for the morphisms. The category
instance supplies associativity and both identity laws. Instance-binding lambdas merely
scope the existential category and linear structures; they introduce no extra hypotheses. -/
theorem exists_linear_scalarLocalization_category
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) :
    (∀ K L M : C,
      ∃! β : (Localization.Away p ⊗[R] (L ⟶ M)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ M)),
        ∀ (f : L ⟶ M) (g : K ⟶ L) (a b : Localization.Away p),
          β (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f)) ∧
    ∃ d : Category.{max r v} (ULift.{0} C),
      (fun [catInst : Category.{max r v} (ULift.{0} C)] ↦
        ∃ a : Preadditive (ULift.{0} C), (fun [addInst : Preadditive (ULift.{0} C)] ↦
          ∃ l : Linear (Localization.Away p) (ULift.{0} C),
            (fun [linInst : Linear (Localization.Away p) (ULift.{0} C)] ↦
              ∃ e : ∀ K L : C, (Localization.Away p ⊗[R] (K ⟶ L))
                  ≃ₗ[Localization.Away p] (ULift.up K ⟶ ULift.up L),
                (∀ K : C, e K K (1 ⊗ₜ[R] 𝟙 K) = 𝟙 (ULift.up K)) ∧
                (∀ (K L M : C) (f : L ⟶ M) (g : K ⟶ L)
                    (a b : Localization.Away p),
                  e K L (b ⊗ₜ[R] g) ≫ e L M (a ⊗ₜ[R] f) =
                    e K M ((a * b) ⊗ₜ[R] (g ≫ f))) ∧
                ∃ lr : Linear R (ULift.{0} C), (fun [rlinInst : Linear R (ULift.{0} C)] ↦
                  (∀ (K L : ULift.{0} C) (r : R) (f : K ⟶ L),
                    r • f = (algebraMap R (Localization.Away p) r) • f) ∧
                  ∃ Q : C ⥤ ULift.{0} C,
                    (∀ K : C, Q.obj K = ULift.up K) ∧
                    (∀ (K L : C) (f : K ⟶ L), HEq (Q.map f) (e K L (1 ⊗ₜ[R] f))) ∧
                    Q.Additive ∧ Q.Linear R ∧
                    ∀ (T S : C ⥤ C) [T.Additive] [T.Linear R],
                      T ⋙ S = 𝟭 C → S ⋙ T = 𝟭 C →
                      ∃ T' S' : ULift.{0} C ⥤ ULift.{0} C,
                        T'.Additive ∧ T'.Linear (Localization.Away p) ∧
                        S'.Additive ∧ S'.Linear (Localization.Away p) ∧
                        (∀ K : C, T'.obj (ULift.up K) = ULift.up (T.obj K)) ∧
                        (∀ K : C, S'.obj (ULift.up K) = ULift.up (S.obj K)) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (T'.map (e K L (a ⊗ₜ[R] f)))
                            (e (T.obj K) (T.obj L) (a ⊗ₜ[R] T.map f))) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (S'.map (e K L (a ⊗ₜ[R] f)))
                            (e (S.obj K) (S.obj L) (a ⊗ₜ[R] S.map f))) ∧
                        T' ⋙ S' = 𝟭 (ULift.{0} C) ∧ S' ⋙ T' = 𝟭 (ULift.{0} C) ∧
                        T ⋙ Q = Q ⋙ T'
                ) (rlinInst := lr)
            ) (linInst := l)) (addInst := a)) (catInst := d) := by
  refine ⟨?_, category R C p, ?_⟩
  · intro K L M
    exact ⟨composition R C p K L M, composition_tmul R C p K L M,
      composition_unique R C p K L M⟩
  let : Category.{max r v} (ULift.{0} C) := category R C p
  let : Preadditive (ULift.{0} C) :=
    { homGroup := fun K L ↦
        inferInstanceAs (AddCommGroup (Localization.Away p ⊗[R] (K.down ⟶ L.down)))
      add_comp := fun K L M f f' g ↦
        (composition R C p K.down L.down M.down g).map_add f f'
      comp_add := fun K L M f g g' ↦ congrArg (fun β ↦ β f)
        ((composition R C p K.down L.down M.down).map_add g g') }
  refine ⟨inferInstance, ?_⟩
  let : Linear (Localization.Away p) (ULift.{0} C) :=
    { homModule := fun K L ↦
        inferInstanceAs (Module (Localization.Away p)
          (Localization.Away p ⊗[R] (K.down ⟶ L.down)))
      smul_comp := fun K L M a f g ↦
        (composition R C p K.down L.down M.down g).map_smul a f
      comp_smul := fun K L M f a g ↦ congrArg (fun β ↦ β f)
        ((composition R C p K.down L.down M.down).map_smul a g) }
  refine ⟨inferInstance, fun K L ↦ LinearEquiv.refl _ _, ?_, ?_, ?_⟩
  · intro K
    rfl
  · intro K L M f g a b
    exact composition_tmul R C p K L M f g a b
  let : Linear R (ULift.{0} C) :=
    { homModule := fun K L ↦
        inferInstanceAs (Module R (Localization.Away p ⊗[R] (K.down ⟶ L.down)))
      smul_comp := fun K L M a f g ↦
        ((composition R C p K.down L.down M.down g).restrictScalars R).map_smul a f
      comp_smul := fun K L M f a g ↦ congrArg (fun β ↦ β f)
        (((composition R C p K.down L.down M.down).restrictScalars R).map_smul a g) }
  refine ⟨inferInstance, ?_, ?_⟩
  · intro K L a f
    change (a • f : Localization.Away p ⊗[R] (K.down ⟶ L.down)) =
      (algebraMap R (Localization.Away p) a) • f
    exact (algebraMap_smul (M := Localization.Away p ⊗[R] (K.down ⟶ L.down))
      (Localization.Away p) a f).symm
  let Q : C ⥤ ULift.{0} C :=
    { obj := fun K ↦ ULift.up K
      map := fun f ↦ (1 : Localization.Away p) ⊗ₜ[R] f
      map_id := fun K ↦ rfl
      map_comp := fun {K L M} f g ↦ by
        change (1 : Localization.Away p) ⊗ₜ[R] (f ≫ g) =
          composition R C p K L M (1 ⊗ₜ[R] g) (1 ⊗ₜ[R] f)
        simp [composition_tmul] }
  have qadd : Q.Additive := ⟨fun {K L f g} ↦ TensorProduct.tmul_add _ _ _⟩
  have qlin : Q.Linear R := ⟨fun {K L} f a ↦ by
    exact (TensorProduct.mk R (Localization.Away p) (K ⟶ L) 1).map_smul a f⟩
  refine ⟨Q, fun K ↦ rfl, fun K L f ↦ HEq.rfl, qadd, qlin, ?_⟩
  let extend : (F : C ⥤ C) → [F.Additive] → [F.Linear R] →
      (ULift.{0} C ⥤ ULift.{0} C) := fun F _ _ ↦
    { obj := fun K ↦ ULift.up (F.obj K.down)
      map := fun f ↦ (F.mapLinearMap R).baseChange (Localization.Away p) f
      map_id := fun K ↦ by
        change (F.mapLinearMap R).baseChange (Localization.Away p)
            (1 ⊗ₜ[R] 𝟙 K.down) = (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K.down)
        simp
      map_comp := fun {K L M} f g ↦ map_composition R C p F K.down L.down M.down f g }
  have extend_add (F : C ⥤ C) [F.Additive] [F.Linear R] : (extend F).Additive :=
    ⟨fun {K L f g} ↦ ((F.mapLinearMap R).baseChange (Localization.Away p)).map_add f g⟩
  have extend_lin (F : C ⥤ C) [F.Additive] [F.Linear R] :
      (extend F).Linear (Localization.Away p) :=
    ⟨fun {K L} f a ↦ ((F.mapLinearMap R).baseChange (Localization.Away p)).map_smul a f⟩
  have extend_comp (F G : C ⥤ C) [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] :
      extend (F ⋙ G) = extend F ⋙ extend G := by
    refine Functor.hext ?_ ?_
    · intro K
      rfl
    intro K L f
    apply heq_of_eq
    change ((F ⋙ G).mapLinearMap R).baseChange (Localization.Away p) f =
      (G.mapLinearMap R).baseChange (Localization.Away p)
        ((F.mapLinearMap R).baseChange (Localization.Away p) f)
    change (((G.mapLinearMap R).comp (F.mapLinearMap R)).baseChange
      (Localization.Away p)) f = _
    rw [LinearMap.baseChange_comp]
    rfl
  have extend_id : extend (𝟭 C) = 𝟭 (ULift.{0} C) := by
    apply Functor.hext (fun K ↦ by cases K; rfl)
    intro K L f
    apply heq_of_eq
    change ((𝟭 C).mapLinearMap R).baseChange (Localization.Away p) f = f
    change (LinearMap.id.baseChange (Localization.Away p)) f = f
    rw [LinearMap.baseChange_id]
    rfl
  have extend_congr (F G : C ⥤ C) [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
      (h : F = G) : extend F = extend G := by
    subst G
    rfl
  intro T S hTadd hTlin hTS hST
  let e : C ≌ C := Equivalence.mk T S (eqToIso hTS.symm) (eqToIso hST)
  have : e.functor.Additive := hTadd
  have : e.functor.Linear R := hTlin
  have : S.Additive := inferInstanceAs e.inverse.Additive
  have : S.Linear R := inferInstanceAs (e.inverse.Linear R)
  refine ⟨extend T, extend S, extend_add T, extend_lin T, extend_add S, extend_lin S,
    fun K ↦ rfl, fun K ↦ rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro K L f a
    exact heq_of_eq (LinearMap.baseChange_tmul _ _ _)
  · intro K L f a
    exact heq_of_eq (LinearMap.baseChange_tmul _ _ _)
  · exact (extend_comp T S).symm.trans ((extend_congr _ _ hTS).trans extend_id)
  · exact (extend_comp S T).symm.trans ((extend_congr _ _ hST).trans extend_id)
  · refine Functor.hext ?_ ?_
    · intro K
      rfl
    intro K L f
    exact heq_of_eq (LinearMap.baseChange_tmul (T.mapLinearMap R) 1 f).symm

end CategoryTheory
