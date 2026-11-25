/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelOpenData
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTransition

/-! Assembly of levelwise strict étale extension data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem openSystemHomExt {T : Scheme.{u}} {O : Type (u + 1)}
    [CommRing O] {t : O} {M N : strictEtaleCoefficientSystem T O t}
    (f g : M ⟶ N) (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

section Transpose
universe a b c d av bv cv dv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {Fm : A ⥤ C} {Gm : C ⥤ A} {Fn : B ⥤ D} {Gn : D ⥤ B}
  {RX : B ⥤ A} {RZ : D ⥤ C}

private theorem openRestrictionTranspose (am : Fm ⊣ Gm) (an : Fn ⊣ Gn)
    (c : RX ⋙ Fm ≅ Fn ⋙ RZ) (b : RZ ⋙ Gm ≅ Gn ⋙ RX)
    (hc : (mateEquiv an am (.mk _ _ _ _ c.hom)) = b.inv)
    (M : B) (N : D) (f : Fn.obj M ⟶ N) :
    am.homEquiv _ _ (c.hom.app M ≫ RZ.map f) =
      RX.map (an.homEquiv _ _ f) ≫ b.inv.app N := by
  have hu := unit_mateEquiv an am (.mk _ _ _ _ c.hom) M
  change RX.map (an.unit.app M) ≫
      (mateEquiv an am (.mk _ _ _ _ c.hom)).app (Fn.obj M) =
    am.unit.app (RX.obj M) ≫ Gm.map (c.hom.app M) at hu
  rw [hc] at hu
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    ← Category.assoc, ← hu]
  have hn := b.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hn]

private theorem openTransitionTranspose (am : Fm ⊣ Gm) (an : Fn ⊣ Gn)
    (c : RX ⋙ Fm ≅ Fn ⋙ RZ) (b : RZ ⋙ Gm ≅ Gn ⋙ RX)
    (hc : (mateEquiv an am (.mk _ _ _ _ c.hom)) = b.inv)
    {Mm : A} {Mn : B} {Nm : C} {Nn : D}
    (tM : Mm ⟶ RX.obj Mn) (tN : Nm ⟶ RZ.obj Nn)
    (fm : Fm.obj Mm ⟶ Nm) (fn : Fn.obj Mn ⟶ Nn) :
    (fm ≫ tN = Fm.map tM ≫ c.hom.app Mn ≫ RZ.map fn) ↔
      am.homEquiv _ _ fm ≫ Gm.map tN ≫ b.hom.app Nn =
        tM ≫ RX.map (an.homEquiv _ _ fn) := by
  have he : am.homEquiv _ _ (Fm.map tM ≫ c.hom.app Mn ≫ RZ.map fn) =
      tM ≫ RX.map (an.homEquiv _ _ fn) ≫ b.inv.app Nn := by
    rw [am.homEquiv_naturality_left, openRestrictionTranspose am an c b hc]
  constructor
  · intro h
    have h' := congrArg (am.homEquiv _ _) h
    rw [am.homEquiv_naturality_right, he] at h'
    apply (cancel_mono (b.inv.app Nn)).mp
    simpa [Category.assoc] using h'
  · intro h
    apply (am.homEquiv _ _).injective
    rw [am.homEquiv_naturality_right, he]
    have h' := congrArg (· ≫ b.inv.app Nn) h
    simpa [Category.assoc] using h'
end Transpose

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (I : StrictEtaleOrdinaryImage O t j)
  (PX : StrictEtaleEvaluation X O t) (PZ : StrictEtaleEvaluation Z O t)
  (L : StrictEtaleLevelOpenData O t j I)

private def openSystemExtension :
    strictEtaleCoefficientSystem X O t ⥤ strictEtaleCoefficientSystem Z O t where
  obj M := {
    level := fun n ↦ (L.level n).obj (M.level n)
    transition := fun n ↦ (L.level (n + 1)).map (M.transition n) ≫
      (L.restriction (Nat.le_succ n)).hom.app (M.level n) }
  map {M N} f := {
    app := fun n ↦ (L.level n).map (f.app n)
    comm := by
      intro n
      dsimp
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, f.comm,
        CategoryTheory.Functor.map_comp, Category.assoc]
      exact congrArg ((L.level (n + 1)).map (M.transition n) ≫ ·)
        ((L.restriction (Nat.le_succ n)).hom.naturality (f.app n)) }
  map_id M := by
    apply openSystemHomExt
    intro n
    exact (L.level n).map_id _
  map_comp f g := by
    apply openSystemHomExt
    intro n
    exact (L.level n).map_comp _ _

omit [IsOpenImmersion j] in
private theorem openSystemExtensionAdditive :
    (openSystemExtension O t j I L).Additive := by
  refine ⟨?_⟩
  intro M N f g
  apply openSystemHomExt
  intro n
  change (L.level n).map
    ((coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := t) n).map (f + g)) =
    (coefficientEvaluation (J := Z.smallEtaleTopology) (O := O) (ell := t) n).map
      ((openSystemExtension O t j I L).map f + (openSystemExtension O t j I L).map g)
  simp only [Functor.map_add]
  rfl

attribute [local instance] openSystemExtensionAdditive

private def openSystemEvaluation (n : ℕ) :
    openSystemExtension O t j I L ⋙ coefficientEvaluation
      (J := Z.smallEtaleTopology) (O := O) (ell := t) n ≅
    coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := t) n ⋙ L.level n :=
  Iso.refl _

private def openSystemHomEquiv (M : strictEtaleCoefficientSystem X O t)
    (N : strictEtaleCoefficientSystem Z O t) :
    ((openSystemExtension O t j I L).obj M ⟶ N) ≃ (M ⟶ I.inverse.obj N) where
  toFun f := {
    app := fun n ↦ (L.levelAdjunction n).homEquiv _ _ (f.app n) ≫
      (I.inverseEvaluation n).inv.app N
    comm := by
      intro n
      apply (cancel_mono ((coefficientRestriction (J := X.smallEtaleTopology)
        O t (Nat.le_succ n)).map ((I.inverseEvaluation n).hom.app N))).mp
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [I.inverseTransition n N]
      simp only [← Category.assoc, Iso.inv_hom_id_app]
      simp only [Category.assoc]
      erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
      dsimp only [Functor.comp_obj, coefficientEvaluation]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact
        (openTransitionTranspose (L.levelAdjunction (n + 1)) (L.levelAdjunction n)
          (L.restriction (Nat.le_succ n)) (I.restrictInverse (Nat.le_succ n))
          (L.restrictionMate (Nat.le_succ n)) (M.transition n) (N.transition n)
          (f.app (n + 1)) (f.app n)).1 (f.comm n) }
  invFun f := {
    app := fun n ↦ ((L.levelAdjunction n).homEquiv _ _).symm
      (f.app n ≫ (I.inverseEvaluation n).hom.app N)
    comm := by
      intro n
      dsimp only [openSystemExtension]
      rw [Category.assoc]
      apply (openTransitionTranspose (L.levelAdjunction (n + 1)) (L.levelAdjunction n)
        (L.restriction (Nat.le_succ n)) (I.restrictInverse (Nat.le_succ n))
        (L.restrictionMate (Nat.le_succ n)) (M.transition n) (N.transition n) _ _).2
      simp only [Equiv.apply_symm_apply]
      rw [Category.assoc, ← I.inverseTransition n N, ← Category.assoc, f.comm]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc] }
  left_inv f := by
    apply openSystemHomExt
    intro n
    simp only [Functor.comp_obj, coefficientEvaluation, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id,
      Equiv.symm_apply_apply]
  right_inv f := by
    apply openSystemHomExt
    intro n
    simp only [Functor.comp_obj, coefficientEvaluation, Equiv.apply_symm_apply,
      Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]

private def openSystemAdjunction : openSystemExtension O t j I L ⊣ I.inverse :=
  Adjunction.mkOfHomEquiv {
    homEquiv := openSystemHomEquiv O t j I L
    homEquiv_naturality_left_symm := by
      intro M M' N f g
      apply openSystemHomExt
      intro n
      change ((L.levelAdjunction n).homEquiv _ _).symm
        ((f.app n ≫ g.app n) ≫ (I.inverseEvaluation n).hom.app N) =
        (L.level n).map (f.app n) ≫ ((L.levelAdjunction n).homEquiv _ _).symm
          (g.app n ≫ (I.inverseEvaluation n).hom.app N)
      rw [Category.assoc]
      exact (L.levelAdjunction n).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := by
      intro M N N' f g
      apply openSystemHomExt
      intro n
      change (L.levelAdjunction n).homEquiv _ _ (f.app n ≫ g.app n) ≫
        (I.inverseEvaluation n).inv.app N' =
        ((L.levelAdjunction n).homEquiv _ _ (f.app n) ≫
          (I.inverseEvaluation n).inv.app N) ≫ (I.inverse.map g).app n
      rw [Adjunction.homEquiv_naturality_right, Category.assoc]
      exact congrArg ((L.levelAdjunction n).homEquiv _ _ (f.app n) ≫ ·)
        ((I.inverseEvaluation n).inv.naturality g) }

private theorem openSystemEvaluationsReflect :
    JointlyReflectIsomorphisms
      (coefficientEvaluation (J := Z.smallEtaleTopology) (O := O) (ell := t)) where
  isIso {M N} f hf := by
    have hi (n : ℕ) : IsIso (f.app n) := hf n
    let g : N ⟶ M := {
      app := fun n ↦ inv (f.app n)
      comm := by
        intro n
        apply (cancel_epi (f.app (n + 1))).mp
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm, Category.assoc]
        simp only [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id]
        rw [(coefficientRestriction (J := Z.smallEtaleTopology) O t (Nat.le_succ n)).map_id]
        exact (Category.comp_id _).symm }
    refine ⟨g, ?_, ?_⟩
    · apply openSystemHomExt
      intro n
      exact IsIso.hom_inv_id _
    · apply openSystemHomExt
      intro n
      exact IsIso.inv_hom_id _

omit [IsOpenImmersion j] in
private theorem openSystemExact :
    PreservesFiniteLimits (openSystemExtension O t j I L) ∧
      PreservesFiniteColimits (openSystemExtension O t j I L) := by
  have hjlim (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := t) n) :=
    (coefficientEvaluation_exact (J := X.smallEtaleTopology) (O := O) (ell := t) n).1
  have hjcolim (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := t) n) :=
    (coefficientEvaluation_exact (J := X.smallEtaleTopology) (O := O) (ell := t) n).2
  have hzlim (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := Z.smallEtaleTopology) (O := O) (ell := t) n) :=
    (coefficientEvaluation_exact (J := Z.smallEtaleTopology) (O := O) (ell := t) n).1
  have hzcolim (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := Z.smallEtaleTopology) (O := O) (ell := t) n) :=
    (coefficientEvaluation_exact (J := Z.smallEtaleTopology) (O := O) (ell := t) n).2
  exact (openSystemEvaluationsReflect O t (Z := Z)).exactFunctor_of_iso
    (F := coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := t))
    (openSystemExtension O t j I L) L.level L.levelExact (openSystemEvaluation O t j I L)

omit [IsOpenImmersion j] in
private theorem openSystemEvaluationMate (n : ℕ) :
    (I.inverseEvaluation n).hom =
      (mateEquiv (openSystemAdjunction O t j I L) (L.levelAdjunction n)
        (.mk _ _ _ _ (openSystemEvaluation O t j I L n).inv)) := by
  apply NatTrans.ext
  funext N
  apply ((L.levelAdjunction n).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  have hc := mateEquiv_counit (openSystemAdjunction O t j I L)
    (L.levelAdjunction n) (.mk _ _ _ _ (openSystemEvaluation O t j I L n).inv) N
  change _ = _ ≫ _ at hc
  erw [hc]
  dsimp only [openSystemEvaluation, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp]
  change _ = ((openSystemAdjunction O t j I L).counit.app N).app n
  change (L.level n).map ((I.inverseEvaluation n).hom.app N) ≫
      (L.levelAdjunction n).counit.app (N.level n) =
    ((L.levelAdjunction n).homEquiv _ _).symm
      (𝟙 ((I.inverse.obj N).level n) ≫ (I.inverseEvaluation n).hom.app N)
  simp only [Category.id_comp, Adjunction.homEquiv_counit]
  rfl

omit [IsOpenImmersion j] in
private theorem openSystemTransition {m n : ℕ} (h : n ≤ m)
    (M : strictEtaleCoefficientSystem X O t) :
    (PZ.strictTransition h).app ((openSystemExtension O t j I L).obj M) =
      (L.level m).map ((PX.strictTransition h).app M) ≫
        (L.restriction h).hom.app (M.level n) := by
  let N := (openSystemExtension O t j I L).obj M
  let g : M ⟶ I.inverse.obj N := openSystemHomEquiv O t j I L M N (𝟙 N)
  have hu (q : ℕ) : g.app q ≫ (I.inverseEvaluation q).hom.app N =
      (L.levelAdjunction q).homEquiv _ _ (𝟙 (N.level q)) := by
    dsimp only [g, openSystemHomEquiv, Equiv.coe_fn_mk, CoefficientSystem.identity]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hn := (PX.strictTransition h).naturality g
  change g.app m ≫ (PX.strictTransition h).app (I.inverse.obj N) =
    (PX.strictTransition h).app M ≫
      (coefficientRestriction (J := X.smallEtaleTopology) O t h).map (g.app n) at hn
  have hi := strictEtaleInverseTransition O t j I PX PZ h N
  have he := (openTransitionTranspose (L.levelAdjunction m) (L.levelAdjunction n)
    (L.restriction h) (I.restrictInverse h) (L.restrictionMate h)
    ((PX.strictTransition h).app M) ((PZ.strictTransition h).app N)
    (𝟙 (N.level m)) (𝟙 (N.level n))).2 (by
      dsimp only [coefficientEvaluation]
      rw [← hu m, ← hu n]
      calc
        (g.app m ≫ (I.inverseEvaluation m).hom.app N) ≫
            (I.lift m).modules.map ((PZ.strictTransition h).app N) ≫
              (I.restrictInverse h).hom.app (N.level n) =
            g.app m ≫ ((PX.strictTransition h).app (I.inverse.obj N) ≫
              (coefficientRestriction (J := X.smallEtaleTopology) O t h).map
                ((I.inverseEvaluation n).hom.app N)) := by
          rw [hi]
          simp only [Category.assoc]
        _ = (PX.strictTransition h).app M ≫
            (coefficientRestriction (J := X.smallEtaleTopology) O t h).map
              (g.app n ≫ (I.inverseEvaluation n).hom.app N) := by
          rw [← Category.assoc, hn, CategoryTheory.Functor.map_comp, Category.assoc])
  dsimp only [coefficientEvaluation] at he
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at he
  exact he

/-- The system-level assembly data for ordinary strict étale extension.
Source: Zheng, Construction 4.1 and Stacks 03S2, 03DI and 03DJ
(blueprint: new-lem-pur-strict-etale-system-open-assembly).

This record supplies only the system functor, its exact adjunction, evaluation mate,
and transition law.  The levelwise functors and their restriction mates are supplied
by `L`; hence this is a proper assembly step rather than a restatement of the full
ordinary-open theorem. -/
structure StrictEtaleSystemOpenAssembly where
  extension : strictEtaleCoefficientSystem X O t ⥤ strictEtaleCoefficientSystem Z O t
  [additive : extension.Additive]
  exact : PreservesFiniteLimits extension ∧ PreservesFiniteColimits extension
  adjunction : extension ⊣ I.inverse
  evaluation : ∀ n, extension ⋙ coefficientEvaluation
    (J := Z.smallEtaleTopology) (O := O) (ell := t) n ≅
      coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := t) n ⋙ L.level n
  evaluationMate : ∀ n, (I.inverseEvaluation n).hom =
    (mateEquiv adjunction (L.levelAdjunction n)
      (.mk _ _ _ _ (evaluation n).inv))
  transition : ∀ {m n : ℕ} (h : n ≤ m) M,
    (PZ.strictTransition h).app (extension.obj M) ≫
      (coefficientRestriction (J := Z.smallEtaleTopology) O t h).map
        ((evaluation n).hom.app M) =
    (evaluation m).hom.app M ≫ (L.level m).map ((PX.strictTransition h).app M) ≫
      (L.restriction h).hom.app (M.level n)

attribute [instance] StrictEtaleSystemOpenAssembly.additive

set_option linter.unusedSectionVars false in
/-- The system-level assembly exists for every levelwise package.
Source: Zheng, Construction 4.1; Stacks Project 03S2, 03DI and 03DJ.
(blueprint: new-lem-pur-strict-etale-system-open-assembly)

Proof. Extend the `n`th level of a system `M` by `L.level n`. Define its
successor transition by applying the next-level extension to the source
transition, then composing with `L.restriction`. On a morphism use the level
functors. Naturality of the restriction comparison proves that these component
maps commute with the transitions and that they define an additive functor.

The component adjunctions `L.levelAdjunction` identify families of component maps
with families of their transposes. The identities `L.restrictionMate`, together
with the normalized evaluation comparison of `I.inverse`, identify the two
transition-compatibility equations under this bijection. Thus it restricts to a
bijection on system morphisms. Componentwise naturality makes this a natural Hom
equivalence, hence gives `adjunction`. Evaluating the constructed functor gives
the required `evaluation`; transposing this comparison by the same Hom
equivalence proves `evaluationMate`.

The evaluation functors are exact and jointly reflect isomorphisms. Since each
`L.level n` is exact and the constructed extension evaluates to it, the existing
joint-conservativity exactness criterion proves `exact`.

For an arbitrary pair `n ≤ m`, transpose the identity of the extended system to
a system map into its inverse image. Naturality of the source transition for this
map, together with `strictEtaleInverseTransition`, gives the transposed form of
the required transition equation. The level Hom equivalence reflects equality,
so the transition equation follows. The same construction covers the empty open
and zero ring; all component maps and Hom equivalences retain these formulas. -/
theorem strictEtaleSystemOpenAssembly_exists :
    Nonempty (StrictEtaleSystemOpenAssembly O t j I PX PZ L) := by
  refine ⟨{
    extension := openSystemExtension O t j I L
    exact := openSystemExact O t j I L
    adjunction := openSystemAdjunction O t j I L
    evaluation := openSystemEvaluation O t j I L
    evaluationMate := openSystemEvaluationMate O t j I L
    transition := ?_ }⟩
  intro m n h M
  dsimp only [openSystemEvaluation, Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact openSystemTransition O t j I PX PZ L h M

end AlgebraicGeometry
