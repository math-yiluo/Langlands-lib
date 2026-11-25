/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.ChosenModuleFlatProperStage
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Refining an already chosen complex to flat terms with proper support

Source: Stacks Project, Tags 05LY, 081G and 0CYS; tensor pullback functoriality.
(blueprint: lem-pc-chosen-complex-flat-proper-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem zero_flat_proper {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (M : X.Modules) (hM : IsZero M) :
    M.IsFlatOver f ∧ Scheme.Modules.HasSupportProperOver f M := by
  constructor
  · intro V U e
    have he : (𝟙 M : M ⟶ M) = 0 := hM.eq_of_src _ _
    have : Subsingleton Γ(M, U.1) := by
      refine ⟨fun a b ↦ ?_⟩
      have ha := congrArg (fun t : M ⟶ M ↦ (t.val.app (op U.1)).hom a) he
      have hb := congrArg (fun t : M ⟶ M ↦ (t.val.app (op U.1)).hom b) he
      change a = 0 at ha
      change b = 0 at hb
      exact ha.trans hb.symm
    let : Module Γ(S, V.1) Γ(M, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
    infer_instance
  · have hz (x : X) : Subsingleton (M.presheaf.stalk x) :=
      AddCommGrpCat.subsingleton_of_isZero
        ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x).map_isZero hM)
    refine ⟨⊥, ?_, ?_⟩
    · ext x
      simp only [TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false,
        Set.mem_ofPred_eq]
      simp [hz x]
    · let Z := Scheme.IdealSheafData.vanishingIdeal
        (⊥ : TopologicalSpace.Closeds X)
      have : IsEmpty Z.subscheme := by
        refine ⟨fun x ↦ ?_⟩
        have hr : Set.range Z.subschemeι = (∅ : Set X) := by simp [Z]
        have hx : Z.subschemeι x ∈ Set.range Z.subschemeι := Set.mem_range_self x
        rw [hr] at hx
        exact hx
      change IsProper (Z.subschemeι ≫ f)
      infer_instance

/-- Refine an already chosen bounded finitely presented complex at stage `j`.
This statement does not descend a complex from the limit: the entire finite-stage
complex `H`, including its differentials, is an input. Its limit pullback is assumed
flat with proper support. The output identifies the new limit pullback with the
pullback of this particular `H`, compatibly with all differentials.

Source: Stacks Project, Limits of Schemes, Tag 05LY and Tag 081G; Cohomology of
Schemes, Tag 0CYS; pullback pasting and tensor pullback functoriality.
(blueprint: lem-pc-chosen-complex-flat-proper-refinement).

Proof: choose bounds `a,b` for `H`. For each degree in the finite integer interval
`[a,b]`, regard its term as a finitely presented module on `X_j`. Pullback pasting
identifies its limit pullback with the displayed module base change. Tag 05LY gives
a stage where that chosen term is flat, and Tag 081G gives a stage where its support
is proper, using Tag 0CYS to interpret proper support. Both properties persist under
further base change. Choose one common upper bound of `j` and these finitely many
stages by directedness. Outside the interval the terms are zero, with flat sections
and empty proper support, so impose no additional stage condition. Pull back `H`
to this common stage using the additive tensor pullback functor on complexes.
Pullback preserves zero objects and finite presentation, so this complex is bounded
and finitely presented. Its terms are flat with proper support by the choice of stage.
The composition isomorphism of tensor pullback, together with pullback pasting,
identifies its limit pullback with that of `H`; naturality gives the equation for each
differential. If the interval is empty, take `j` itself. For a preorder, restrict to a final
directed poset in its thin filtered category (Tag 0032); finality preserves the limit.
Apply the directed-poset argument there and return the resulting stage through the
final functor. Thus antisymmetry is not an assumption. -/
theorem exists_chosen_complex_flat_proper_refinement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (H : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ)
    (hH_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n))
    (hH_fp : ∀ n : ℤ, (H.X n).IsFinitePresentation)
    (hH_flat : ∀ n : ℤ,
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n)).IsFlatOver
        (pullback.snd f (c.π.app (op i))))
    (hH_support : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n))) :
    ∃ (k : I) (hjk : j ≤ k)
      (K : CochainComplex
        (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
      (∀ n : ℤ, (K.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (K.X n).IsFlatOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk)))))) ∧
      (∀ n : ℤ, Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) (K.X n)) ∧
      ∃ e : ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))).obj
            (K.X n) ≅
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n),
        ∀ n m : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))).map
            (K.d n m) ≫ (e m).hom =
          (e n).hom ≫ (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (H.d n m) := by
  classical
  obtain ⟨a, b, hab⟩ := hH_bounded
  have hterm (n : ℤ) := by
    have : (H.X n).IsFinitePresentation := hH_fp n
    exact exists_eventually_chosen_module_flat_proper R c hc i f j hij
      (H.X n) (hH_flat n) (hH_support n)
  choose stage hstage hprops using hterm
  have hbound (s : Finset ℤ) : ∃ k : I, j ≤ k ∧ ∀ n ∈ s, stage n ≤ k := by
    induction s using Finset.induction_on with
    | empty => exact ⟨j, le_rfl, by simp⟩
    | @insert n s _ ih =>
      obtain ⟨k, hjk, hk⟩ := ih
      obtain ⟨l, hkl, hnl⟩ := exists_ge_ge k (stage n)
      refine ⟨l, hjk.trans hkl, ?_⟩
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact hnl
      · exact (hk m hm).trans hkl
  obtain ⟨k, hjk, hk⟩ := hbound (Finset.Icc a b)
  let Tj : Over (Spec (R.obj i)) := Over.mk (Spec.map (R.map (homOfLE hij)))
  let Tk : Over (Spec (R.obj i)) :=
    Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk))))
  let Tlim : Over (Spec (R.obj i)) := Over.mk (c.π.app (op i))
  let g : Tk ⟶ Tj := Over.homMk (Spec.map (R.map (homOfLE hjk)))
    (by dsimp [Tk, Tj]; simp [← Functor.map_comp, ← Spec.map_comp])
  let q : Tlim ⟶ Tk :=
    Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op)
  let r : Tlim ⟶ Tj := Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)
  have hqr : q ≫ g = r := by
    ext
    exact c.w (homOfLE hjk).op
  let B := Scheme.Modules.moduleBaseChange f g
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction (baseChangeMap f g)
  have : B.Additive := adj.left_adjoint_additive
  let K := (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj H
  have hfp (n : ℤ) : (K.X n).IsFinitePresentation := by
    have : (H.X n).IsFinitePresentation := hH_fp n
    exact Scheme.Modules.isFinitePresentation_of_iso
      ((adj.leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap f g))).symm.app
          (H.X n))
  have hp (n : ℤ) : (K.X n).IsFlatOver (pullback.snd f Tk.hom) ∧
      Scheme.Modules.HasSupportProperOver (pullback.snd f Tk.hom) (K.X n) := by
    by_cases hn : n ∈ Finset.Icc a b
    · exact hprops n k (hk n hn)
    · apply zero_flat_proper
      apply B.map_isZero
      apply hab
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      exact hn
  obtain ⟨ec⟩ := Scheme.Modules.nonempty_tensorPullbackComp
    (baseChangeMap f q) (baseChangeMap f g)
  have heq : baseChangeMap f q ≫ baseChangeMap f g = baseChangeMap f r := by
    rw [← baseChangeMap_comp, hqr]
  let ecomp : Scheme.Modules.moduleBaseChange f r ≅
      B ⋙ Scheme.Modules.moduleBaseChange f q :=
    eqToIso (congrArg Scheme.Modules.tensorPullback heq.symm) ≪≫ ec
  refine ⟨k, hjk, K, ⟨a, b, fun n hn ↦ B.map_isZero (hab n hn)⟩,
    hfp, fun n ↦ (hp n).1, fun n ↦ (hp n).2,
    fun n ↦ (ecomp.app (H.X n)).symm, ?_⟩
  intro n m
  exact ecomp.inv.naturality (H.d n m)

end AlgebraicGeometry
