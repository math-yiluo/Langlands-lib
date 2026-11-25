/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteLineComparisons
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassLinePullbackHorizontal
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation

/-! # Pullback of the ordinary roots-of-unity line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] lineModule
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem adjoint_evaluation_of_unit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F' ⊣ G') (p : C ⥤ C') (q : D ⥤ D')
    (e : F ⋙ q ≅ p ⋙ F') (d : G ⋙ p ≅ q ⋙ G')
    {M : C} {N : D}
    (hu : p.map (a.unit.app M) ≫ d.hom.app (F.obj M) ≫ G'.map (e.hom.app M) =
      a'.unit.app (p.obj M)) (h : F.obj M ⟶ N) :
    p.map ((a.homEquiv _ _) h) ≫ d.hom.app N =
      (a'.homEquiv _ _) (e.inv.app M ≫ q.map h) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn := d.hom.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc]
  have he : p.map (a.unit.app M) ≫ d.hom.app (F.obj M) =
      a'.unit.app (p.obj M) ≫ G'.map (e.inv.app M) := by
    apply (Iso.eq_comp_inv (G'.mapIso (e.app M))).2
    simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using hu
  rw [he, Category.assoc, ← Functor.map_comp, Adjunction.homEquiv_unit]

private theorem adjoint_evaluation
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M : SpTowerShriek.S l E Y} {N : SpTowerShriek.S l E X}
    (h : g.pull.obj M ⟶ N) (n : ℕ) :
    evaluatedAdjoint l E g h n =
      ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
        ((g.ordinaryPullEvaluation n).inv.app M ≫ (SpTowerShriek.ev l E X n).map h) := by
  simpa only [evaluatedAdjoint, ordinaryAdjoint] using
    adjoint_evaluation_of_unit g.ordinaryAdjunction
      (proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f)
      (SpTowerShriek.ev l E Y n) (SpTowerShriek.ev l E X n)
      (g.ordinaryPullEvaluation n) (g.ordinaryPushEvaluation n)
      (SpTowerShriek.geometry_unit_evaluation l E b g n M) h

set_option linter.unusedVariables false in
/-- The normalized Tate line is cartesian for the unit-normalized tensor inverse image.

Source: blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (4),
using the scalar extension in clause (2); Stacks 03EL and roots base change.
(blueprint: lem-sfb-tower-class-line-pullback-existence).

Proof: the existing finite Tate comparison theorem, specialized to every actual
coefficient quotient, gives normalized finite isomorphisms. Invertibility of ell
on Y supplies its residue-field invertibility hypotheses on both Y and X.
Conjugate these finite comparisons by the ordinary pull-evaluation isomorphism
and the two canonical lineEvaluation isomorphisms. The horizontal compatibility
lemma says precisely that the resulting isomorphisms commute with the ordinary
system transitions. The systemIsoOfEvaluation_exists theorem therefore assembles
them into an isomorphism of systems with these exact evaluated components.

Evaluation of an ordinary adjoint is the finite adjoint of the evaluated map
transported by the inverse pull-evaluation comparison: this follows from
geometry_unit_evaluation and naturality of the push-evaluation comparison.
Apply this identity to the assembled isomorphism. Cancel the evaluation
comparisons and use naturality of the finite adjunction. The normalized finite
tensor formula is then exactly LinePullback.normalization. This includes empty
charts and imposes no finiteness condition on f.
-/
theorem linePullback_nonempty
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : SpTowerShriek.Geometry l E b f)
    (q : CoefficientPullback l E b f g) (k : TensorPullback l E f g)
    (hY : IsUnit (l : Γ(Y, ⊤))) (cY : Chern l E Y) (cX : Chern l E X)
    (nY : cY.Normalized l E) (nX : cX.Normalized l E) :
    Nonempty (LinePullback l E f g cY cX) := by
  obtain ⟨δ, hδ⟩ := finiteLineComparisons_exists l E (b := b) f hY
  let d := fun n ↦ (g.ordinaryPullEvaluation n).app (lineModule l E cY) ≪≫
    (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).mapIso
      (lineEvaluation l E cY n) ≪≫ δ n ≪≫ (lineEvaluation l E cX n).symm
  obtain ⟨e, he⟩ := SemilinearSections.systemIsoOfEvaluation_exists.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) d
      (fun h ↦ linePullback_components_horizontal l E f g cY cX δ hδ h)
  refine ⟨⟨e, ?_⟩⟩
  intro n U a z
  have hn : evaluatedAdjoint l E g e.hom n ≫
      (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
        (lineEvaluation l E cX n).hom =
      (lineEvaluation l E cY n).hom ≫
        ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
          (δ n).hom := by
    rw [adjoint_evaluation, ← Adjunction.homEquiv_naturality_right,
      ← Adjunction.homEquiv_naturality_left]
    apply congrArg
      ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
    rw [he]
    simp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id,
      Category.comp_id]
  have hs := congrArg (fun t ↦ t.val.app U
    ((lineEvaluation l E cY n).inv.val.app U
      (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
        U.unop a z))) hn
  have hy := congrArg (fun t ↦ t.val.app U
    (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
      U.unop a z)) (lineEvaluation l E cY n).inv_hom_id
  change (lineEvaluation l E cY n).hom.val.app U
    ((lineEvaluation l E cY n).inv.val.app U
      (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
        U.unop a z)) = _ at hy
  change _ = (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
    (δ n).hom).val.app U
      ((lineEvaluation l E cY n).hom.val.app U
        ((lineEvaluation l E cY n).inv.val.app U
          (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
            U.unop a z))) at hs
  rw [hy] at hs
  exact hs.trans (hδ n U a z)

end AlgebraicGeometry.ProEtale.SpTowerClasses
