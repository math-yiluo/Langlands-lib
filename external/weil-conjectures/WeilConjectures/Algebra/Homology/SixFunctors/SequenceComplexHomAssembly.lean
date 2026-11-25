/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos

/-! # Assembling chain maps from compatible finite components

Source: Stacks 0941, the category of modules on the ringed sequence site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- A family of chain maps commuting with every horizontal transition assembles
uniquely into a chain map on the ringed sequence site.

Source: Stacks 0941, strict systems as modules on the sequence site.
Proof: use the equivalence between sequence modules and strict semilinear systems.
In degree i the finite maps form a system morphism by the horizontal equation.
Their chain equations hold at every level, hence in the system category. Full
faithfulness of the equivalence lifts this chain map uniquely to sequence modules.
(blueprint: lem-coef-sequence-complex-hom-assembly). -/
theorem sequenceComplexHom_existsUnique
    (X Y : CochainComplex (systemSequenceModules B) ℤ)
    (f : ∀ n : ℕ,
      ((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj X ⟶
        ((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj Y)
    (hf : ∀ (i : ℤ) {m n : ℕ} (h : m ≤ n),
      (f n).f i ≫ sequenceSystemTransition B (Y.X i) h =
        sequenceSystemTransition B (X.X i) h ≫ (systemRestriction B h).map ((f m).f i)) :
    ∃! g : X ⟶ Y, ∀ n : ℕ,
      ((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).map g = f n := by
  let F := (strictSystemSequenceEquivalence B).inverse
  let a (i : ℤ) : F.obj (X.X i) ⟶ F.obj (Y.X i) :=
    { app := fun n ↦ (f n).f i
      comm := hf i }
  have ha (i j : ℤ) : F.map (X.d i j) ≫ a j = a i ≫ F.map (Y.d i j) := by
    apply strictRingSystem_hom_ext
    intro n
    exact ((f n).comm i j).symm
  let g : X ⟶ Y :=
    { f := fun i ↦ F.preimage (a i)
      comm' := by
        intro i j _
        apply F.map_injective
        simpa only [Functor.map_comp, Functor.map_preimage] using (ha i j).symm }
  have hg (n : ℕ) :
      ((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).map g = f n := by
    apply HomologicalComplex.hom_ext
    intro i
    exact congrArg (fun t ↦ t.app n) (F.map_preimage (a i))
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply HomologicalComplex.hom_ext
  intro i
  apply F.map_injective
  apply strictRingSystem_hom_ext
  intro n
  exact congrArg (fun t ↦ t.f i) ((hg' n).trans (hg n).symm)

end SheafOfModules
