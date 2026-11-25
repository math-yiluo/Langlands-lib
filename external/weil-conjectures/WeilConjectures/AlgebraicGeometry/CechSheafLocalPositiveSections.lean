/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.CechEvaluationComparison

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every positive-degree cocycle on an open of U_i has a sectionwise boundary.

Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1 (insertion
homotopy). (blueprint: lem-pc-cech-local-positive-section-boundary)

Proof: An open W of U_i identifies with an open V of X contained in U_i.
Evaluate the isomorphisms e and their differential compatibility hd on V.
For a Cech cocycle, insert i as the first index to construct its primitive:
the extra intersection with U_i is V itself. The alternating differential
of this primitive is the cocycle, because deletion of the inserted index
contributes the cocycle and all other terms cancel by its cocycle equation.
Transport the primitive back through e in degree p and the restriction
isomorphism on sections. These are additive isomorphisms, so hd transports
the boundary equation. This is an assertion on every open, requiring no
sheafification or reflection of exactness. Empty opens and zero modules
satisfy the same insertion formula.
-/
theorem cech_sheaf_restrict_positive_section_boundary
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1))
    (i : ι) (p : ℕ) :
    let K := ((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D
    ∀ (W : (U i).toScheme.Opens) (x : Γ((K.sc (p + 1)).X₂, W)),
      (K.sc (p + 1)).g.app W x = 0 →
        ∃ z : Γ((K.sc (p + 1)).X₁, W), (K.sc (p + 1)).f.app W z = x := by
  let G := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op
  have : G.PreservesZeroMorphisms := { map_zero := by intros; rfl }
  let C := (cechComplexFunctor U).obj
    ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)
  let E : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj D ≅ C :=
    HomologicalComplex.Hom.isoOfComponents e (fun a b hab ↦ by
      obtain rfl : a + 1 = b := hab
      exact (hd a).symm)
  dsimp only
  change ∀ (W : (U i).toScheme.Opens)
      (x : Γ((D.X (p + 1)).restrict (U i).ι, W)),
    ((Scheme.Modules.restrictFunctor (U i).ι).map
      (D.d (p + 1) ((ComplexShape.up ℕ).next (p + 1)))).app W x = 0 →
    ∃ z : Γ((D.X ((ComplexShape.up ℕ).prev (p + 1))).restrict (U i).ι, W),
      ((Scheme.Modules.restrictFunctor (U i).ι).map
        (D.d ((ComplexShape.up ℕ).prev (p + 1)) (p + 1))).app W z = x
  have hn : (ComplexShape.up ℕ).next (p + 1) = p + 2 := by simp
  have hp : (ComplexShape.up ℕ).prev (p + 1) = p := by simp
  rw [hn, hp]
  intro W x hx
  let V : X.Opens := (U i).ι ''ᵁ W
  let T := (evaluation X.Opensᵒᵖ (ModuleCat.{u} Γ(X, ⊤))).obj (op V) ⋙
    forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat
  obtain ⟨c⟩ := TopCat.Presheaf.cech_evaluation_comparison U F.presheafModuleCat V
  have hV : V ≤ U i := by
    exact ((U i).ι.image_le_opensRange W).trans (by simp)
  have hle : ∀ j, U j ⊓ V ≤ U i ⊓ V := fun j ↦
    le_inf (inf_le_right.trans hV) inf_le_right
  have hc := TopCat.Presheaf.exactAt_cechComplex_of_le
    (fun j ↦ U j ⊓ V)
    (F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat) hle p
  have hC : ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).ExactAt (p + 1) :=
    hc.of_iso c.symm
  have hD := hC.of_iso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso E).symm
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hD
  exact hD x hx

end AlgebraicGeometry
