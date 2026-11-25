/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Sectionwise short exactness of étale Čech complexes

Source: Stacks Project, Cohomology on Sites, Lemma 03F9, proof.
(blueprint: lem-weil-pbc-etale-cech-sectionwise-short-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The categorical Čech functor preserves zero morphisms.
Source: Stacks 03AO, functoriality of the Čech complex.
(blueprint: lem-weil-pbc-etale-cech-sectionwise-short-exact). -/
instance etale_cech_preservesZero (X : Scheme.{u}) (U : X.Etale)
    {T : Type (u + 1)} (V : T → X.Etale) (f : ∀ t, V t ⟶ U) :
    (cechComplexFunctor (fun t ↦ Over.mk (f t)) :
      ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ _).PreservesZeroMorphisms where
  map_zero := by
    intro F G
    apply HomologicalComplex.Hom.ext
    funext p
    apply Pi.hom_ext
    intro a
    simp [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp]

/-- A short exact sheaf sequence which is surjective on all intersections of a family
induces a short exact sequence of Čech complexes.

Source: Stacks Project, Cohomology on Sites, Lemma 03F9, proof, the paragraph beginning
"Hence for any U in Cov we get a short exact sequence of Cech complexes".
(blueprint: lem-weil-pbc-etale-cech-sectionwise-short-exact).

Proof: Evaluation of abelian sheaves is left exact: the inclusion into presheaves and
object evaluation preserve finite limits. Thus at each iterated fibre product the
sequence is exact on the left. The assumed surjectivity makes it short exact there.
In degree p the Čech functor takes the product of these sequences over all tuples of
p+1 indices, and acts on morphisms by the product of their section maps. Arbitrary
products in abelian groups are exact, including an empty product, so the sequence in
each degree is short exact. The criterion for short exactness of homological complexes
then gives short exactness of the sequence of Čech complexes. No covering hypothesis
is required in this step: only exactness on the specified intersections is used. -/
theorem etale_cech_shortExact_of_sections
    (X : Scheme.{u})
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (U : X.Etale) (T : Type (u + 1))
    (V : T → X.Etale) (f : ∀ t, V t ⟶ U)
    (hsurj : ∀ (p : ℕ) (a : Fin (p + 1) → T),
      Function.Surjective (S.g.hom.app
        (op (piObj (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))).left))) :
    (S.map (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op ⋙
      cechComplexFunctor (fun t ↦ Over.mk (f t)))).ShortExact := by
  classical
  have := hS.mono_f
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  let W : (Fin (p + 1) → T) → X.Etaleᵒᵖ := fun a ↦
    op (piObj (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))).left
  let Q := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ _).obj (Discrete.functor W)
  have hQ : (S.map Q).ShortExact := by
    refine ShortComplex.ShortExact.mk'
      (hS.exact.map_of_mono_of_preservesKernel Q inferInstance inferInstance) ?_ ?_
    · change Mono (Q.map S.f)
      infer_instance
    · have he : ∀ a, Epi ((S.map Q).g.app a) := fun a ↦
        (AddCommGrpCat.epi_iff_surjective _).2 (hsurj p a.as)
      exact NatTrans.epi_of_epi_app _
  have hL := hQ.map_of_exact (lim (J := Discrete (Fin (p + 1) → T)))
  apply ShortComplex.shortExact_of_iso _ hL
  refine ShortComplex.isoMk
    (Pi.isoLimit (Q.obj S.X₁)).symm
    (Pi.isoLimit (Q.obj S.X₂)).symm
    (Pi.isoLimit (Q.obj S.X₃)).symm ?_ ?_
  · change (Pi.isoLimit (Q.obj S.X₁)).inv ≫
        Limits.Pi.map (fun a ↦ S.f.hom.app (W a)) =
      lim.map (Q.map S.f) ≫ (Pi.isoLimit (Q.obj S.X₂)).inv
    apply Pi.hom_ext
    intro a
    rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc,
      Pi.isoLimit_inv_π (Q.obj S.X₁) a, Category.assoc]
    erw [Pi.isoLimit_inv_π (Q.obj S.X₂) a]
    exact (limMap_π (Q.map S.f) ⟨a⟩).symm
  · change (Pi.isoLimit (Q.obj S.X₂)).inv ≫
        Limits.Pi.map (fun a ↦ S.g.hom.app (W a)) =
      lim.map (Q.map S.g) ≫ (Pi.isoLimit (Q.obj S.X₃)).inv
    apply Pi.hom_ext
    intro a
    rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc,
      Pi.isoLimit_inv_π (Q.obj S.X₂) a, Category.assoc]
    erw [Pi.isoLimit_inv_π (Q.obj S.X₃) a]
    exact (limMap_π (Q.map S.g) ⟨a⟩).symm

end AlgebraicGeometry.Scheme
