/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Homology.StalkTensorComplexDegrees
import WeilConjectures.Algebra.Homology.StalkTensorComplexDifferential
import Mathlib.Topology.Sheaves.Abelian

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
set_option autoImplicit false
noncomputable section
namespace AlgebraicGeometry

-- Elaborating the two total tensor constructions needs additional heartbeats.
/-- Pinned stalk tensor comparison for complexes.

Proof: fix the chosen canonical module tensor-stalk isomorphisms and their
naturality. The degreewise stalk tensor comparison preserves the total coproduct
injections with these exact component maps. The module stalk functor is additive,
as is seen after forgetting to abelian-group presheaves. Differential compatibility
then follows from naturality of the component maps and preservation of the signed
sum defining the total differential. Assemble the degree isomorphisms with
HomologicalComplex.Hom.isoOfComponents. Its components are definitionally the
degreewise maps, so their injection formula proves the required pinned equation.
Arbitrary coproducts cover unbounded complexes, including zero factors.
Source: Stacks Project, perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-pullback-stalk-square).
-/
theorem exists_pinned_stalk_tensor (Y : Scheme.{u}) (z : Y) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let T := RingedSpace.moduleStalkFunctor Y.toRingedSpace z
    letI := ModuleCat.monoidalCategory (R := Y.presheaf.stalk z)
    let S := T.mapHomologicalComplex (.up ℤ)
    ∃ e : ∀ P Q : CochainComplex Y.Modules ℤ,
      S.obj (pullbackTensorTotal Y P Q) ≅ S.obj P ⊗ S.obj Q,
      ∀ P Q p q n (h : p + q = n),
        T.map (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h) ≫
          (e P Q).hom.f n =
          (Classical.choose (SheafOfModules.stalkTensorIso Y.toRingedSpace z)
            (P.X p) (Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor (S.obj P) (S.obj Q)
              (curriedTensor _) (.up ℤ) p q n h := by
  classical
  let := SheafOfModules.monoidalCategory Y.sheaf
  let T := RingedSpace.moduleStalkFunctor Y.toRingedSpace z
  let φ := Classical.choose (SheafOfModules.stalkTensorIso Y.toRingedSpace z)
  have hφ := (Classical.choose_spec
    (SheafOfModules.stalkTensorIso Y.toRingedSpace z)).2
  obtain ⟨e, he⟩ := CochainComplex.exists_stalk_tensor_degree_iso Y.toRingedSpace z φ
  let : T.Additive := ⟨by
    intro M N f g
    ext m
    change (TopCat.Presheaf.stalkFunctor Ab z).map
      ((PresheafOfModules.toPresheaf _).map (f + g).val) m = _
    change (TopCat.Presheaf.stalkFunctor Ab z).map
      ((PresheafOfModules.toPresheaf _).map (f.val + g.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl⟩
  refine ⟨fun P Q ↦ HomologicalComplex.Hom.isoOfComponents (e P Q)
    (fun n m _ ↦ CochainComplex.stalk_tensor_degree_differential
      Y.toRingedSpace z φ hφ e he P Q n m), ?_⟩
  intro P Q p q n h
  exact he P Q p q n h


end AlgebraicGeometry
