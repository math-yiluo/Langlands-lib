/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness of stalks of sheaves of modules

Source: Stacks Project, Modules, Section 17.3 (Tag 01AF, `section-kernels`)
and Lemma 01AG (`lemma-abelian`) (blueprint: lem-weil-pbc-module-stalk-exact).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat.Presheaf Opposite
noncomputable section
namespace AlgebraicGeometry.RingedSpace

private instance module_toSheaf_preservesFiniteColimits (X : RingedSpace.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (moduleRings X)) :=
  (CategoryTheory.moduleSheaves_colimits_forgetful (moduleRings X)).2.2.1

private theorem stalk_comp_forget (X : RingedSpace.{u}) (x : X) :
    moduleStalkFunctor X x ⋙ forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} =
      SheafOfModules.toSheaf (moduleRings X) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := by
  rfl

private instance stalk_preservesFiniteLimits (X : RingedSpace.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalkFunctor X x) := by
  let A : ModuleCat.{u} (X.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have hb : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteLimits (moduleStalkFunctor X x ⋙ A) := by
    rw [stalk_comp_forget]
    exact comp_preservesFiniteLimits (SheafOfModules.toSheaf (moduleRings X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x)
  exact preservesFiniteLimits_of_reflects_of_preserves _ A

private instance stalk_preservesFiniteColimits (X : RingedSpace.{u}) (x : X) :
    PreservesFiniteColimits (moduleStalkFunctor X x) := by
  let A : ModuleCat.{u} (X.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have hb : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteColimits (moduleStalkFunctor X x ⋙ A) := by
    rw [stalk_comp_forget]
    exact comp_preservesFiniteColimits (SheafOfModules.toSheaf (moduleRings X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x)
  exact preservesFiniteColimits_of_reflects_of_preserves _ A

/--
Source: Stacks Project, Modules, Section 17.3 (Tag 01AF, `section-kernels`),
and Lemma 01AG (`lemma-abelian`) (blueprint: lem-weil-pbc-module-stalk-exact).

Sectionwise injectivity implies stalkwise injectivity. Stalks preserve the canonical
kernel, cokernel and image (the stalk of the image inclusion has the same range
as the stalk map of φ), and detect exactness of a complex at its middle term.
The mono, epi and exactness assertions in `ModuleCat` express injectivity,
surjectivity and equality of the image with the kernel, respectively. In particular,
the cokernel assertion gives the canonical linear quotient isomorphism.

Proof (the node's steps):
0. Use the sectionwise kernel and functoriality of stalk maps. Any other categorical
   kernel or cokernel is uniquely isomorphic compatibly with its structure map, so
   its stalk description is independent of these choices
   (`situation-conventions`, `def-weil-pbc-module-stalk`).
1. If a germ maps to zero, shrink its representative until its image is zero.
   Sectionwise injectivity makes the representative zero on that neighborhood,
   hence the original germ is zero (`def-weil-pbc-module-stalk`). For a sheaf
   monomorphism the sectionwise kernel inclusion is zero, making every section
   kernel zero; inclusions of submodules are sectionwise injective by definition.
2. The sectionwise kernel inclusion is injective, so its stalk map is injective by
   step 1. A germ annihilated by the stalk map of φ has, after shrinking, a
   representative annihilated by φ; this section belongs to the sectionwise
   kernel. Conversely the composite with φ is zero (`def-weil-pbc-module-stalk`).
3. Form the presheaf Q(U) = G(U)/φ(F(U)) and sheafify it as a module presheaf.
   Every map out of G annihilating φ factors sectionwise through Q and then
   uniquely through its sheafification. This constructs the categorical cokernel
   (`def-weil-presheaf-modules-sheafification`,
   `situation-conventions`).
4. Every germ of Q lifts to a germ of G by sectionwise quotient surjectivity.
   A germ of G maps to zero in Q precisely when, after shrinking, its
   representative lies in the sectionwise image of φ. Thus the stalk quotient
   map is surjective with kernel the image of the stalk map of φ
   (`def-weil-pbc-module-stalk`).
5. Sheafification does not change stalks
   (`lem-weil-pbc-stalk-sheafification-space`). The resulting bijective additive
   stalk map is linear by the module germ action, hence a module isomorphism
   (`def-weil-presheaf-modules-sheafification`, `def-weil-pbc-module-stalk`).
6. The stalk cokernel map is the composite of the quotient map in step 4 and
   the isomorphism in step 5. It is surjective with kernel the image of φ_x;
   the first isomorphism theorem gives the induced linear quotient isomorphism
   (`def-weil-pbc-module-stalk`).
7. The image is the kernel of the cokernel map. Step 2 applied to that map,
   and step 6, identify its stalk inclusion with the image of φ_x. Since
   φ_x factors through this injective inclusion, its map to the stalk image
   is surjective (`situation-conventions`, `def-weil-pbc-module-stalk`).
8. Use `lem-weil-pbc-ringed-space-module-exactness-local-lifting` (2): exactness
   is equivalent to locally lifting every section killed by the second map.
   Such local lifts give a preimage of every kernel germ. Conversely, stalkwise
   exactness gives a preimage germ at each point; represent it by a section
   and shrink until the equality of germs holds on sections. These neighborhoods
   cover the given open and provide the required local lifts
   (`def-weil-pbc-module-stalk`, `def-weil-pbc-exact-sequence`).
-/
theorem module_stalk_exact (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ G) :
    ((∀ (U : Opens X),
        Function.Injective (ConcreteCategory.hom (φ.val.app (Opposite.op U)))) →
      ∀ (x : X), Mono ((moduleStalkFunctor X x).map φ)) ∧
    (∀ (x : X),
      Mono ((moduleStalkFunctor X x).map (kernel.ι φ)) ∧
      ((ShortComplex.mk
          ((moduleStalkFunctor X x).map (kernel.ι φ))
          ((moduleStalkFunctor X x).map φ) (by
            rw [← (moduleStalkFunctor X x).map_comp]
            simp)).Exact)) ∧
    (∀ (x : X),
      Epi ((moduleStalkFunctor X x).map (cokernel.π φ)) ∧
      ((ShortComplex.mk
          ((moduleStalkFunctor X x).map φ)
          ((moduleStalkFunctor X x).map (cokernel.π φ)) (by
            rw [← (moduleStalkFunctor X x).map_comp]
            simp)).Exact)) ∧
    (∀ (x : X),
      Epi ((moduleStalkFunctor X x).map (Abelian.factorThruImage φ)) ∧
      Mono ((moduleStalkFunctor X x).map (Abelian.image.ι φ)) ∧
      LinearMap.range ((moduleStalkFunctor X x).map (Abelian.image.ι φ)).hom =
        LinearMap.range ((moduleStalkFunctor X x).map φ).hom) ∧
    (∀ (H : SheafOfModules.{u} (moduleRings X)) (χ : F ⟶ G) (ψ : G ⟶ H),
      ∀ (h : χ ≫ ψ = 0),
        (ShortComplex.mk χ ψ h).Exact ↔
          ∀ (x : X), ((ShortComplex.mk χ ψ h).map (moduleStalkFunctor X x)).Exact) := by
  -- Transfer exactness through the faithful functors to abelian sheaves and groups.
  have detect (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) :
      S.Exact ↔ ∀ x : X, (S.map (moduleStalkFunctor X x)).Exact := by
    let T := SheafOfModules.toSheaf (moduleRings X)
    rw [← S.exact_map_iff_of_faithful T,
      TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    apply forall_congr'
    intro x
    let A : ModuleCat.{u} (X.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
      forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
    rw [← (S.map (moduleStalkFunctor X x)).exact_map_iff_of_faithful A]
    have hb : Functor.PreservesZeroMorphisms
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x) := inferInstance
    change ((S.map (SheafOfModules.toSheaf (moduleRings X))).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor (X := X.carrier) AddCommGrpCat.{u} x)).Exact ↔
      ((S.map (moduleStalkFunctor X x)).map
        (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})).Exact
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hinj x
    have : Mono φ := by
      constructor
      intro Z a b hab
      ext U z
      apply hinj (unop U)
      exact congrArg (fun f => f.val.app U z) hab
    exact Functor.map_mono (moduleStalkFunctor X x) φ
  · intro x
    refine ⟨Functor.map_mono _ _, ?_⟩
    exact (ShortComplex.exact_kernel φ).map (moduleStalkFunctor X x)
  · intro x
    refine ⟨Functor.map_epi _ _, ?_⟩
    exact (ShortComplex.exact_cokernel φ).map (moduleStalkFunctor X x)
  · intro x
    have := Functor.map_epi (moduleStalkFunctor X x) (Abelian.factorThruImage φ)
    refine ⟨inferInstance, Functor.map_mono _ _, ?_⟩
    have hf := (ModuleCat.epi_iff_surjective
      ((moduleStalkFunctor X x).map (Abelian.factorThruImage φ))).mp inferInstance
    have he : (moduleStalkFunctor X x).map (Abelian.factorThruImage φ) ≫
        (moduleStalkFunctor X x).map (Abelian.image.ι φ) =
          (moduleStalkFunctor X x).map φ := by
      rw [← Functor.map_comp, Abelian.image.fac]
    rw [← he, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr hf)]
  · intro H χ ψ h
    exact detect (ShortComplex.mk χ ψ h)

end AlgebraicGeometry.RingedSpace
