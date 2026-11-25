/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Finite generation of stalks of finite type module sheaves

Source: Stacks Project, Modules, Tag 01B4.
-/

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A finite type module sheaf has finitely generated stalks.

Source: Stacks Project, Modules, Tag 01B4, finite local generating sections.
(blueprint: lem-weil-pbc-finite-type-module-stalk-finite)

Proof: Choose a finite local generating family on a neighbourhood U of x. Its
free-sheaf map is an epimorphism, hence locally surjective on sections. Any germ
of F at x has a representative on an open V inside U. Lift that representative
locally through the generating epimorphism and select a member of the lifting
cover containing x. On this member the lift in the finite free sheaf is a finite
linear combination of its coordinate sections. Taking germs expresses the given
germ in the span of the finitely many generator germs. Thus their finite span is
the whole stalk, proving finite generation. If the family is empty the same
argument says every germ vanishes, so it also covers the zero stalk. No
Noetherian, integral, or quasi-coherent assumption is needed. -/
theorem finite_moduleStalk_of_isFiniteType (X : Scheme.{u}) (F : X.Modules)
    [F.IsFiniteType] (x : X) :
    Module.Finite (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := q.coversTop ⊤ x trivial
  let U : X.Opens := q.X i
  have hxU : x ∈ U := g.le hxV
  let y : U.toScheme := ⟨x, hxU⟩
  let e := overEquiv (X := X) U
  have := hq.isFiniteType i
  let a := (q.generators i).map e.functor
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  let a' := a.ofEpi ((overFunctorEquiv U).hom.app F)
  have : a'.IsFiniteType := inferInstance
  have : Finite a'.I := inferInstance
  let N := (restrictFunctor U.ι).obj F
  have hspan := (generating_sections_iff_stalk_span U.toScheme N a'.s).mp a'.epi y
  have : Module.Finite (U.toScheme.presheaf.stalk y) (N.presheaf.stalk y) := by
    constructor
    rw [← hspan]
    exact Submodule.fg_span (Set.finite_range _)
  let s := restrictStalkNatIso U.ι y
  let σ := (U.stalkIso y).hom.hom
  let ℓ : N.presheaf.stalk y →ₛₗ[σ] F.presheaf.stalk x :=
    { toFun := fun m ↦ (s.hom.app F).hom m
      map_add' := fun m n ↦ map_add (s.hom.app F).hom m n
      map_smul' := by
        intro r m
        obtain ⟨V, hyV, r, rfl⟩ := U.toScheme.presheaf.exists_germ_eq r
        obtain ⟨W, hyW, m, rfl⟩ := N.presheaf.exists_germ_eq m
        have hy : y ∈ V ⊓ W := ⟨hyV, hyW⟩
        rw [← U.toScheme.presheaf.germ_res_apply
            (homOfLE inf_le_left : V ⊓ W ⟶ V) y hy r,
          ← N.presheaf.germ_res_apply (homOfLE inf_le_right : V ⊓ W ⟶ W) y hy m,
          ← Scheme.Modules.germ_smul]
        let r' := U.toScheme.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op r
        let m' := N.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op m
        have hm := ConcreteCategory.congr_hom
          (germ_restrictStalkNatIso_hom_app U.ι y F hy) m'
        have hsm := ConcreteCategory.congr_hom
          (germ_restrictStalkNatIso_hom_app U.ι y F hy) (r' • m')
        have hr := ConcreteCategory.congr_hom (U.germ_stalkIso_hom y hy) r'
        simp only [ConcreteCategory.comp_apply] at hm hsm hr
        change (s.hom.app F).hom _ = _ at hm hsm
        change σ _ = _ at hr
        erw [hsm, hm, hr]
        convert Scheme.Modules.germ_smul F (U := U.ι ''ᵁ (V ⊓ W)) x
          ⟨y, hy, rfl⟩ r' m' using 1
        · congr 1
          have ha := ConcreteCategory.congr_hom
            (smul_restrictAppIso_hom U.ι F (V ⊓ W) r') m'
          change (N.smul r').asHom.hom m' =
            (F.smul ((U.ι.appIso (V ⊓ W)).inv r')).asHom.hom m' at ha
          have happ : U.ι.appIso (V ⊓ W) = Iso.refl _ := Scheme.ofRestrict_appIso _ _ _
          rw [happ] at ha
          change (N.smul r').asHom.hom m' = (F.smul r').asHom.hom m' at ha
          exact ha
        · rfl }
  apply Module.Finite.of_surjective ℓ
  change Function.Surjective (ConcreteCategory.hom (s.hom.app F))
  exact (ConcreteCategory.bijective_of_isIso (s.hom.app F)).surjective

end AlgebraicGeometry.Scheme.Modules
