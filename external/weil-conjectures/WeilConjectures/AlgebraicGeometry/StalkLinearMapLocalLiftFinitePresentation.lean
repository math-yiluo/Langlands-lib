/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.FiniteFreeLocalStalkMapLift
import WeilConjectures.AlgebraicGeometry.FiniteFreeLocalHomZero
import WeilConjectures.AlgebraicGeometry.LocalStalkFactorizationGermComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Spreading one linear map of stalks from a finitely presented source

Source: Stacks Project, Modules, Lemma 01CP, finite presentation argument.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

private theorem lift_of_finiteFree_cokernel
    (X : RingedSpace.{u}) (F G : Modules X) (x : X)
    (U : Opens X) (hxU : x ∈ U) (I J : Type u) [Finite I] [Finite J]
    (a : SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) J ⟶
      SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I)
    (b : SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I ⟶ F.over U)
    [Epi b] (hab : a ≫ b = 0)
    (hb : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ b hab))
    (χ : (moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
      (moduleStalkFunctor X x).obj G) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (φ : (F.homObj G).val.obj (op W)),
      ∀ (Z : Opens X) (k : Z ⟶ W) (hxZ : x ∈ Z) (s : F.val.obj (op Z)),
        TopCat.Presheaf.germ G.val.presheaf Z x hxZ (φ.app (op (Over.mk k)) s) =
          χ (TopCat.Presheaf.germ F.val.presheaf Z x hxZ s) := by
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
  obtain ⟨V, hxV, i, ψ, hψ⟩ := exists_finiteFree_local_stalkMap_lift
    X F G x U hxU I b χ
  let T : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} (R.over V) :=
    SheafOfModules.overMap.{u} R i
  have hrel (Z : Opens X) (k : Z ⟶ V) (hxZ : x ∈ Z)
      (t : (SheafOfModules.free (R := R.over U) J).val.obj
        (op (Over.mk (k ≫ i)))) :
      TopCat.Presheaf.germ G.val.presheaf Z x hxZ
        (ψ.val.app (op (Over.mk k))
          (a.val.app (op (Over.mk (k ≫ i))) t)) = 0 := by
    have hh := hψ Z k hxZ (a.val.app (op (Over.mk (k ≫ i))) t)
    refine hh.trans ?_
    have hz : b.val.app (op (Over.mk (k ≫ i)))
        (a.val.app (op (Over.mk (k ≫ i))) t) = 0 := by
      exact congrArg (fun f ↦ f.val.app (op (Over.mk (k ≫ i))) t) hab
    rw [hz, map_zero, map_zero]
  obtain ⟨W, hxW, j, hzero⟩ := exists_finiteFree_local_hom_zero
    X G x U V hxV i J (T.map a ≫ ψ) (by
      intro Z k hxZ t
      exact hrel Z k hxZ t)
  let S : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} (R.over W) :=
    SheafOfModules.overMap.{u} R j
  have hkill : S.map (T.map a) ≫ S.map ψ = 0 := by
    rw [← S.map_comp]
    exact hzero
  have hc := CategoryTheory.Limits.isColimitCoforkMapOfIsColimit'
    S (by rw [← T.map_comp, hab, T.map_zero])
    (CategoryTheory.Limits.isColimitCoforkMapOfIsColimit' T hab hb)
  let θ : S.obj (T.obj (F.over U)) ⟶ S.obj (G.over V) :=
    (CategoryTheory.Limits.CokernelCofork.IsColimit.desc' hc (S.map ψ) hkill).val
  have hθ : S.map (T.map b) ≫ θ = S.map ψ :=
    (CategoryTheory.Limits.CokernelCofork.IsColimit.desc' hc (S.map ψ) hkill).property
  clear_value θ
  obtain ⟨φ, hφ⟩ := exists_internalHom_of_local_stalk_factorization X F G x U V W hxW i j
    (SheafOfModules.free (R := R.over U) I) b ψ χ hψ θ hθ
  exact ⟨W, hxW, φ, hφ⟩

private theorem lift_of_presentation
    (X : RingedSpace.{u}) (F G : Modules X) (x : X)
    (U : Opens X) (_hxU : x ∈ U) (P : (F.over U).Presentation) [P.IsFinite]
    (χ : (moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
      (moduleStalkFunctor X x).obj G) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (φ : (F.homObj G).val.obj (op W)),
      ∀ (Z : Opens X) (k : Z ⟶ W) (hxZ : x ∈ Z) (s : F.val.obj (op Z)),
        TopCat.Presheaf.germ G.val.presheaf Z x hxZ (φ.app (op (Over.mk k)) s) =
          χ (TopCat.Presheaf.germ F.val.presheaf Z x hxZ s) := by
  exact lift_of_finiteFree_cokernel X F G x U _hxU P.generators.I P.relations.I
    (P.relations.π ≫ CategoryTheory.Limits.kernel.ι P.generators.π)
    P.generators.π (by simp) P.isColimit χ

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One specified stalk-linear map from a finitely presented source is induced
by a local morphism on a neighborhood. This only asserts existence of a lift;
it asserts neither uniqueness nor a comparison isomorphism.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third
paragraph, lifting an element of the displayed finite-coordinate kernel.
(blueprint: lem-weil-pbc-stalk-linear-map-local-lift-finite-presentation)

Proof: Choose a finite free presentation of F near x. Represent the images under
χ of its finitely many generator germs by sections of G on a common smaller
neighborhood. These sections define a morphism from the finite free generator
sheaf to G. Its composite with the finite free relation map has zero stalk,
since the generator-to-F map kills every relation. Each of its finitely many
basis images therefore vanishes after shrinking; intersect those neighborhoods.
The resulting composite is zero as a sheaf morphism. The cokernel universal
property of the presentation now descends this map to a local morphism φ from
F to G. Its stalk map agrees with χ on all generator germs, hence everywhere
because the presentation's stalk generator map is surjective. Naturality of
germs gives the displayed formula for every section over every subneighborhood.
Restriction does not change the stalk, by cofinality of subneighborhoods. Empty
finite sets require no shrinking, so zero source or zero target causes no exception. -/
theorem exists_local_internalHom_of_stalkLinearMap
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X)
    (χ : (moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
      (moduleStalkFunctor X x).obj G) :
    ∃ (U : Opens X) (hxU : x ∈ U) (φ : (F.homObj G).val.obj (op U)),
      ∀ (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
        TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) =
          χ (TopCat.Presheaf.germ F.val.presheaf V x hxV s) := by
  classical
  obtain ⟨D, hD⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  have hxcover := (Opens.coversTop_iff _ D.X).mp D.coversTop
  have hxmem : x ∈ ⨆ d, D.X d := by rw [hxcover]; trivial
  obtain ⟨d, hxd⟩ := Opens.mem_iSup.mp hxmem
  let U := D.X d
  change x ∈ U at hxd
  let P : (F.over U).Presentation := D.presentation d
  have : P.IsFinite := hD.isFinite_presentation d
  clear_value P
  exact lift_of_presentation X F G x U hxd P χ

end AlgebraicGeometry.RingedSpace
