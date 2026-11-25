/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Stalk vanishing for a scalar cone

Source: Stacks Project, Tags 08EK and 05QR
(blueprint: lem-sc-scalar-cone-stalk-vanishing).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem homology_linear (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (n : ℤ) :
    letI : Linear
        (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).Linear
      (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let R := RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})
  let : Linear R C :=
    SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
  have : (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).Linear R := by
    constructor
    intro A B f r
    rfl
  have : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).Linear R := by
    change ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n) ⋙
      ShortComplex.homologyFunctor C).Linear R
    infer_instance
  let : Localization.Lifting (DerivedCategory.Q : _ ⥤ DerivedCategory C)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      (DerivedCategory.homologyFunctor C n) :=
    ⟨DerivedCategory.homologyFunctorFactors C n⟩
  exact (Localization.functor_linear_iff (DerivedCategory.Q : _ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
    (DerivedCategory.homologyFunctor C n)).mp inferInstance

private theorem stalk_scalar_apply (X : Scheme.{u}) (x : X)
    (g : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    letI : Linear
        (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
    ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M,
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map (g • 𝟙 M) m =
        X.presheaf.germ ⊤ x trivial (g.val (op ⊤)) • m := by
  let R := RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})
  let : Linear R (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
  intro m
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf _).map (g • 𝟙 M).val)
      (TopCat.Presheaf.germ M.val.presheaf U x hxU m) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ M.val.presheaf U x hxU (g.val (op U) • m) = _
  rw [PresheafOfModules.germ_smul (R := X.toRingedSpace.presheaf) M.val]
  congr 1
  rw [← X.presheaf.germ_res_apply (homOfLE le_top : U ⟶ ⊤) x hxU]
  congr 1
  exact (g.property (homOfLE le_top : U ⟶ ⊤).op).symm

/-- A single scalar cone has zero cohomology stalks at a point where the scalar
is invertible, or where its input already has zero cohomology stalks in every degree.
Source: Stacks Project, Tag 08EK, cone construction, and Tag 05QR
(blueprint: lem-sc-scalar-cone-stalk-vanishing).

Proof: Take the exact sequence H^n(E) → H^n(K) → H^(n+1)(E) of
Mathlib's distinguished-triangle homology sequence and apply the module stalk
exactness theorem. Homology is linear over global sections: its linearity on
complexes follows from short-complex homology linearity, and descends through
localization. On a module stalk, sectionwise scalar multiplication acts by the
scalar's top-section germ, as follows by representing an element on an open
neighborhood and using restriction compatibility. On the basic open this germ
is a unit, so the scalar maps on H^n(E)_x and H^(n+1)(E)_x are isomorphisms.
Cancel them in the two zero composites to show the incoming and connecting
stalk maps are zero. Exactness then makes H^n(K)_x zero. If instead every input
cohomology stalk is zero, the incoming and outgoing maps are zero directly.
In either case a zero module has a subsingleton carrier. -/
theorem scalar_cone_stalk_vanishing (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (g : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E K : schemeDerivedCategory X) (b : E ⟶ K) (d : K ⟶ E⟦(1 : ℤ)⟧)
    (hcone : Triangle.mk (schemeDerivedScalar X g (𝟙 E)) b d ∈
      distTriang (schemeDerivedCategory X)) (x : X)
    (hx : x ∈ X.basicOpen (g.val (op ⊤)) ∨
      ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) :
    ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x)) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let T := Triangle.mk (schemeDerivedScalar X g (𝟙 E)) b d
  have exactStalk (A : ShortComplex C) (hA : A.Exact) : (A.map S).Exact :=
    ((RingedSpace.module_stalk_exact X.toRingedSpace A.f).2.2.2.2
      A.X₃ A.f A.g A.zero).mp hA x
  rcases hx with hx | hx
  · let R := RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})
    let : Linear R C :=
      SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
    have unit := (X.mem_basicOpen_top (g.val (op ⊤)) x).mp hx
    have iso (n : ℤ) :
        IsIso (S.map ((DerivedCategory.homologyFunctor C n).map T.mor₁)) := by
      have := homology_linear X n
      rw [show T.mor₁ = g • 𝟙 E from rfl, Functor.map_smul]
      rw [(DerivedCategory.homologyFunctor C n).map_id E]
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      change Function.Bijective (fun m => S.map (g • 𝟙 _) m)
      have heq : (fun m : S.obj ((DerivedCategory.homologyFunctor C n).obj E) =>
          S.map (g • 𝟙 _) m) =
          (fun m => X.presheaf.germ ⊤ x trivial (g.val (op ⊤)) • m) := by
        funext m
        exact stalk_scalar_apply X x g _ m
      exact heq.symm ▸ unit.smul_bijective
    intro n
    have h₃ := exactStalk _
      (DerivedCategory.HomologySequence.exact₃ T hcone n (n + 1) rfl)
    have := iso n
    have := iso (n + 1)
    have hb : S.map ((DerivedCategory.homologyFunctor C n).map T.mor₂) = 0 := by
      apply (cancel_epi (S.map ((DerivedCategory.homologyFunctor C n).map T.mor₁))).mp
      rw [comp_zero, ← S.map_comp, ← Functor.map_comp,
        comp_distTriang_mor_zero₁₂ T hcone, Functor.map_zero, S.map_zero]
    have hd : S.map (DerivedCategory.HomologySequence.δ T n (n + 1) rfl) = 0 := by
      apply (cancel_mono
        (S.map ((DerivedCategory.homologyFunctor C (n + 1)).map T.mor₁))).mp
      rw [zero_comp, ← S.map_comp,
        DerivedCategory.HomologySequence.δ_comp T hcone n (n + 1) rfl, S.map_zero]
    exact ModuleCat.subsingleton_of_isZero (h₃.isZero_X₂ hb hd)
  · intro n
    have h := exactStalk _
      (DerivedCategory.HomologySequence.exact₃ T hcone n (n + 1) rfl)
    have hE : IsZero (S.obj ((DerivedCategory.homologyFunctor C n).obj E)) :=
      (ModuleCat.isZero_iff_subsingleton).mpr (hx n)
    have hE' : IsZero (S.obj ((DerivedCategory.homologyFunctor C (n + 1)).obj E)) :=
      (ModuleCat.isZero_iff_subsingleton).mpr (hx (n + 1))
    exact ModuleCat.subsingleton_of_isZero (h.isZero_X₂
      (hE.eq_of_src _ _) (hE'.eq_of_tgt _ _))

end AlgebraicGeometry.Scheme
