/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategoryComparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.Restriction

/-!
# Comparison of the two notions of perfect complexes on a scheme

`AlgebraicGeometry.Scheme.IsPerfect X E` asks that, locally on `X`, the restriction of
`E ∈ schemeDerivedCategory X` to the site over an open `U` be represented by a strictly perfect
complex: a bounded complex whose terms are direct summands of finite free modules.
`AlgebraicGeometry.Scheme.Modules.IsPerfectComplex E'` asks that, locally on affine opens `U`,
the restriction of `E' ∈ DerivedCategory X.Modules` to `U` be represented by a bounded complex
of finite projective `𝒪_U`-modules. We show that they agree along the equivalence
`AlgebraicGeometry.schemeDerivedCategoryEquiv X :
schemeDerivedCategory X ≌ DerivedCategory X.Modules`.

## Main statements

- `AlgebraicGeometry.Scheme.isPerfect_iff_isPerfectComplex`:
  `IsPerfect X E ↔ IsPerfectComplex ((schemeDerivedCategoryEquiv X).functor.obj E)`.

Source: Stacks Project, Cohomology of Sheaves, Definitions 08C4 and 08CM
(blueprint: lemma-coherent-base-change-invertible-sheaves--1).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

section Transport

variable (U : X.Opens)

instance additive_overEquiv_functor : (Modules.overEquiv U).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance additive_overEquiv_inverse : (Modules.overEquiv U).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The free module of rank `m` on the site over `U` corresponds to the free `𝒪_U`-module of
rank `m`. -/
private noncomputable def overEqFreeIso (m : ℕ) :
    (Modules.overEquiv U).functor.obj (SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin m)) :=
  (SheafOfModules.mapFreeIso _ _ (Modules.overEquivFunctorObjUnitIso U)).symm

/-- A strictly perfect complex on the site over `U` corresponds to a bounded complex of finite
projective `𝒪_U`-modules. -/
private lemma isFiniteProjective_of_isStrictlyPerfect
    {K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ}
    (hK : IsStrictlyPerfect X U K) :
    (∃ a b : ℤ,
      CochainComplex.IsStrictlyGE
        ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ) |>.obj K) a ∧
      CochainComplex.IsStrictlyLE
        ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ) |>.obj K) b) ∧
    ∀ n, (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K |>.X n)
      |>.IsFiniteProjective := by
  obtain ⟨⟨a, b, hab⟩, hp⟩ := hK
  refine ⟨⟨a, b, ?_, ?_⟩, fun n ↦ ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (Modules.overEquiv U).functor.map_isZero (hab i (Or.inl hi))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (Modules.overEquiv U).functor.map_isZero (hab i (Or.inr hi))
  · obtain ⟨m, ι, π, h⟩ := hp n
    refine ⟨m, ⟨⟨(Modules.overEquiv U).functor.map ι ≫ (overEqFreeIso X U m).hom,
      (overEqFreeIso X U m).inv ≫ (Modules.overEquiv U).functor.map π, ?_⟩⟩⟩
    change ((Modules.overEquiv U).functor.map ι ≫ (overEqFreeIso X U m).hom) ≫
      (overEqFreeIso X U m).inv ≫ (Modules.overEquiv U).functor.map π = 𝟙 _
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, h, CategoryTheory.Functor.map_id]

/-- A bounded complex of finite projective `𝒪_U`-modules corresponds to a strictly perfect
complex on the site over `U`. -/
private lemma isStrictlyPerfect_of_isFiniteProjective
    (P : CochainComplex U.toScheme.Modules ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ n, (P.X n).IsFiniteProjective) :
    IsStrictlyPerfect X U
      (((Modules.overEquiv U).inverse.mapHomologicalComplex (.up ℤ)).obj P) := by
  refine ⟨⟨a, b, fun n hn ↦ ?_⟩, fun n ↦ ?_⟩
  · refine (Modules.overEquiv U).inverse.map_isZero ?_
    rcases hn with hn | hn
    · exact P.isZero_of_isStrictlyGE a n hn
    · exact P.isZero_of_isStrictlyLE b n hn
  · obtain ⟨r, ⟨ρ⟩⟩ := hP n
    let c : (Modules.overEquiv U).inverse.obj
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) ≅
        SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)) :=
      (Modules.overEquiv U).inverse.mapIso (overEqFreeIso X U r).symm ≪≫
        ((Modules.overEquiv U).unitIso.app _).symm
    refine ⟨r, (Modules.overEquiv U).inverse.map ρ.i ≫ c.hom,
      c.inv ≫ (Modules.overEquiv U).inverse.map ρ.r, ?_⟩
    change ((Modules.overEquiv U).inverse.map ρ.i ≫ c.hom) ≫ c.inv ≫
      (Modules.overEquiv U).inverse.map ρ.r = 𝟙 _
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, ρ.retract,
      CategoryTheory.Functor.map_id]

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [∀ U : X.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]

/-- Restriction to `U` commutes with the comparison `schemeDerivedCategoryEquiv`: on
`schemeDerivedCategory X` it is the derived functor of restriction to the site over `U`,
followed by `overEquiv U`; on `DerivedCategory X.Modules` it is the derived functor of
`Scheme.Modules.restrictFunctor U.ι`. -/
noncomputable def restrictMapDerivedCategoryIso :
    (schemeDerivedCategoryEquiv.{w} X).functor ⋙
        (Modules.restrictFunctor U.ι).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙
        (Modules.overEquiv U).functor.mapDerivedCategory := by
  let O := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have hG : (O ⋙ (Modules.overEquiv U).functor).Additive := inferInstance
  let e : DerivedCategory.Qh ⋙ ((schemeDerivedCategoryEquiv.{w} X).functor ⋙
        (Modules.restrictFunctor U.ι).mapDerivedCategory) ≅
      DerivedCategory.Qh ⋙ (O ⋙ (Modules.overEquiv U).functor).mapDerivedCategory :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (qhCompSchemeDerivedCategoryEquivFunctor.{w} X) _ ≪≫
      (Modules.restrictFunctor U.ι).mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomotopyCategory (F := Modules.restrictFunctor U.ι)
        (G := O ⋙ (Modules.overEquiv U).functor)
        (Modules.overFunctorEquiv U).symm (.up ℤ)) _ ≪≫
      (O ⋙ (Modules.overEquiv U).functor).mapDerivedCategoryFactorsh.symm
  exact (Localization.whiskeringLeftFunctor' DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
      _).preimageIso e ≪≫
    (Functor.mapDerivedCategoryCompIso O (Modules.overEquiv U).functor).symm

end Transport

section Main

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [∀ U : X.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]

/-- **The two notions of perfect complexes agree.** An object `E` of `schemeDerivedCategory X`
is perfect in the sense of `AlgebraicGeometry.Scheme.IsPerfect` (locally on an open cover, its
restriction to the site over an open is strictly perfect) if and only if its image in
`DerivedCategory X.Modules` is perfect in the sense of
`AlgebraicGeometry.Scheme.Modules.IsPerfectComplex` (locally on an affine open cover, its
restriction is a bounded complex of finite projective modules).

Proof: under `Scheme.Modules.overEquiv U`, strictly perfect complexes on the site over `U`
correspond to bounded complexes of finite projective `𝒪_U`-modules, and the restriction
functors correspond (`restrictMapDerivedCategoryIso`). A representative on an open `U` restricts
to a representative on an affine open `V ⊆ U` containing the given point, since restriction of
a free module along an open immersion is free.
Source: Stacks Project, Cohomology of Sheaves, Definitions 08C4 and 08CM
(blueprint: lemma-coherent-base-change-invertible-sheaves--1). -/
theorem isPerfect_iff_isPerfectComplex (E : schemeDerivedCategory X) :
    IsPerfect X E ↔
      Modules.IsPerfectComplex ((schemeDerivedCategoryEquiv.{w} X).functor.obj E) := by
  constructor
  · intro hE x
    obtain ⟨U, hxU, K, hK, ⟨e⟩⟩ := hE x
    obtain ⟨⟨a, b, ha, hb⟩, hP⟩ := isFiniteProjective_of_isStrictlyPerfect X U hK
    let PU := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
    let eU : (Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((schemeDerivedCategoryEquiv.{w} X).functor.obj E) ≅ DerivedCategory.Q.obj PU :=
      (restrictMapDerivedCategoryIso X U).app E ≪≫
        (Modules.overEquiv U).functor.mapDerivedCategory.mapIso e ≪≫
        (Modules.overEquiv U).functor.mapDerivedCategoryFactors.app K
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    let j := X.homOfLE hVU
    let Rj := Modules.restrictFunctor j
    let PV := (Rj.mapHomologicalComplex (.up ℤ)).obj PU
    have := ha
    have := hb
    refine ⟨V, hV, hxV, PV, a, b, ?_, ?_, fun n ↦ ?_, ⟨?_⟩⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact Rj.map_isZero (CochainComplex.isZero_of_isStrictlyGE PU a i hi)
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact Rj.map_isZero (CochainComplex.isZero_of_isStrictlyLE PU b i hi)
    · obtain ⟨r, ⟨ρ⟩⟩ := hP n
      refine ⟨r, ⟨⟨Rj.map ρ.i ≫ (Modules.restrictFreeIso j _).hom,
        (Modules.restrictFreeIso j _).inv ≫ Rj.map ρ.r, ?_⟩⟩⟩
      rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, ρ.retract,
        CategoryTheory.Functor.map_id]
      rfl
    · exact (Functor.mapDerivedCategoryNatIso
          (Modules.restrictFunctorCongr (X.homOfLE_ι hVU).symm ≪≫
            Modules.restrictFunctorComp j U.ι)).app _ ≪≫
        (Functor.mapDerivedCategoryCompIso _ Rj).symm.app _ ≪≫
        Rj.mapDerivedCategory.mapIso eU ≪≫ Rj.mapDerivedCategoryFactors.app PU
  · intro hE x
    obtain ⟨U, -, hxU, P, a, b, ha, hb, hP, ⟨e⟩⟩ := hE x
    refine ⟨U, hxU, ((Modules.overEquiv U).inverse.mapHomologicalComplex (.up ℤ)).obj P,
      isStrictlyPerfect_of_isFiniteProjective X U P a b hP, ⟨?_⟩⟩
    let O := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let i₁ : (Modules.overEquiv U).functor.mapDerivedCategory.obj (O.mapDerivedCategory.obj E) ≅
        DerivedCategory.Q.obj P :=
      ((restrictMapDerivedCategoryIso X U).app E).symm ≪≫ e
    exact ((Functor.mapDerivedCategoryIdIso _).app _).symm ≪≫
      (Functor.mapDerivedCategoryNatIso (Modules.overEquiv U).unitIso).app _ ≪≫
      (Functor.mapDerivedCategoryCompIso (Modules.overEquiv U).functor
        (Modules.overEquiv U).inverse).symm.app _ ≪≫
      (Modules.overEquiv U).inverse.mapDerivedCategory.mapIso i₁ ≪≫
      (Modules.overEquiv U).inverse.mapDerivedCategoryFactors.app P

end Main

end AlgebraicGeometry.Scheme
