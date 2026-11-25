/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.FiniteProjectiveOpenStalkMapsLift
import Mathlib.Data.Int.Interval

/-! # Lifting reverse-degree stalk components

Source: Stacks Project, Tags 09RE, 0BC7 and 01CP.
(blueprint: lem-sc-perfect-open-stalk-reverse-components-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Lift reverse-degree stalk components without imposing differential equations.
Source: Stacks Project, Tag 09RE, affine case (1); Tag 0BC7 (2);
Tag 01CP, finitely presented internal Hom comparison.
(blueprint: lem-sc-perfect-open-stalk-reverse-components-lift).

Proof: Choose the support interval and the finite-free retractions for P.
Restriction preserves zero terms and these retractions. There are only finitely
many reverse-degree pairs inside the support interval. Sandwich each given stalk
map between the stalk retractions, giving a finite matrix of structure-ring
stalk elements. Represent every entry by a section on a neighbourhood inside T
and intersect the finitely many neighbourhoods. Restrict the retractions and
sandwich the lifted matrices back to obtain k. Set k to zero outside the support
interval and outside the reverse-degree relation. The zero-source or zero-target
criterion proves agreement for every discarded pair. The open-subscheme stalk
comparison gives e: restriction to Z followed by the stalk equals the stalk on V.
Its naturality and preservation of the splitting identities prove the displayed
component equality. Empty support, rank zero, and non-Noetherian stalk rings
require no extra hypotheses. This constructs only components, not a homotopy. -/
theorem exists_perfect_open_stalk_reverse_components_lift
    (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (x : X) (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
    (T : X.Opens) (hTV : T ≤ V) (hxT : x ∈ T)
    (h : ∀ i j : ℤ,
      ((openModuleStalkFunctor X V ⟨x, hxV⟩).obj
        ((((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P).X i)) ⟶
      ((openModuleStalkFunctor X V ⟨x, hxV⟩).obj
        ((((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P).X j)))
    (hzero : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0) :
    ∃ (Z : X.Opens) (hZT : Z ≤ T) (hxZ : x ∈ Z),
      let PV := ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P
      let R := (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (hZT.trans hTV))).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X Z ⟨x, hxZ⟩).mapHomologicalComplex (.up ℤ)
      let F := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      ∃ (e : R ⋙ S ≅ F) (k : ∀ i j : ℤ, (R.obj PV).X i ⟶ (R.obj PV).X j),
        (∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → k i j = 0) ∧
        ∀ i j, (openModuleStalkFunctor X Z ⟨x, hxZ⟩).map (k i j) =
          (e.app PV).hom.f i ≫ h i j ≫ (e.app PV).inv.f j := by
  classical
  obtain ⟨⟨a, b, hbound⟩, hfree⟩ := hP
  let D := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)
  let PV := (D.mapHomologicalComplex (.up ℤ)).obj P
  let J := {n : ℤ // n ∈ Finset.Icc a b}
  let I := ULift.{u} (J × J)
  let : Fintype J := Finset.Subtype.fintype _
  let : Fintype I := inferInstance
  have hPVfree (n : ℤ) : ∃ m : ℕ,
      ∃ (ι : PV.X n ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)) ⟶ PV.X n),
        ι ≫ π = 𝟙 (PV.X n) := by
    obtain ⟨m, i, r, hir⟩ := hfree n
    let c : D.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
        SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)) :=
      (asIso (sigmaComparison D (fun _ : ULift.{u} (Fin m) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
        Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso (homOfLE hVU))
    refine ⟨m, D.map i ≫ c.hom, c.inv ≫ D.map r, ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact D.map_id _
  obtain ⟨Z, hZT, hxZ, e₀, g, hg⟩ :=
    exists_finite_projective_open_stalk_maps_lift X V x hxV T hTV hxT I
      (fun q ↦ PV.X q.down.1.val) (fun q ↦ PV.X q.down.2.val)
      (fun q ↦ hPVfree q.down.1.val) (fun q ↦ h q.down.1.val q.down.2.val)
  let R₀ := SheafOfModules.overMap (moduleRings X.toRingedSpace)
    (homOfLE (hZT.trans hTV))
  let S₀ := openModuleStalkFunctor X Z ⟨x, hxZ⟩
  let R := R₀.mapHomologicalComplex (.up ℤ)
  let e := Functor.mapHomologicalComplexCompIso e₀ (.up ℤ)
  let k (i j : ℤ) (hi : a ≤ i ∧ i ≤ b) (hj : a ≤ j ∧ j ≤ b) :=
    g (ULift.up (⟨i, Finset.mem_Icc.mpr hi⟩, ⟨j, Finset.mem_Icc.mpr hj⟩))
  have hk (i j : ℤ) (hi : a ≤ i ∧ i ≤ b) (hj : a ≤ j ∧ j ≤ b) :
      S₀.map (k i j hi hj) = (e.app PV).hom.f i ≫ h i j ≫ (e.app PV).inv.f j :=
    hg (ULift.up (⟨i, Finset.mem_Icc.mpr hi⟩, ⟨j, Finset.mem_Icc.mpr hj⟩))
  let k' : ∀ i j : ℤ, (R.obj PV).X i ⟶ (R.obj PV).X j := fun i j ↦
    if hi : a ≤ i ∧ i ≤ b then
      if hj : a ≤ j ∧ j ≤ b then
        if (ComplexShape.up ℤ).Rel j i then k i j hi hj else 0
      else 0
    else 0
  refine ⟨Z, hZT, hxZ, e, k', ?_, ?_⟩
  · intro i j hij
    by_cases hi : a ≤ i ∧ i ≤ b
    · by_cases hj : a ≤ j ∧ j ≤ b
      · simp only [k', dite_eq_left hi, dite_eq_left hj, ite_eq_right hij]
      · simp only [k', dite_eq_left hi, dite_eq_right hj]
    · simp only [k', dite_eq_right hi]
  · intro i j
    by_cases hi : a ≤ i ∧ i ≤ b
    · by_cases hj : a ≤ j ∧ j ≤ b
      · by_cases hij : (ComplexShape.up ℤ).Rel j i
        · simpa only [k', dite_eq_left hi, dite_eq_left hj, ite_eq_left hij] using hk i j hi hj
        · simp only [k', dite_eq_left hi, dite_eq_left hj, ite_eq_right hij,
            Functor.map_zero, hzero i j hij, zero_comp, comp_zero]
      · have hz := hbound j (by omega)
        have hz' := (openModuleStalkFunctor X V ⟨x, hxV⟩).map_isZero
          ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
            (homOfLE hVU)).map_isZero hz)
        have hh : h i j = 0 := hz'.eq_of_tgt _ _
        simp only [k', dite_eq_left hi, dite_eq_right hj, Functor.map_zero, hh, zero_comp,
          comp_zero]
    · have hz := hbound i (by omega)
      have hz' := (openModuleStalkFunctor X V ⟨x, hxV⟩).map_isZero
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hVU)).map_isZero hz)
      have hh : h i j = 0 := hz'.eq_of_src _ _
      simp only [k', dite_eq_right hi, Functor.map_zero, hh, zero_comp, comp_zero]

end
end AlgebraicGeometry.Scheme
