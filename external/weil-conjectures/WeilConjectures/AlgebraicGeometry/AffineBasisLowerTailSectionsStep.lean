/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Affine-basis lower truncation tower inputs
Source: Stacks Project, Tags 0BKT, 0D64, 071B and 08D4. -/

@[expose] public section
universe u wC wA
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing transfers through the open-restriction and source comparisons.
Source: Stacks Project, Tags 01E1 and 03FD. -/
private theorem evaluation_rightDerived_isZero
    (X : Scheme.{u}) (V : X.Opens) (M : X.Modules) (q : ℕ)
    (hM : Subsingleton ((M.restrict V.ι).H (q + 1))) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    let G := S ⋙ forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
    IsZero ((G.rightDerived (q + 1)).obj M) := by
  dsimp only
  obtain ⟨e, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison
    V.toScheme (q + 1)
  have hzero : IsZero ((forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace (q + 1)).obj
        (M.restrict V.ι))) := by
    have : Subsingleton ((RingedSpace.moduleCohomology
        V.toScheme.toRingedSpace (q + 1)).obj (M.restrict V.ι)) :=
      (e (M.restrict V.ι)).injective.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  obtain ⟨c⟩ := nonempty_openRestriction_moduleCohomology_iso X V (q + 1)
  exact hzero.of_iso (c.app M).symm

set_option backward.isDefEq.respectTransparency false in
/-- Positive acyclicity of actual homology sheaves makes the successive lower
truncation transition invertible in degree i once n >= 1-i.
Source: Stacks Project, Tag 0BKT (lemma-cohomology-over-U-trivial), bounded-below
hypercohomology argument, and Tag 08D4, proof of (2).
(blueprint: lem-sc-affine-basis-lower-tail-sections-step).

Proof: The lower-truncation step triangle has first object H^(-n)(E)[n].
Below a this sheaf is H^(-n)(F), and above or at a it is zero. Apply derived
sections and exact forgetting to this triangle. Its first object's homology in
degrees i and i+1 identifies by the shifted-single comparison with positive
right-derived sections in degrees n+i and n+i+1. These are positive since n >= 1-i.
The hypothesis on W=V and the module-cohomology-source comparison on the restriction
to V make both zero. The long exact homology sequence then makes the displayed
transition monic and epic, hence invertible. No termwise acyclicity, quasi-coherence,
boundedness or K-injectivity is required. Empty V obeys the same calculation. -/
theorem affineBasisLowerTail_sections_step_isIso
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a i n : ℤ) (hn : 1 - i ≤ n) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    let G := S ⋙ forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
    let t := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let E := (t.truncLT a).obj (DerivedCategory.Q.obj F)
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (G.rightDerivedFunctor.map ((t.natTransTruncGEOfLE
        (-n) (-n + 1) (Int.le_add_one (le_refl (-n)))).app E))) := by
  dsimp only
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let G := S ⋙ forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
  let t := DerivedCategory.TStructure.t (C := C)
  let E := (t.truncLT a).obj ((DerivedCategory.Q (C := C)).obj F)
  let M := (DerivedCategory.homologyFunctor C (-n)).obj E
  have hvan (q : ℕ) : IsZero ((G.rightDerived (q + 1)).obj M) := by
    by_cases hm : -n < a
    · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app
        ((DerivedCategory.Q (C := C)).obj F) a (-n) hm
      let e : M ≅ F.homology (-n) :=
        asIso ((DerivedCategory.homologyFunctor C (-n)).map
          ((t.truncLTι a).app ((DerivedCategory.Q (C := C)).obj F))) ≪≫
          (DerivedCategory.homologyFunctorFactors C (-n)).app F
      have hz := evaluation_rightDerived_isZero X V (F.homology (-n)) q
        (hhomology V hV le_rfl (-n) q)
      exact hz.of_iso ((G.rightDerived (q + 1)).mapIso e)
    · have hz : IsZero M :=
        DerivedCategory.isZero_of_isLE E (a - 1) (-n) (by omega)
      exact (G.rightDerived (q + 1)).map_isZero hz
  have hz (j : ℤ) (hj : 1 ≤ n + j) :
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
        (G.rightDerivedFunctor.obj
          ((DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj M))⟦n⟧))) := by
    let q := (n + j).toNat - 1
    have hp : n + j = ((q + 1 : ℕ) : ℤ) := by dsimp [q]; omega
    let K := (DerivedCategory.singleFunctor C 0).obj M
    let e := (DerivedCategory.singleFunctorIsoCompQ C 0).app M
    let e₁ := G.rightDerivedFunctor.mapIso
      ((shiftFunctor (DerivedCategory C) n).mapIso e.symm)
    let e₂ := (G.rightDerivedFunctor.commShiftIso n).app K
    let e₃ := ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftIso
      n j (q + 1) (by simpa using hp)).app (G.rightDerivedFunctor.obj K)
    exact (hvan q).of_iso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).mapIso (e₁ ≪≫ e₂) ≪≫
        e₃ ≪≫ G.homologyRightDerivedFunctorObjSingleFunctorIso M (q + 1))
  obtain ⟨f, h, hT⟩ := DerivedCategory.exists_lowerTruncationStepTriangle E n
  let T := Pretriangulated.Triangle.mk f
    ((t.natTransTruncGEOfLE (-n) (-n + 1) (Int.le_add_one (le_refl (-n)))).app E) h
  let T' := G.rightDerivedFunctor.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := G.rightDerivedFunctor.map_distinguished T hT
  exact DerivedCategory.isIso_homologyMap_mor₂ T' hT' i (i + 1) rfl
    (hz i (by omega)) (hz (i + 1) (by omega))

end AlgebraicGeometry
