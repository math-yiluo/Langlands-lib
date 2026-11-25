/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineDescentRingDiagram

import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.AffineDescentSpectrumIso
import WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectTransport
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedQCoh
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # A perfect model over the coordinate-ring colimit

Source: Stacks Project, Tags 09RF and 08EB.
(blueprint: lem-pc-affine-descent-colimit-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A perfect object on the limit affine base change has a bounded finite-projective
model over the colimit of the actual coordinate-ring diagram. This is a representation
statement, not a descent statement: no finite stage or descended object is asserted.
Source: Stacks Project, Tag 09RF, affine case, and Tag 08EB
(blueprint: lem-pc-affine-descent-colimit-model).

Proof: The affine source and affine base imply every fibre product is affine.
The canonical spectrum comparison is an isomorphism, by the affine tail diagram
comparison: finality preserves the ring colimit, connected base-change limits give
the limit scheme, and affine global sections give the colimit of its stage rings.
Perfectness implies quasi-coherent cohomology. Transport E
along this affine isomorphism and apply perfect_iff_affine_bounded_projective (08EB).
Transport its model comparison back. The resulting associated-sheaf functor is exactly
affineDescentRealization with the colimit-desc map. This proves the stated isomorphism.
The argument applies to the zero ring, empty affine source, and zero object. -/
theorem exists_affine_descent_colimit_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    (Z : Scheme.{u}) [IsAffine Z] (t : Z ⟶ Spec (R.obj i))
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{u}) (U : Y.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hc : IsColimit c)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (hE : (pullback t (Spec.map (c.ι.app i))).IsPerfect E) :
    ∃ P : CochainComplex (ModuleCat.{u} (colimit (affineDescentRings R i t) : CommRingCat.{u})) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (colimit (affineDescentRings R i t) : CommRingCat.{u}) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (colimit (affineDescentRings R i t) : CommRingCat.{u}) (P.X n)) ∧
      Nonempty ((affineDescentRealization (pullback t (Spec.map (c.ι.app i)))
        (colimit (affineDescentRings R i t) : CommRingCat.{u})
        (colimit.desc _ (affineDescentRingCocone R i t c))).obj P ≅ E) := by
  let Y := pullback t (Spec.map (c.ι.app i))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let A := colimit (affineDescentRings R i t)
  let r : A ⟶ Γ(Y, ⊤) := colimit.desc _ (affineDescentRingCocone R i t c)
  let q : Y ⟶ Spec A := Y.toSpecΓ ≫ Spec.map r
  have : IsIso q := isIso_affine_descent_colimit_toSpec R c hc i Z t
  let s := (asIso q).symm
  obtain ⟨e, ⟨he⟩⟩ := Scheme.exists_scheme_iso_derived_equivalence s
  let Eqc : schemeDerivedQCohCategory Y :=
    ⟨E, schemeDerivedQCohProperty_of_isPerfect Y E hE⟩
  have hqc := Scheme.scheme_iso_derived_inverse_preserves_qcoh s e he Eqc
  have hp := Scheme.scheme_iso_derived_inverse_preserves_perfect s e he E hE
  let E' : schemeDerivedQCohCategory (Spec A) := ⟨e.inverse.obj E, hqc⟩
  obtain ⟨P, hb, hf, hp, ⟨hP⟩⟩ :=
    (perfect_iff_affine_bounded_projective A E').mp hp
  refine ⟨P, hb, hf, hp, ⟨?_⟩⟩
  let T := tilde.functor A
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let α := Functor.isoWhiskerLeft T (Scheme.Modules.pullbackIsoPushforwardInv q)
  let eC := (Functor.mapHomologicalComplexCompIso α (.up ℤ)).app P
  exact DerivedCategory.Q.mapIso eC ≪≫ (he.app ((T.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    (e.functor.mapIso hP).symm ≪≫ e.counitIso.app E

end AlgebraicGeometry
