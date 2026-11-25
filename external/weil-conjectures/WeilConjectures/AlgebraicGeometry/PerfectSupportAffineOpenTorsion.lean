/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
import WeilConjectures.AlgebraicGeometry.PerfectSupportAffineModuleModel
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedProjectiveHomPowerTorsion

/-! # Power torsion on an affine open

Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-perfect-support-affine-open-torsion).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- Keep the transport argument independent of the concrete derived sheaf models.
private theorem comp_eq_zero_of_scalar_preimage
    {A : Type*} [CommRing A] {C D : Type*}
    [Category C] [Preadditive C] [Linear A C] [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Full] [F.Additive] {P M : C} {E E' : D}
    (eP : F.obj P ≅ E) (eM : F.obj M ≅ E') (r : A)
    (g : E ⟶ E) (β : E ⟶ E')
    (hscalar : F.map (r • 𝟙 P) ≫ eP.hom = eP.hom ≫ g)
    (hzero : r • F.preimage (eP.hom ≫ β ≫ eM.inv) = 0) : g ≫ β = 0 := by
  have h : F.map ((r • 𝟙 P) ≫ F.preimage (eP.hom ≫ β ≫ eM.inv)) = 0 := by
    rw [Linear.smul_comp, Category.id_comp, hzero, F.map_zero]
  rw [F.map_comp, Functor.map_preimage, ← Category.assoc, hscalar, Category.assoc] at h
  apply (cancel_epi eP.hom).mp
  apply (cancel_mono eM.inv).mp
  simpa only [Category.assoc, zero_comp, comp_zero] using h

/-- Every local morphism from a restricted perfect source into a shift of a restricted
supported target is killed by a power of the global function on an affine open.
Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-perfect-support-affine-open-torsion).

Proof: Compare localized-site restriction with restriction to the open subscheme U.
Perfectness and quasi-coherence restrict, and the stalk comparison restricts the support
condition. Identify the affine U with Spec of its section ring and use the affine derived
equivalence and bounded finite-projective model. Induct on the number of nonzero terms
of the model, simultaneously for all shifts of the target. The stupid-truncation triangle
at the highest term gives an exact Hom sequence. Kill the image in its single-term Hom
by a power f^a; exactness lifts the resulting map from the shorter model. Induction kills
that lift by f^b, so f^(a+b) kills the original map. For a single projective term in degree
zero, Hom in the derived category is Hom into H^0 of the shifted target. This module
localizes to zero at f by the support hypothesis, so each element is killed by a power
of f. Finitely many generators of the source give one exponent for their images.
Transport back along the exact equivalences. Their compatibility with multiplication
identifies this action with precomposition by the restriction of f^n times identity.
The zero complex and the empty affine open give zero Hom groups. -/
theorem perfect_support_affine_open_torsion
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E E' : schemeDerivedQCohCategory X)
    (hE : X.IsPerfect E.obj)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (k : ℤ) (β : R.obj E.obj ⟶ R.obj (E'.obj⟦k⟧)),
      ∃ n : ℕ, R.map (schemeDerivedScalar X (f ^ n) (𝟙 E.obj)) ≫ β = 0 := by
  classical
  intro R k β
  let A : Type u := ↑(X.sheaf.obj.obj (op U))
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨P, M, F, hF, hAdd, hb, hf, hp, hM, eP, eM, hscalar⟩ :=
    perfect_support_affine_module_model X f E E' hE hSupport U hU k
  let α := F.preimage (eP.hom ≫ β ≫ eM.inv)
  obtain ⟨n, hn⟩ := DerivedCategory.bounded_projective_hom_power_torsion
    A (f.val (op U)) P hb hf hp M hM α
  exact ⟨n, comp_eq_zero_of_scalar_preimage (A := A) F eP eM ((f.val (op U)) ^ n)
    (R.map (schemeDerivedScalar X (f ^ n) (𝟙 E.obj))) β (hscalar (f ^ n)) hn⟩

end AlgebraicGeometry.Scheme
