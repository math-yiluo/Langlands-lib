/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.PerfectGeneratorExists
import WeilConjectures.AlgebraicGeometry.PerfectGeneratorPullback
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGeneration

/-! # Isomorphisms detected by affine pullbacks of perfect complexes

Source: Stacks Project, Tag 0AA8, first proof paragraph, and Tag 0BQT.
(blueprint: lem-sc-affine-pullback-perfect-detects-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry

/-- Affine pullbacks of perfect complexes detect isomorphisms between quasi-coherent
complexes. Source: Stacks Project, Tag 0AA8, first proof paragraph, and Tag 0BQT.
(blueprint: lem-sc-affine-pullback-perfect-detects-iso).

Proof: Choose a perfect generator P on X and pull it back along g. Complete the
underlying morphism to a distinguished triangle. Its cone has quasi-coherent cohomology.
For every shift of the pulled-back generator, injectivity of Hom into the given
map shifted by one kills the composite into the shifted first term of the triangle.
Exactness and surjectivity at shift zero make each map into the cone factor through
the first triangle arrow and then vanish. The generator
criterion makes the cone zero. The distinguished triangle then makes the morphism
invertible; the fully faithful inclusion reflects this isomorphism. -/
theorem affinePullbackPerfect_detects_iso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (g : X' ⟶ X) [IsAffineHom g]
    {A B : schemeDerivedQCohCategory X'} (φ : A ⟶ B)
    (htest : ∀ (M : schemeDerivedQCohCategory X), Scheme.IsPerfect X M.obj →
      ∀ m n : ℤ, Function.Bijective
        (fun t : ((derivedPullback g).obj M.obj)⟦m⟧ ⟶ A.obj⟦n⟧ ↦ t ≫ φ.hom⟦n⟧')) :
    IsIso φ := by
  classical
  obtain ⟨P, hp, hqc, hgen, _⟩ := exists_perfect_generator X
  let M : schemeDerivedQCohCategory X := ⟨P, hqc⟩
  obtain ⟨hX'⟩ := nonempty_derivedOpenLocalization.{u, w} X'
  obtain ⟨_, _, hgen'⟩ := perfect_generator_pullback g M hp hgen
  let Q := (derivedPullback g).obj P
  obtain ⟨htri, _⟩ := schemeDerivedQCoh_compactlyGenerated X'
  let := htri
  have hqciso : (schemeDerivedQCohProperty X').IsClosedUnderIsomorphisms := by
    constructor
    intro C D e hC n
    exact (SheafOfModules.isQuasicoherent (moduleRings X'.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).mapIso e) (hC n)
  let := hqciso
  obtain ⟨Z, b, c, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ.hom
  let T := Pretriangulated.Triangle.mk φ.hom b c
  have hzqc : schemeDerivedQCohProperty X' Z :=
    (schemeDerivedQCohProperty X').ext_of_isTriangulatedClosed₃ T hT A.property B.property
  have hvan (n : ℤ) (t : Q⟦n⟧ ⟶ Z) : t = 0 := by
    have hc : t ≫ c = 0 := by
      have hi := (htest M hp n 1).1
      apply hi
      simp only [Category.assoc, zero_comp]
      have hh : c ≫ φ.hom⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ T hT
      rw [hh, comp_zero]
    obtain ⟨v, hv⟩ := T.coyoneda_exact₃ hT t hc
    change t = v ≫ b at hv
    change Q⟦n⟧ ⟶ B.obj at v
    let eA := (shiftFunctorZero (schemeDerivedCategory X') ℤ).app A.obj
    let eB := (shiftFunctorZero (schemeDerivedCategory X') ℤ).app B.obj
    obtain ⟨s, hs⟩ := (htest M hp n 0).2 (v ≫ eB.inv)
    dsimp only at hs
    have hs' : (s ≫ eA.hom) ≫ φ.hom = v := by
      have hn := (shiftFunctorZero (schemeDerivedCategory X') ℤ).hom.naturality φ.hom
      dsimp only [Functor.id_map] at hn
      change (s ≫ (shiftFunctorZero (schemeDerivedCategory X') ℤ).hom.app A.obj) ≫
        φ.hom = v
      rw [Category.assoc, ← hn, ← Category.assoc, hs]
      simp [eB]
    have hh : φ.hom ≫ b = 0 := comp_distTriang_mor_zero₁₂ T hT
    rw [hv, ← hs', Category.assoc, hh, comp_zero]
  have hz : IsZero Z := (hgen' ⟨Z, hzqc⟩).2 (by
    intro n
    exact ⟨fun a b ↦ (hvan n a).trans (hvan n b).symm⟩)
  have : IsIso φ.hom := (T.isZero₃_iff_isIso₁ hT).1 hz
  have : IsIso ((schemeDerivedQCohProperty X').ι.map φ) := ‹IsIso φ.hom›
  exact (schemeDerivedQCohProperty X').fullyFaithfulι.isIso_of_isIso_map φ

end AlgebraicGeometry
