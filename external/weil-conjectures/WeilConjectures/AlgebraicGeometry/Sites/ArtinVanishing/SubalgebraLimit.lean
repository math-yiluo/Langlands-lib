/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Torsion cohomological dimension through finitely generated subalgebras

An algebra `S` over a field `L` is the filtered union of its finitely generated `L`-subalgebras
`A` (`CommRingCat.isColimitFGSubalgebraCocone`), so that `Spec S` is the limit of the affine
schemes `Spec A`, with affine transition maps. A uniform bound `cd_tor(Spec A) ≤ n` therefore
passes to `Spec S`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.spec_of_forall_fg`), by
`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry.Scheme

/-- If `cd_tor(Spec A) ≤ n` for every finitely generated `L`-subalgebra `A` of an algebra `S`
over a field `L`, then `cd_tor(Spec S) ≤ n`: `Spec S` is the limit of the `Spec A`. -/
theorem HasTorsionCohomologicalDimensionLE.spec_of_forall_fg {L : Type u} [Field L]
    (S : Type u) [CommRing S] [Algebra L S] {n : ℕ}
    (h : ∀ A : Subalgebra L S, A.FG → (Spec (.of A)).HasTorsionCohomologicalDimensionLE n) :
    (Spec (.of S)).HasTorsionCohomologicalDimensionLE n := by
  let D := (fgSubalgebraDiagramOf L S).op ⋙ Scheme.Spec
  have : ∀ i, CompactSpace (D.obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (Spec (.of i.unop.1)))
  have : ∀ i, QuasiSeparatedSpace (D.obj i) :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (Spec (.of i.unop.1)))
  have : ∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g) :=
    fun g ↦ inferInstanceAs (IsAffineHom (Spec.map ((fgSubalgebraDiagramOf L S).map g.unop)))
  exact HasTorsionCohomologicalDimensionLE.of_isLimit (n := n) D
    (Scheme.Spec.mapCone (fgSubalgebraCoconeOf L S).op)
    (isLimitOfPreserves Scheme.Spec (isColimitFGSubalgebraCocone L S).op)
    fun i ↦ (h i.unop.1 i.unop.2 :)

end AlgebraicGeometry.Scheme
