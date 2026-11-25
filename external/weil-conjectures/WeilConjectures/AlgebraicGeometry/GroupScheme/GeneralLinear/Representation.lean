/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.Mathlib.RepresentationTheory.Semisimple

/-!
# Algebraic-group modules

An *algebraic-group module* of a group scheme `G` over a field `k` is a finite-dimensional vector
space `k^m` with a homomorphism of group schemes `r : G ⟶ GL_m`, a rational representation
(`AlgebraicGeometry.GeneralLinearGroup.RationalHom`). The `k`-points of `G` act on `k^m` through
`r`; this is the representation `RationalHom.representation`, and the stable subspaces, the
simple and the semisimple algebraic-group modules are those of this representation.

Simple and semisimple modules are only defined for `k` algebraically closed of characteristic `0`,
the setting of the blueprint. There `G(k)` is schematically dense in an algebraic group `G`, so
stability under `G(k)` is stability under `G`; over a general field it is not.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.representation`: the representation of
  `G(k)` on `k^m` given by a rational representation.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.IsSimple`: simple algebraic-group modules.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.IsSemisimple`: semisimple algebraic-group
  modules.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.isSimple_iff`: a module is simple if and only
  if it is nonzero and has no nonzero proper stable subspace.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.isSemisimple_iff`: a module is semisimple if
  and only if it is a direct sum of simple modules.

## Blueprint

- `det-d-linear`: coefficients and representations; the constructions on representations it
  lists are Mathlib's `Representation`, `Subrepresentation`, `Representation.IsIrreducible`,
  `Representation.IsSemisimpleRepresentation`, `Representation.tprod` and
  `Representation.exteriorPower`.
- `def-wf-algebraic-representations`: `RationalHom` and `RationalHom.representation`.
- `def-wf-simple-module`: `RationalHom.IsSimple`.
- `def-wf-semisimple-module`: `RationalHom.IsSemisimple`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup.RationalHom

variable {k : Type u} [CommRing k] {G : Over (Spec (.of k))} [GrpObj G]
  {m : Type u} [Fintype m] [DecidableEq m]

/-- The algebraic-group module of a rational representation `r : G ⟶ GL_m`: the `k`-points of `G`
act on `k^m` through their images in `GL_m(k)`. (blueprint: `def-wf-algebraic-representations`) -/
noncomputable def representation (r : RationalHom G m) [IsMonHom r] :
    Representation k (AlgebraicGeometry.points G k) (m → k) where
  toFun g := Matrix.toLin' (r.points k g : Matrix m m k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' x y := by simp [Module.End.mul_eq_comp]

@[simp]
theorem representation_apply (r : RationalHom G m) [IsMonHom r] (g : AlgebraicGeometry.points G k) :
    r.representation g = Matrix.toLin' (r.points k g : Matrix m m k) :=
  rfl

end AlgebraicGeometry.GeneralLinearGroup.RationalHom

namespace AlgebraicGeometry.GeneralLinearGroup.RationalHom

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {m : Type u} [Fintype m] [DecidableEq m] (r : RationalHom G m) [IsMonHom r]

/-- A *simple* algebraic-group module: `k^m` is nonzero and has no nonzero proper subspace stable
under `G` (`RationalHom.isSimple_iff`). (blueprint: `def-wf-simple-module`)

Stability is tested on the `k`-points `G(k)` only. This is the scheme-theoretic notion (a
subcomodule, i.e. stable under `G(R)` for every `k`-algebra `R`) because `G` is an algebraic
group, i.e. locally of finite type over `k`, and `k` is algebraically closed of characteristic
`0`, the standing hypotheses of `det-d-linear`: then `G` is reduced (Cartier) and `G(k)` is
schematically dense in `G`. Without these hypotheses the two notions differ, which is why
`[LocallyOfFiniteType G.hom] [IsAlgClosed k] [CharZero k]` are imposed. -/
abbrev IsSimple [LocallyOfFiniteType G.hom] [IsAlgClosed k] [CharZero k] : Prop :=
  r.representation.IsIrreducible

/-- A *semisimple* algebraic-group module: a direct sum of simple modules
(`RationalHom.isSemisimple_iff`). (blueprint: `def-wf-semisimple-module`)

As for `RationalHom.IsSimple`, testing stability on `G(k)` agrees with the scheme-theoretic notion
because `G` is locally of finite type over `k` and `k` is algebraically closed of characteristic
`0`; without these hypotheses it does not. -/
abbrev IsSemisimple [LocallyOfFiniteType G.hom] [IsAlgClosed k] [CharZero k] : Prop :=
  r.representation.IsSemisimpleRepresentation

/-- An algebraic-group module is simple if and only if it is nonzero and its only subspaces
stable under `G` are `0` and `k^m`. (blueprint: `def-wf-simple-module`) -/
theorem isSimple_iff [LocallyOfFiniteType G.hom] [IsAlgClosed k] [CharZero k] :
    r.IsSimple ↔ Nontrivial (m → k) ∧ ∀ U : Submodule k (m → k),
      (∀ g : AlgebraicGeometry.points G k, U ≤ U.comap (Matrix.toLin' (r.points k g))) →
        U = ⊥ ∨ U = ⊤ :=
  Representation.isIrreducible_iff

/-- An algebraic-group module is semisimple if and only if it is a direct sum of simple modules:
there is a set of subspaces stable under `G`, each simple, which are independent and span `k^m`.
(blueprint: `def-wf-semisimple-module`) -/
theorem isSemisimple_iff [LocallyOfFiniteType G.hom] [IsAlgClosed k] [CharZero k] :
    r.IsSemisimple ↔ ∃ s : Set (Subrepresentation r.representation),
      (∀ U ∈ s, U.toRepresentation.IsIrreducible) ∧
        iSupIndep (fun U : s ↦ U.1.toSubmodule) ∧ ⨆ U : s, U.1.toSubmodule = ⊤ :=
  Representation.isSemisimpleRepresentation_iff_exists_iSupIndep

end AlgebraicGeometry.GeneralLinearGroup.RationalHom
