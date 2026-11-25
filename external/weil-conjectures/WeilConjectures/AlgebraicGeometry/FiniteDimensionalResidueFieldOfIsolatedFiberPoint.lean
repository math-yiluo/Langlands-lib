/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Residue fields at isolated points of fibres

Source: Stacks Project, Morphisms, Lemmas 01TH and 01TG
(blueprint: lem-weil-pbc-isolated-fibre-point-residue-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- An isolated point of a fibre of a locally finite type morphism has finite residue
field extension. Source: Stacks Project, Morphisms, Lemma 01TH, (2) implies (1),
and Lemma 01TG (blueprint: lem-weil-pbc-isolated-fibre-point-residue-finite).

Proof:
1. Put `s = f x` and form `f.fiber s` with projections `p` to `X` and `pi` to
   `Spec kappa(s)` (def-pc-scheme-fibre). By lem-weil-pbc-lft-base-change, `pi` is
   locally of finite type. The fibre homeomorphism identifies `x` with the unique
   point `xi = f.asFiber x` over it; its singleton is open by hypothesis.
2. Apply lem-weil-pbc-lft-over-field-isolated-point-residue-finite to this fibre
   over `kappa(s)` and `xi`: `kappa(xi)` is finite over `kappa(s)` through `pi`.
   By lem-weil-pbc-spec-residue-field-identification, the residue field of
   `Spec kappa(s)` at its unique point is `kappa(s)`. The canonical map to `S`
   induces the identity on that residue field, since its stalk map is the residue map.
3. By lem-weil-pbc-fibre-product-point-residue-field, the residue field at `xi`
   is the fraction field of a prime quotient of `kappa(x) tensor kappa(s)` over
   `kappa(s)`. This tensor product is `kappa(x)`, via `a tensor b` mapping to
   `a * f.residueFieldMap x b`. It is a field, so the prime is zero. Thus the
   residue map induced by `p` is an isomorphism `kappa(x) -> kappa(xi)`, compatible
   with the two actions of `kappa(s)` (def-weil-residue-field).
4. Transport finite dimensionality along this `kappa(s)`-linear isomorphism:
   the extension induced by `f` is finite (def-pc-field-extension). -/
theorem finiteDimensional_residueField_of_isOpen_singleton_asFiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (S.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hq : (f.stalkMap x).hom.QuasiFinite :=
    (f.quasiFiniteAt_iff_isOpen_singleton_asFiber).mpr hx
  have hr : (X.residue x).hom.QuasiFinite :=
    RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ (X.residue_surjective x))
  have hc := hr.comp hq
  rw [← CommRingCat.hom_comp, ← residue_residueFieldMap] at hc
  have hi := RingHom.QuasiFinite.of_comp hc
  let : Algebra.QuasiFinite (S.residueField (f x)) (X.residueField x) := hi
  exact Module.Finite.of_quasiFinite

end AlgebraicGeometry.Scheme.Hom
