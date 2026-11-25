/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Normal curves over a perfect field are smooth

A connected scheme `X` locally of finite type over a perfect field `k`, whose local rings are
integrally closed domains and of dimension one, is smooth of relative dimension one over `k`:
its local rings are fields or discrete valuation rings, hence regular
(`AlgebraicGeometry.IsRegular.of_isIntegrallyClosed_stalk`), so `X` is smooth over the perfect
field `k` (`AlgebraicGeometry.smooth_of_isRegular`), and the relative dimension of an irreducible
smooth `k`-scheme is its dimension
(`AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`).

This lets statements about smooth geometrically connected curves over a finite field be applied
to curves which are normal, separated, of finite type and of pure dimension one, the form used in
the blueprint (`theorem-rank-one-sheaves-have-finite--1`,
`proposition-no-fixed-class-degree-one--1`).

## Main statements

- `AlgebraicGeometry.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk`
- `AlgebraicGeometry.IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk`
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **A normal connected scheme of dimension one over a perfect field is a smooth curve.** Let
`f : X ⟶ Spec k` be locally of finite type, `k` perfect, `X` connected of dimension one with
local rings integrally closed domains. Then `f` is smooth of relative dimension one: the local
rings of `X` are regular, being fields or discrete valuation rings, so `X` is smooth over `k`,
and `X` is irreducible of dimension one. -/
theorem smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [ConnectedSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X = 1) : SmoothOfRelativeDimension 1 f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular X := IsRegular.of_isIntegrallyClosed_stalk hX hdim.le
  have : Smooth f := smooth_of_isRegular f
  have : IrreducibleSpace X := IsRegular.irreducibleSpace X
  exact (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr (by exact_mod_cast hdim)

/-- **A normal geometrically connected curve of dimension one over a perfect field (e.g. a finite
field) is smooth of relative dimension one** (the hypotheses of blueprint
`theorem-rank-one-sheaves-have-finite--1` and `proposition-no-fixed-class-degree-one--1`:
`U₀` normal, geometrically connected, separated, of finite type and pure of dimension one). -/
theorem IsCurve.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    [GeometricallyConnected f]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X = 1) : SmoothOfRelativeDimension 1 f :=
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton (f := f)
  AlgebraicGeometry.smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk f hX hdim

end AlgebraicGeometry
