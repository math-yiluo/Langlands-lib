# Proof of scheme-morphism factorization from canonical section maps

The theorem `Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions` in
module `Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof` has
type exactly `Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctions.{u}`,
for an arbitrary universe `u`. That published statement (module
`Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctions`) is imported by
name and left unchanged. It says: for schemes `X S Y : Scheme.{u}` and
morphisms `p : X ⟶ S`, `e : S ⟶ X`, `g : X ⟶ Y`, if

1. `e ≫ p = 𝟙 S`,
2. `IsIso (p.app U)` for every open `U : S.Opens`, and
3. `g x = (e ≫ g) (p x)` for every point `x : X`,

then `g = p ≫ e ≫ g` as scheme morphisms. The proof uses no further
assumptions. Composition is in categorical order, and
`f.app U : Γ(T, U) ⟶ Γ(T', f ⁻¹ᵁ U)` is Mathlib's canonical section map of
`f : T' ⟶ T`.

## Proof

The proof has three steps.

**Step 1 (`key`).** Let `W` be an open of `X` with
`hW : p ⁻¹ᵁ (e ⁻¹ᵁ W) = W`. Then the composite section map
`e.app W ≫ p.app (e ⁻¹ᵁ W) : Γ(X, W) ⟶ Γ(X, p ⁻¹ᵁ e ⁻¹ᵁ W)` equals the
restriction map `X.presheaf.map (eqToHom hW).op` along that equality of
opens.

To prove this, write `W = p ⁻¹ᵁ U` with `U = e ⁻¹ᵁ W`, which `hW` permits.
Since `e ⁻¹ᵁ (p ⁻¹ᵁ U)` is definitionally `(e ≫ p) ⁻¹ᵁ U`, the section
equation `e ≫ p = 𝟙 S` gives `hU : e ⁻¹ᵁ (p ⁻¹ᵁ U) = U`.
`Scheme.Hom.comp_app` turns `p.app U ≫ e.app (p ⁻¹ᵁ U)` into
`(e ≫ p).app U`. `Scheme.Hom.congr_app` applied to `e ≫ p = 𝟙 S`, followed
by the identity law, then shows that it equals the restriction
`S.presheaf.map (eqToHom hU).op`. Hypothesis 2 makes `p.app U` invertible, so
`e.app (p ⁻¹ᵁ U) = inv (p.app U) ≫ S.presheaf.map (eqToHom hU).op`.
Substitute this into the composite. The naturality of `p` on the
restriction (`Scheme.Hom.naturality`) moves `p.app U` past the restriction.
Cancelling `inv (p.app U) ≫ p.app U` leaves a restriction map of `X` along
an equality of opens. It agrees with `X.presheaf.map (eqToHom hW).op`
definitionally, because morphisms between opens are proof-irrelevant.

**Step 2 (`hbase`).** The underlying continuous maps agree:
`g.base = (p ≫ e ≫ g).base`. This is checked pointwise (`ext x`).
Hypothesis 3 gives `g x = (e ≫ g) (p x)`, and `Scheme.Hom.comp_apply`
identifies the right-hand side with `(p ≫ e ≫ g) x`.

**Step 3 (extensionality).** `Scheme.Hom.ext` reduces the goal to `hbase`
and, for each open `V : Y.Opens`, the equation
`g.app V ≫ X.presheaf.map (eqToHom _).op = (p ≫ e ≫ g).app V`. The
transport on the left is along `(p ≫ e ≫ g) ⁻¹ᵁ V = g ⁻¹ᵁ V`, which comes
from `hbase`. Applying `hbase` to the preimage of `V` gives
`hW : p ⁻¹ᵁ (e ⁻¹ᵁ (g ⁻¹ᵁ V)) = g ⁻¹ᵁ V`. The right-hand side
`(p ≫ e ≫ g).app V` unfolds definitionally (this is how `Scheme.Hom.comp_app`
is proved) to `g.app V ≫ e.app (g ⁻¹ᵁ V) ≫ p.app (e ⁻¹ᵁ (g ⁻¹ᵁ V))`, and
the proof states it in that form with `change`. Rewriting with `key` at
`W = g ⁻¹ᵁ V` turns the right-hand side into
`g.app V ≫ X.presheaf.map (eqToHom hW).op`. This agrees with the left-hand
side up to the proof of the equality of opens, so `rfl` closes the goal.

## Remarks

Equality of the underlying point maps alone would not suffice. Step 3 also
compares the structure-sheaf maps, and that comparison needs Hypothesis 2
and the section equation through Step 1. Hypothesis 2 is used only on opens
of the form `e ⁻¹ᵁ W` with `p ⁻¹ᵁ (e ⁻¹ᵁ W) = W`. No separatedness or
other geometric hypotheses on `X`, `S`, or `Y` are used.

## Provenance

This is the internal proof obligation for the published internal statement.
The argument follows the route Worker 143 proposed for parent task
`014e89e9-670d-40d8-8e52-26f62f6a0116`: put `h = e ≫ g`, identify
`g ⁻¹ᵁ V` with `p ⁻¹ᵁ (h ⁻¹ᵁ V)`, use `e` to invert `p`'s section map, and
conclude by morphism extensionality. Worker 266 implemented it in Lean for
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` with Lean 4.34.0.
No external literature theorem is claimed.
