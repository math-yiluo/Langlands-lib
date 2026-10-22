# Scheme-morphism factorization from canonical section maps

The proposition `Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctions`
in `Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctions` states the
following internal factorization criterion. It is a Prop-valued definition;
this contribution does not prove it.

For every universe `u`, the proposition quantifies over arbitrary schemes
`X S Y : Scheme.{u}` and scheme morphisms `p : X ⟶ S`, `e : S ⟶ X`, and
`g : X ⟶ Y`. It asserts that these three hypotheses imply
`g = p ≫ e ≫ g` as scheme morphisms:

1. `e ≫ p = 𝟙 S`: the map `e` is a section of `p`.
2. For every open subset `U : S.Opens`, `IsIso (p.app U)` holds. Here
   `p.app U : Γ(S, U) ⟶ Γ(X, p ⁻¹ᵁ U)` is the canonical homomorphism of
   commutative rings induced by `p`. The hypothesis concerns this actual map
   on every open, rather than the existence of abstract ring isomorphisms or
   a condition just on global sections over the whole scheme.
3. For every point `x` of the underlying topological space of `X`,
   `g x = (e ≫ g) (p x)` in the underlying point type of `Y`. The expressions
   use Mathlib's function coercion for scheme morphisms, so the right-hand
   side is `g (e (p x))`. This is an equality of the actual underlying maps.

Composition is written in categorical order: `e ≫ p` means first `e`, then
`p`. The conclusion says that `g` factors through `p` with specified factor
`e ≫ g : S ⟶ Y`. It is equality of full scheme morphisms, including their
structure-sheaf maps. The statement imposes no group structure, finiteness,
separatedness, reducedness, smoothness, properness, or noetherian hypotheses.

## Provenance and rationale

This is internal mathematical content proposed by Worker 143 for the
pointed-morphism rigidity development on parent task
`014e89e9-670d-40d8-8e52-26f62f6a0116`, and formalized and documented by
Worker 155. It is not attributed as a verbatim result from external literature.
The declaration uses the scheme and morphism APIs of Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, with Lean 4.34.0.

The intended sheaf-theoretic rationale is as follows; it is motivation for a
separate proof obligation, not a proof supplied by this contribution. Put
`h = e ≫ g`. For an open `V` of `Y`, pointwise equality identifies
`g ⁻¹ᵁ V` with `p ⁻¹ᵁ (h ⁻¹ᵁ V)`. The section equation identifies the further
preimage along `e` with `h ⁻¹ᵁ V`. The isomorphism hypothesis on
`p.app (h ⁻¹ᵁ V)`, together with the section equation, makes the corresponding
section map induced by `e` its inverse after transporting along these equal
opens. Functoriality then permits comparison of the section maps of `g` and
`p ≫ h`; morphism extensionality also needs their already given equality on
points. Any proof must account for these transports and the structure-sheaf
maps explicitly: equality on underlying points alone is insufficient.

In the pinned Mathlib, `Scheme.Hom.app` is the canonical section map,
`Scheme.Hom.comp_apply` describes the underlying point map of a composite,
`Scheme.Hom.comp_app` describes its section maps, and `Scheme.Hom.ext`
compares both the base maps and section maps with the required open transport.
Independent statement review and Library publication precede the separate
exact-target proof task.
