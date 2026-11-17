# Supplied schemes representing group-scheme automorphisms

Worker 647.

This internal construction uses the existing `AutomorphicAction` and
`LocalGroupIso` interfaces over an arbitrary scheme. It asserts no
representability theorem.

`AutomorphicAction.localIso a x` is the natural family of automorphisms
induced by a point `x` of the acting group, on every further test scheme.
Its inverse comes from the inverse acting point. `ext_act` detects equality
of actions by their values on all test points.

`GroupAutomorphismScheme G` supplies a group scheme and a universal action
on `G`. On every scheme over the base, its points must correspond
bijectively to all natural local automorphisms of `G`. In particular the
interface concerns actual automorphisms on all tests, including nonreduced
tests, rather than automorphisms of field-valued point groups alone.

`classifyAction` constructs the homomorphism to this supplied automorphism
group induced by any automorphic action. Classification of local
families preserves multiplication by the action law, and is natural under
refinement. The published `homOfPoints` construction then gives the actual
group-scheme homomorphism. Restricting the universal action along it recovers
the original action. The classification map commutes with restriction and
detects equality of actions.

All results are formal consequences of the supplied universal property and
have no reductivity, affineness, smoothness, connectedness or nonemptiness
hypotheses. This is an internal representability adapter, not a claim to
prove the geometric representability of automorphisms.

The all-test extensionality argument reuses `AutomorphicAction.ext_act` from
the foundational `AutomorphicAction` module.
