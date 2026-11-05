# Proper coherent formal existence over complete local rings

`ProperFormalCoherentExistenceStatement` asserts essential surjectivity of
coherent completion for a proper scheme over a complete local noetherian
commutative ring. Its input is an actual `FormalModuleSystem f m`, for
`m = IsLocalRing.maximalIdeal R`, with locally finitely presented terms.
It asks for an actual locally finitely presented module sheaf `M` on `X`
and a single `FormalModuleSystem.Comparison` from its ordinary restriction
system to the supplied system. Thus the isomorphisms at consecutive
thickenings must commute with every specified transition.

The source is the Stacks Project, Proposition 30.25.4 (Tag 088C), together
with the actual-thickening formulation of Section 30.27, Remark 30.27.2
(Tag 088F). Both are retained in the registered source
`stacks-formal-line-bundle-effectivity-2026-11-03`, in
`literature/Stacks Project - Grothendieck existence and compatible formal
module systems (2026-11-03)/088C.html` and `0CYW.html`.
The source gives an equivalence for any ideal of completeness in a
noetherian ring. This proposition retains only its existence direction
and specializes to the maximal ideal of a local ring. The index is
shifted from the source's `n ≥ 1` to `n : ℕ` and exponent `n+1`.

The schemes in the system are the actual fibre products
`X ×[Spec R] Spec(R / m^(n+1))`. A proper scheme over a noetherian affine
base, and all these thickenings, are noetherian. On them the source's
coherent module condition is expressed by Mathlib's
`SheafOfModules.IsFinitePresentation`: finite free presentations on an
open cover, including quasi-coherence. The same condition is required
of the output.

No projectivity, flatness, smoothness, residue-field or characteristic
condition is imposed. Properness removes any further support condition
in Remark 30.27.2. The statement asserts coherent algebraization; local
rank-one promotion is a separate obligation for the parent formal
line-bundle effectivity proof. No proof of coherent existence is supplied
by this statement.
