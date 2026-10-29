# Descent of isomorphisms between trivial modules

`Langlands.Scheme.Modules.TrivialIsoDescentStatement` concerns actual sheaves of
modules on schemes. For a quasi-compact flat surjection `p : X ⟶ Y`, let `M` and
`N` be modules on `Y`, each equipped with a global isomorphism to the structure
module. An isomorphism `e : p* M ≅ p* N` is compatible when its forward map
intertwines the canonical `equalCompositeIso` comparisons for every scheme `U`
and every pair `a,b : U ⟶ X` with `a ≫ p = b ≫ p`.

The proposition states that such an `e` is the actual pullback of a unique
isomorphism `e₀ : M ≅ N`. The conclusion is literal equality of isomorphisms
under `mapIso`, and the premise only constrains the forward map.

This is an internal consequence of compatible-global-unit descent and the
published structure-module scalar equivalence. The chosen base trivializations
normalize `e` to an automorphism of the structure module on `X`; canonical
comparison compatibility makes its unit compatible on equal-composite pairs.
`Langlands.Scheme.CompatibleUnitsDescentStatement`, proved using Mathlib's
effective-epimorphism theorem and the existing multiplicative-group representing
equivalence, supplies the descended unit. Transporting its automorphism through
the base trivializations gives the desired isomorphism. Pullback injectivity for
units follows from epimorphism cancellation under the same representing
equivalence, and supplies uniqueness.

The statement imposes global trivializations on both base modules. It does not
assert descent between arbitrary line bundles or effectivity of object descent,
and it does not establish the host kernel-character classification.
