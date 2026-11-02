# Effective geometric descent for quasi-coherent modules

This internal construction proves geometric object effectivity for a
quasi-coherent module along an affine flat surjection. It combines the actual
geometric cocycle coalgebra with the ordinary pullback comparison equivalence.
All schemes, including every scheme test in the descent data, retain an
arbitrary universe `u`. The module categories consist of actual ordinary sheaves
of modules; all pullbacks, pushforwards, adjunctions and comparison maps are
the Library functors.

Let `p : X → Y`, let `F` be a module on `X`, and let `D : Datum p F`.
The rank-independent `Datum` and `Str` definitions are those of
`LineBundleFlatDescentStr`. For a module `M` on `Y`, write
`β_M = p*η_M` for the structure map of its comparison coalgebra.
Write `G = p*p_*`, and let `evaluation_F(a,b) : a*G F → b*F` be the map
from `GeometricModuleCoalgebra`, for any `a ≫ p = b ≫ p`.

`evaluation_naturality` states that, for any module morphism `f : A → B`
on `X`,

`a*G(f) ≫ evaluation_B(a,b) = evaluation_A(a,b) ≫ b*f`.

The proof applies naturality of `equalCompositeIso` to `p_*f` and then
naturality of the actual adjunction counit. It needs no geometric or
quasi-coherence assumptions.

`comparison_coaction_evaluation` states

`a*β_M ≫ evaluation_(p*M)(a,b) = E(a,b;M)`,

where `E` is the actual canonical `equalCompositeIso`. Its proof applies
naturality of `E` to `η_M`, combines the two maps inside `b*`, and uses
the left triangle identity `β_M ≫ ε_(p*M) = id`. It likewise needs no
geometric or quasi-coherence assumptions, including none on `M`.

Assume `p` is affine and `F` is quasi-coherent. The module
`GeometricModuleCoalgebra` then supplies `coalgebra D` with underlying module
`F` and structure map `coaction D`. For a coalgebra morphism from the
comparison of `M` to this coalgebra, `coalgebra_hom_compatible` proves

`a*f ≫ θ_D(a,b) = E(a,b;M) ≫ b*f`

on every scheme test. The proof pulls the actual coalgebra-morphism equation
`β_M ≫ G(f) = f ≫ coaction D` back along `a` and postcomposes with
`evaluation_F(a,b)`. The two identities above simplify the left side;
`coaction_evaluation` simplifies the right side. Thus the result establishes
the geometric compatibility of the actual underlying morphism, rather than
identifying geometric descent data with coalgebras by assumption.

`strOfCompatibleIso` takes an actual isomorphism `e : p*M ≅ F`
satisfying this all-test compatibility and constructs `Str D (id Y) M`.
This construction itself requires no geometric or quasi-coherence assumptions.
For a test `g : Z → X`, `h : Z → Y` with `h ≫ id Y = g ≫ p`,
its comparison is the inverse composition comparison from `h*M` to
`g*(p*M)`, followed by `g*e`. Naturality follows from transport of an
inverse composition comparison and transport of a pulled-back morphism.
The compatibility field follows from the assumed equation for `e` and
the formula for `E` through the common composite `h`.

With `p` additionally flat and surjective, `exists_compatible_iso`
uses `exists_module_of_pullbackCoalgebra` to choose `M` and an isomorphism
between its actual comparison coalgebra and `coalgebra D`. Applying the
coalgebra forgetful functor yields the actual isomorphism `p*M ≅ F`;
`coalgebra_hom_compatible` supplies all its overlap equations.
Finally, `exists_str` applies `strOfCompatibleIso` and concludes

`∃ M : Y.Modules, Nonempty (Str D (id Y) M)`.

The provenance is internal: this is a consequence of the published ordinary
pullback comonadicity theorem and the geometric coaction construction, using
only canonical pullback comparisons, adjunction naturality, the left triangle
identity and the existing transport calculus. No effectivity statement for
geometric object cocycles is taken as an input.

The conclusion provides an ordinary module on `Y`; it does not assert that
this module is quasi-coherent or finitely presented, or flat over a further
base. Descending those properties, passing from a single affine flat
surjection to the required topology of coherent families, and proving
`FieldCoherentStackAtlasStatement` remain separate obligations.
