# Quotients from scalar central quotients

`Langlands.quotientOfScalarCentralQuotients` is an internal algebraic
constructor over a field `R` and a group `G`. The field, group, source carrier
`V`, and irreducible target carrier `W` have four independent universes. It
returns an actual intertwiner from `rho` to `sigma` paired with its
surjectivity proof.

The inputs are finite composition length of `rho` as a module over the monoid
algebra, irreducibility of `sigma`, and a function `chi` from the full center
of `G` to `R` giving the scalar action on `sigma`. No multiplicativity of
`chi` is required. Occurrence of `sigma` means a literal surjection onto it
from a subrepresentation. The final input is such an occurrence in `rho`.

The remaining input is a scalar-case extraction rule. It quantifies over
representations `tau` whose carriers lie in the same universe as `V`, over
actual surjections `rho -> tau`, and over exact scalar action of every
central element on `tau` by `chi`. If `sigma` occurs in such a `tau`, the
rule must supply an actual surjection `tau -> sigma`. This is a hypothesis
of the constructor, not an assertion established by this module. In
particular it ranges over quotients of the original `rho`; arbitrary
subquotients are unnecessary. The carrier of `sigma` remains independently
quantified throughout.

The private occurrence dichotomy starts with a surjection `q : S -> sigma`
and an invariant subspace `A` of the ambient representation. Restrict the
ambient projection onto the quotient by `A` to `S`, and let `K` be its
kernel. Irreducibility makes `q` restricted to `K` either surjective or zero.
In the first case the same vectors, viewed inside `A`, give an occurrence
in `A`. In the second case `q` descends through `S / K`; the actual
first-isomorphism equivalence identifies this quotient with the image of
`S` in the quotient by `A`. This gives an occurrence in that quotient. All
maps and subspaces are constructed explicitly, without identifying carrier
universes.

For a central element `z`, the central defect is the intertwining
endomorphism `D = tau(z) - chi(z) * id`. If `sigma` occurs in a finite-length
`tau`, this defect cannot be surjective. Indeed, Noetherianity would first
make it injective. It restricts to an injective endomorphism of the
subrepresentation witnessing occurrence, which is Artinian, so that
restriction would be surjective as well. The quotient map to `sigma`
annihilates this restriction because the central action on `sigma` is the
specified scalar. Surjectivity would force every vector of `sigma` to be
zero, contrary to the nontriviality included in irreducibility.

The implemented reduction is strong induction on the natural-valued finite
composition length of `tau`. If its full central action is already the
specified scalar action, apply the input scalar-case rule. Otherwise some
central defect `D` is nonzero. Its image `A` is nonzero and proper by the
preceding argument. Both `A` and `tau / A` are actual quotients of `tau`,
hence of the original `rho`, and inherit finite length. Additivity of
representation length and nontriviality of both terms show that both have
strictly smaller natural lengths. The occurrence dichotomy locates `sigma`
in one of these terms. Apply the induction hypothesis there and compose
surjections to obtain the required quotient of `tau`. At the start, use
`tau = rho` and the identity map. Classical choice packages the resulting
existence proof into the returned subtype.

This construction is derived solely from the Library's representation
length and exact-sequence results, Mathlib's finite-length module facts,
and the explicit algebraic arguments above. It has internal provenance
and attributes no analytic assertion to a literature source. It assumes no
semisimplicity of a Jacquet module and neither constructs an analytic
projector nor proves the discrete-series Jacquet quotient criterion. Its
application to that criterion still needs independent proofs of the
finite-length and scalar-case analytic inputs. No support, summand,
exhaustion, or Langlands classification theorem is used here.
