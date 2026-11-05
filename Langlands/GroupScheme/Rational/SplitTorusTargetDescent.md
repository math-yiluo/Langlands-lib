# Descending a homomorphism together with its split torus target

Worker 1485 constructs this internal adapter to the actual Hom equivalence
from `SplitTorusHomBaseChange`, whose character descent uses Worker 1376's
construction. Its provenance is that Hom equivalence and the definition of
an actual split torus. No external assertion is transcribed.

Let `k` and `K` be fields in any common universe `u`, with any field extension
`K/k`. Let `G` be a reduced affine actual group scheme over `k` with
`HasPointedSplitTorusDomination G`. Given any supplied actual split torus `D`
over `K` and actual homomorphism `g : G_K → D`,
`HasPointedSplitTorusDomination.descendSplitTorusHom` constructs
`SplitTorusHomDescentData G D g`.

The returned data consist of an actual group scheme `target` over `k`, its
split-torus predicate, an actual homomorphism `hom : G → target`, an actual
group-scheme isomorphism `recovery : target_K ≅ D`, and the equality
`baseChange(hom) ≫ recovery.hom = g`. Thus both the target and map are
recovered after actual scalar extension. The equality is of represented
group-scheme morphisms and therefore holds on every scheme test.
The result uses no previously supplied ground-field form of `D`.

The construction chooses a finite coordinate splitting `D ≅ Gm_K^I`,
takes `target = Gm_k^I`, and combines the canonical split-torus base-change
comparison with the inverse of that chosen splitting to obtain `recovery`.
It applies the inverse of `splitTorusHomEquiv` to `g ≫ recovery.inv`.
The Hom equivalence's recovery law and the isomorphism identities give
the stored equation. The choice of target and its splitting is
noncanonical; no uniqueness across different target choices is claimed.

No smoothness, connectedness, solvability, finite-type, characteristic,
perfectness, infinitude, algebraicity or separability assumption is added.
The construction supplies no dominance, fppf quotient property or kernel
geometry. It does not construct a geometric radical or prove split
unipotence, and it does not prove the host split geometric radical theorem.
