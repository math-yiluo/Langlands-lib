# Descent of central isogenies with Galois-invariant full kernels

This internal construction combines the published descent theorems for
Galois-invariant closed subgroups and affine fppf quotients with fpqc
reflection of central isogenies. It introduces no classification input.

For schemes `B`, `S` and a morphism `b : S ⟶ B`, let `G` be a group scheme
over `B`, let `Q` be a group scheme over `S`, and let
`q : G_S ⟶ Q` be an actual homomorphism. The structure
`Descent.CentralIsogenyRecovery b q` contains an actual group scheme `R`
over `B`, a homomorphism `r : G ⟶ R`, proofs that the total scheme of `R`
is affine and that `r` is a central isogeny, and an isomorphism
`e : R_S ≅ Q` satisfying the exact equation
`(baseChange b).map r ≫ e.hom = q`.
The structure itself assumes neither that `b` is a cover nor that the
supplied `q` is a central isogeny; those are conditions of its construction.

The theorem
`Descent.nonempty_centralIsogenyRecovery_of_galoisInvariant_kernel`
constructs such recovery data when `K/k` is a Galois field extension,
`G` is affine over `k`, `Q` has affine total scheme over `K`, and `q`
is a central isogeny. Its additional hypothesis is equality of the full
range subgroup functors

`range (radicalGaloisHom (kernelι q) σ) = range (kernelι q)`

for every `k`-algebra automorphism `σ` of `K`. Here `radicalGaloisHom`
is the existing canonical base-change transport into the original
base-changed ambient group. Despite its historical name, this expression
transports the actual inclusion, without taking the reduced subgroup.
The equality is on every test scheme over `K`.

The implemented proof has three steps. First, affineness of `Q` makes
its unit a closed immersion, so the full kernel inclusion of `q` is
closed. The existing theorem
`Descent.GaloisInvariantClosedSubgroup.exists_descent` descends that
inclusion to `i : N ⟶ G`, with a source recovery isomorphism and an
equation identifying its base change with the kernel inclusion.
Precomposing an inclusion with an isomorphism preserves its range,
so this equation identifies the extended range of `i` with the full
kernel of `q`. Flatness, surjectivity and local finite presentation
of `q` then make it an fppf quotient by that range.

Second, `Descent.exists_affine_fppfQuotient` descends this supplied
quotient to an affine target `R` and an actual arrow `r`, together
with the isomorphism `e` and the exact recovery equation above.
Quasi-compactness needed by that theorem follows from finiteness of
the original central isogeny. Third, transport through `e` shows
that the base change of `r` is a central isogeny, and
`centralIsogenyFpqcReflection` reflects that property to `r`.
The field extension is fpqc, as provided by `fieldExtension_fpqc`.

`Descent.centralIsogenyRecoveryOfGaloisInvariantKernel` chooses the
resulting recovery structure using classical choice. Its fields retain
the arrow, its central-isogeny property, the actual target isomorphism
and the commuting equation for further transport arguments.

The construction permits infinite Galois extensions and all
characteristics. It requires no smoothness, reducedness, connectedness
or finite type hypothesis on `G` or `Q` beyond the explicit assumptions
above. In particular it does not replace a possibly infinitesimal
kernel by its field-valued points. For the type-D application it
supplies the descent step once a correctly numbered split vector
cover and invariance of its full kernel have been proved; it does
not prove either of those inputs or the aligned spin-cover theorem.
