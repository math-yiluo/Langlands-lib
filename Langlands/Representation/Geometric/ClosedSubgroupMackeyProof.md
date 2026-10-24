# Natural closed-subgroup Mackey support filtration

`Langlands.Geometric.closedSubgroupMackeyFiltration` proves exactly the
published proposition `ClosedSubgroupMackeyFiltration.{uG,uV}`. The group
and representation carrier universes remain independent. The statement
and all its imported definitions are unchanged.

## Scope and conclusion

Let `G` be a nonarchimedean locally compact Hausdorff sigma-compact group,
let `P,Q` be closed subgroups, and let `s : OrderedDoubleCosets P Q n`
be any specified finite orbit ordering. For every `i : Fin n`, the theorem
supplies a natural isomorphism from the actual quotient functor
`(s.supportFiltration (R := ℂ)).graded i` to
`orbitPiece P Q (s.representative i)`.

The input category consists of all smooth complex representations of `P`
in the specified carrier universe and their intertwining maps. There are
no admissibility, dimension, or length restrictions. For a representative
`w`, the orbit is `P*w⁻¹*Q`; its stabilizer inside `Q` consists of the
`q` for which `w⁻¹*q*w` lies in `P`. The orbit piece is compact induction
to `Q` after pulling back the inducing representation along this
conjugation map. The supplied ordering and support filtration are retained.

## Implemented proof

The closing proof introduces the quantified group, topology instances,
closed subgroups, orbit ordering, and index. It then supplies the witness
required by `HasGradedPieces`, using the published construction
`OrderedDoubleCosets.supportGradedOrbitIsoOfExtension` with all geometric
inputs discharged by proved results.

First, `s.cosetOrbit_isLocallyClosed i` supplies local closedness of the
selected orbit. The proved `cosetOrbitHomeomorph` identifies its actual
subspace with the quotient of `Q` by the orbit stabilizer. The theorem
`cosetOrbitHomeomorph_mk` supplies the required representative formula,
sending the class of `q` to the class of `w⁻¹*q`.

Second, the proved `closedOrbitSectionExtension` supplies the extension
assertion used by the assembly. The assembly applies it to the open upper
initial orbit union. The selected orbit lies there as a relatively closed
subset. Thus every compact orbit section is the restriction of an actual
ambient compactly induced function in the upper support step. The
extension proof constructs these functions by prescribed-value local
covariant sections, compact clopen cutoffs, and finite gluing. Their
compact projected nonzero support and a uniform open right stabilizer are
part of the existing compact-induction carrier.

The assembly uses the canonical restriction natural transformation. Its
kernel is exactly the lower support step inside the upper one, and the
extension theorem proves componentwise surjectivity. The published natural
first-isomorphism construction therefore produces an isomorphism on the
specified graded quotient. Its forward map sends the class of a function
to the actual orbit restriction `q ↦ f(w⁻¹*q)`. Naturality follows from
restriction and quotient descent; no natural choice of extension witnesses
is needed.

Consequently no extension, surjectivity, homeomorphism, local section, or
natural isomorphism remains as an extra hypothesis of the closing theorem.
The proof uses the existing `ClosedSubgroupAssembly`, `CosetOrbitHomeomorph`,
and `OrbitSectionExtensionProof` interfaces rather than changing their
carriers or the target proposition.

## Provenance and boundary

This is an internal assembly of the published restriction, topology,
section-extension, and natural quotient results. The source motivating the
statement is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), Theorem 5.2 and sections 5.3–5.15,
particularly the support restriction discussion in 5.11 and case III of
5.15. Sections 5.3–5.15, printed pages 461–465 / PDF pages 22–26, were
read in the retained original. The implemented proof follows direct
compact covariant section extension and quotient descent; it does not
implement the source's entire sheaf formalism.

The finite orbit ordering is an input of this target. This proof does not
prove `ClosedSubgroupOrbitOrdering`, nor does it establish the separate
normalized Jacquet and parabolic comparison assertions.

Literature ID: `bernstein-zelevinsky-1977-induced-i`. Retained original
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Author: Worker 112.
