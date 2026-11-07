# Base representation comparison for actual compact intertwining operators

This is a derived construction for the change of base representation in
Waldspurger IV.1. It constructs the comparison on ordinary induced vectors,
proves that restriction gives one fixed compact comparison, and applies that
comparison to the original standard integral wherever its domain is full.
The inducing representations may have independent carrier universes.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d’après Harish-Chandra)*, IV.1, printed pp.276–278 / PDF pp.42–44,
registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Page 276 identifies all unramified twists on the same compact section space;
page 277 states the representative naturality square and compact conjugation;
pages 277–278 define the original integral by absolute convergence against
every smooth dual vector and representability on the original vector space.
The character-translation comparison below is derived from these conventions
and the existing Library constructions. It is not a separate theorem quoted
from the article. The convergence cone and rationality theorem IV.1.1 remain
separate obligations.

The imports reuse `CompactIntertwiningFamilies`, `ProductCompactBaseChange`
and `StandardIntertwiningFullDomainTransport`. In particular,
`productBaseTwistEquiv` is an equivalence of the original inducing vector
representations despite its product-oriented name. No replacement
representation category, integral or normalization is introduced.

## Objects and hypotheses

The ambient group `G` has the existing nonarchimedean topological-group
structure and is locally compact. `h` and `h'` are actual closed-subgroup
semidirect decompositions of `P = MU` and `P' = MU'` with common subgroup `M`.
The source and target unipotent subgroups are closed. The supplied proofs
`hδ` and `hδ'` are the unimodular-modulus premises of the existing positive
Levi/full normalization comparison. `K` is an actual compact open subgroup,
and the two factorizations `G = PK` and `G = P'K` are explicit. The family
`ν : I → (M →* ℝ≥0ˣ)` is arbitrary, its members are continuous, and both
semidirect projections are continuous. These are generic hypotheses: the
module does not claim their realization for every reductive rational-point
group or classify them as permissible external Chapter V inputs.

`A` and `B` are canonical complex `SmoothRep` objects of `M`, in independent
universes. Fix an actual character `τ : unramifiedCharacters ν` and an
actual equivariant equivalence

`a : (A.twist τ).representation.Equiv B.representation`.

At a variable character `χ`, `productBaseTwistEquiv ν τ χ a` identifies
`A.twist (χ * τ)` with `B.twist χ`; its vector map is the original `a`.
The order in Lean is `χ * τ`. The actual character group is commutative,
so this is also the parameter `τ * χ` used by left-translation pullback.
No admissibility, irreducibility, unitary restriction or finite dimension
is required here. The group, character-index and two inducing-carrier
universes are independent. In particular, no characteristic-zero, split
or quasisplit restriction enters through this generic group construction.

## Fixed compact comparison

`compactInductionBaseChangeEquiv` is an equivalence of the actual compact
induced representations of `K`. It first restores the fixed twist using
`unramified_compactPictureInducing_eq`, in the reverse direction, and then
applies `compactInductionPictureEquiv h K a`. The evaluation theorem states

`(S_P f)(k) = a (f(k))`.

Thus `S_P` depends on `τ` and `a` but is independent of the variable `χ`.
The proof is definitional evaluation on the original compact function
carriers. Ordinary vectors retain the scalar ambiguity in the choice of
`a`; no independence of that choice is asserted.

`unramifiedLeviInductionCompactEquiv_baseChange` proves the restriction square
between the actual Levi-normalized induced representations:

`R_B,χ ∘ inducedMap(a_χ) = S_P ∘ R_A,χτ`.

Both sides are sections obtained by restricting to `K` and applying `a`
pointwise, so the implemented proof uses function and subtype extensionality.
The inverse-square theorem applies the injective restriction equivalence
and cancels its inverse. It compares actual normalized induction, rather
than merely unrelated fixed vector spaces.

## Ambient and compact operator squares

For arbitrary actual ambient intertwiners `J_A` at `χ * τ` and `J_B` at `χ`,
`compactIntertwiningOperator_baseChange` takes their ambient square as its
explicit hypothesis and proves

`J_B^K ∘ S_P = S_P' ∘ J_A^K`.

The proof unfolds compact conjugation, uses the inverse restriction square,
uses the supplied ambient square, and applies the target restriction square.
`compactIntertwiningOperator_baseChange_iff` proves the converse as well:
test the compact equality on the restriction of an arbitrary source vector,
cancel the restriction inverses and use injectivity of target restriction.
These helper results transfer squares; they do not assume a square and then
claim to establish its representation-theoretic source.

## Original full domain and standard integral

`standardIntertwining_domain_eq_top_baseChange_iff` states that the original
standard-intertwining domain is full for `A.twist (χ * τ)` exactly when it is
full for `B.twist χ`, for the same quotient measure `qν` on
`(U ∩ U') \ U'`. This uses `domain_eq_top_iff_equiv` on the actual
`productBaseTwistEquiv`. The domain includes scalar absolute integrability
and original-carrier representability; no convergence premise is produced
without an initial full-domain proof on one side.

For `standardCompactOperator_baseChange`, the additional integral hypotheses
are explicit: the ambient group is Hausdorff; `U'`, `U ∩ U'` and the quotient
have the stated Borel structures; `μU'` and `μI` are regular, right-invariant
Haar measures; `hqν` is their actual quotient-integration compatibility
with `qν`; `M` is closed; and `hsq` is the squared-modulus compatibility of
the two decompositions. Separate proofs `hfullA` and `hfullB` of full domain
are displayed. The preceding equivalence allows either one to supply the
other. The same measures and normalization data are used for both operators.

The theorem proves the displayed compact square for the actual
`standardCompactOperator` values. Its implemented proof applies the general
compact comparison and supplies its ambient-square hypothesis from
`fullSourceIntertwiner_natural` applied to the actual twisted equivalence.
The original integral relation is therefore preserved through the existing
full-source standard-intertwiner construction; no arbitrary ambient square
is left as an additional premise of this specialization.

## Retained obligations

This construction neither proves a nonempty convergence region nor the
rationality of the standard integral. It does not construct continuation
data, compare independent continuations after translation, prove generic
induced irreducibility, or descend to stabilizers or twist orbits. Opposite
composition, parabolic independence, nonvanishing, positivity and global
`j`/`mu` normalization remain separate. The ordinary compact comparison alone
also does not remove the choice of `a` or establish orbit-level descent.
