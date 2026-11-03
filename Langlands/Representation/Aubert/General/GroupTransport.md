# Normalized parabolic functors under ambient group equivalence

This internal construction transports the actual normalized parabolic functors
between two locally compact nonarchimedean groups. It is a prerequisite for the
assigned rational Jacquet compatibility proof. It supplies no proof of the
whole rational Jacquet proposition.

## Inputs and scope

The ambient groups `G` and `H` both belong to `Type uG`. The representation
carrier universe `uV` is independent. A continuous multiplicative equivalence
`e : H ≃ₜ* G` is specified. The actual subgroups are decomposed as
`P = M ⋉ U` and `P' = M' ⋉ U'` by
`IsSemidirectDecomposition`. Subgroup compatibility means the literal
membership equivalences

```text
x ∈ P' ↔ e x ∈ P,
x ∈ M' ↔ e x ∈ M,
x ∈ U' ↔ e x ∈ U.
```

The unipotent subgroups `U` and `U'` are closed. Jacquet transport needs the
compatibilities for `M` and `U`; induction also needs the one for `P`.
The initial subgroup construction needs only groups and topologies; the
character comparisons need locally compact topological groups. The functor
constructions assume locally compact nonarchimedean groups.

No compatibility of standard parabolic families or root data with an actual
Weyl representative is asserted or assumed implicitly.

## Subgroups, characters and projections

In namespace `Langlands.Aubert.General.GroupTransport`, `subgroupEquiv`
restricts `e` to any corresponding actual subgroups. Its inverse is the
restriction of `e.symm`; its forward and inverse evaluation laws are proved.

`closedRestrictCharacter_transport` compares the actual restricted Haar
characters. The two automorphisms of `U'` and `U`, induced by conjugation by
corresponding elements of `M'` and `M`, are conjugate through `subgroupEquiv`.
The proof installs the closed-subgroup local compactness and Borel structures
and applies `mulEquivHaarChar_trans_symm` from the published generic conjugation
module. `closedHalfCharacter_transport` and
`closedInverseHalfCharacter_transport` follow by applying the definitions of
the positive square root, complex character and inverse.

`projection_transport` compares the actual Levi projections. The projection's
characterization says that its inverse times the original parabolic element
belongs to the unipotent subgroup. The subgroup membership compatibility and
the multiplicative laws of `e` transport this characterization.

## Actual normalized functors

`jacquetIsoApp` uses
`Jacquet.Localization.transportEquiv` with the identity on the representation
carrier. Thus it sends the class of a vector to the class of the same vector.
Equality of the inverse half characters proves equivariance for the normalized
actions. `jacquetIsoApp_hom_mk` states this evaluation law.
`jacquetIso` proves the natural isomorphism

```text
r_G ⋙ pullback(e_M) ≅ pullback(e) ⋙ r_H,
```

where `e_M` is the restriction of `e` to `M' ≃ₜ* M`. Naturality holds on
vector representatives and extends to the whole actual coinvariant quotient.

`inducingRepresentation_transport` uses the positive half-character and
projection comparisons to identify the actual inducing actions.
`inductionIsoApp` then applies the published
`Induction.precomposeSmoothInducedGroupEquiv`. Its map sends a smooth induced
function `f` to `f ∘ e`; the inverse is precomposition by `e.symm`.
The reused construction preserves covariance and transports a uniform open
right stabilizer. `inductionIsoApp_hom_eval` records this evaluation.
Function extensionality proves naturality, giving `inductionIso`:

```text
i_G ⋙ pullback(e) ≅ pullback(e_M) ⋙ i_H.
```

Both natural isomorphisms are on the full smooth complex representation
categories. Normalized induction allows the output carrier universe
`max uG uV`; Jacquet restriction retains `uV`.

## Exact Grothendieck groups

The K0 identities use the published exact finite-length smooth
Grothendieck group, with saturated carriers `Type (max uG uV)`.
`inductionK0_transport` assumes finite-length and finite-length-short-exact
preservation for the two induction functors. `jacquetK0_transport` assumes
the corresponding properties for the two Jacquet functors. Pullback itself
has these preservation properties by the published group-transport results.

The two identities follow by `map_comp` and `map_eq_of_iso`, applied to the
natural isomorphisms above. They are, in composition notation,

```text
pullback(e) ∘ i_G = i_H ∘ pullback(e_M),
pullback(e_M) ∘ r_G = r_H ∘ pullback(e).
```

`inductionJacquetK0_transport` combines these identities and associativity:

```text
pullback(e) ∘ (i_G ∘ r_G) = (i_H ∘ r_H) ∘ pullback(e).
```

This final identity takes the two named `ParabolicFiniteLength` hypotheses.
No finite-length preservation theorem is proved here.

## Provenance and retained obligations

This is derived implementation infrastructure, without a claim to a separately
numbered literature result. The proof uses the published actual quotient and
smooth-function transport constructions, the semidirect projection
characterization, the Haar-character transport law and the functorial exact
Grothendieck group laws. Direct imports are
`Aubert.General.Conjugation`, `Induction.SmoothGroupTransport` and
`Jacquet.LocalizationTransport`.

For the rational Jacquet consumer, the actual restricted parabolic, Levi and
unipotent membership equivalences must still be proved for the chosen ambient
Levi equivalence and every required normalizer lift. The geometric expansion,
its common-term reduction, and the longest-survivor identification remain
separate obligations. This construction introduces no new premise into the
published rational target and does not discharge those obligations.
