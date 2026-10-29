# Local detection of a central scalar subquotient

The theorem `Langlands.admissibleCentralSubquotient` proves the complete
unapplied proposition
`Langlands.AdmissibleCentralSubquotientStatement.{uG,uA,uV,uW}` from
`Langlands.Representation.Exponents.AdmissibleCentralSubquotientStatement`.
The group `G`, commutative parameter group `A`, ambient vector space `V`
and scalar quotient space `W` retain four independent universes. The proof
introduces exactly the published statement's hypotheses.

Let `ρ : Representation ℂ G V` be admissible, let compact open subgroups
be cofinal among open subgroups of `G`, and let
`c : A →* Subgroup.center G` be continuous for the center's subspace
topology. For an actual invariant subspace `U`, the hypothesis supplies
a surjective linear map `q : U.toSubmodule →ₗ[ℂ] W` onto a nonzero
vector space, with
`q (U.toRepresentation (c a : G) u) = (χ a : ℂ) • q u`.
The theorem proves both that `χ.ker` is open in the original topology
of `A` and that the ordinary character space with power `1` in the full
transpose dual is nonzero. The dual uses the same character `χ`, without
inversion or conjugation.

## Open kernel in the original topology

The private helper `scalar_open_kernel` uses only smoothness, continuity
of `c`, and the actual nonzero scalar quotient. Choose `u ∈ U` with
`q u ≠ 0`. Smoothness supplies an open subgroup `H` fixing its image
in `V`. The homomorphism
`f = (Subgroup.center G).subtype.comp c : A →* G` is continuous because
subtype inclusion is continuous. Thus `H.toSubgroup.comap f` is an open
subgroup of the supplied topological group `A`.

For an element of this preimage, the scalar equation says
`χ(a) • q(u) = q(u)`. Scalar cancellation on the nonzero vector gives
`χ(a) = 1`. Consequently the preimage lies in `χ.ker`, and
`Subgroup.isOpen_mono` proves that this kernel is open in the original
topology. This helper makes no change to that topology and uses no
finite-dimensional argument.

## Finite-dimensional detection

The private helper `finite_scalar_detector` treats a finite-dimensional
representation of an abstract commutative group. It supplies a temporary
discrete topology on that group, so the transpose action is locally
constant. Its operator span is finite dimensional because the carrier
and its dual are finite dimensional. Applying the published
`finiteActionCommutativeSpectrum` to the full transpose dual gives
generalized character-space spanning, indexed by characters with open
kernel in this temporary topology and nonzero ordinary character space.
The published `scalarSubquotientDualSpectrum` detects the scalar
quotient's character in this indexing predicate. The helper takes only
the nonzero ordinary character-space conclusion. The temporary topology
is confined to this algebraic helper; it supplies no evidence for the
original-topology conclusion.

In the main proof, choose a nonzero quotient vector and a preimage `u`
in `U`. Smoothness and cofinality provide a compact open subgroup `K`
fixing `u`. Put `S = fixedVectors ρ K.toSubgroup`. Centrality shows
that every `ρ(c a)` preserves `S`, so `S` is an actual
subrepresentation of the restricted `A`-action, even though it need
not be a subrepresentation of `G`. Admissibility makes `S` finite
dimensional.

The subrepresentation `U₀` of `S` is the inverse image of `U` under
inclusion into `V`. Restrict `q` along this inclusion to obtain `q₀`.
The chosen `u` belongs to `U₀` and has nonzero image. Hence the actual
range `q₀.range` is nontrivial. Corestricting `q₀` to this range gives
a surjective scalar-equivariant map. Applying `finite_scalar_detector`
to this map yields a nonzero functional `φ` on `S` satisfying
`φ(ρ(c a) s) = χ(a) φ(s)`.

## Extension by compact averaging

The private helper `central_average_commute` packages each central
operator `ρ(c a)` as a genuine `G`-intertwiner of `ρ` with itself.
The intertwining equation follows by applying `ρ` to centrality.
The published naturality identity `Compact.averageMap_commute`
then shows that compact averaging over `K` commutes with this operator.

Corestrict the averaging map to obtain a linear map `P : V →ₗ[ℂ] S`,
using `Compact.averageMap_mem_fixedVectors`.
The identity `Compact.averageMap_id` gives `P(s) = s` for `s ∈ S`.
The helper above also gives
`P(ρ(c a) v) = S.toRepresentation a (P v)`.
Set `ψ = φ.comp P`. The identity on `S` ensures `ψ ≠ 0`, and the
commutation equation transfers the character equation from `φ` to `ψ`.
The published characterization `mem_commutativeCharacterSpace_one`
puts `ψ` in the required ordinary character space. Its nonvanishing
shows that this space is not `⊥`.

## Provenance and scope

This is internal derived algebra using the published smoothness,
admissibility, finite-spectrum, scalar-subquotient and compact-averaging
interfaces. It is not presented as a numbered theorem from external
literature. Worker 84 suggested the finite-fixed-space and
central-equivariant averaging route; Worker 728 supplied an informal
consistency check and local argument. Worker 429 implemented the
complete central-local probe reused here. Worker 189 adapted its module
and theorem names, checked it against the current Library statement,
and prepared this proof explanation and submission.

The proof uses one finite fixed space and supplies no decomposition or
finite-spectrum assertion for the full dual of the original
representation. It adds no irreducibility, finite-length, continuity
of `χ`, or structure on `W` hypothesis. Actual Jacquet applications and
analytic exponent or cone estimates remain separate obligations. The
published statement pair and its imported pairs are unchanged.
