# Certified cyclic base change commutes with unramified twists

`Langlands.Henniart.certifiedCyclicBaseChangeTwistEquivariance` proves
`Langlands.Henniart.CertifiedCyclicBaseChangeTwistEquivarianceStatement.{uK, uV}`
of `Langlands.Correspondence.HenniartCandidateBaseChangeFiniteImageReductionStatement`
at arbitrary universes `uK`, `uV`. Given the uniqueness of σ-lifts
(`Langlands.BaseChange.SigmaLiftUniquenessStatement`, Henniart–Lemaire 2011,
II.2.9, Remarque (2)), a map `Ch` on supercuspidal classes for a cyclic step
\(M/L\) of prime degree that is certified by σ-lifts for some \(\sigma\ne 1\)
(`Langlands.BaseChange.IsSigmaLiftOnSupercuspidals`) satisfies
`Numerical.IsUnramifiedTwistEquivariant`. The argument is the one of
Henniart–Lemaire, II.2.9, Remarques (2) and (4): twisting a σ-lift gives a
σ-lift of the twist, and uniqueness identifies it with the certified lift of the
twisted class. The uniqueness of σ-lifts enters only as the premise of the
statement; no other hypothesis is added.

## Setting

Write \(L=\) `S.base`, \(M=\) `S.top`, \(f=\) `S.residueDegree`, with the
algebra structure `S.algebra` of the embedding and the canonical topologies,
valuations and local-field structures of both fields. The proof supplies the
instances that the σ-lift statements need: the scalar tower over
\(\mathbb Q_p\) and finite dimensionality
(`Weil.Local.extensionAlgebra_isScalarTower`,
`Weil.Local.extensionAlgebra_finiteDimensional`), the Galois property
`S.isGalois`, the module topology of \(M\) over \(L\)
(`Langlands.BaseChange.isModuleTopology_padic_extension`) and characteristic
zero of \(L\) (from \(\mathbb Q_p\)).

## Cyclicity of \(M/L\)

The Galois group has prime order (`S.card_prime`), so by Mathlib's
`zpowers_eq_top_of_prime_card` every automorphism is a power of
\(\sigma\ne 1\). Hence `orderOf σ` is the order of the group, which equals
\([M:L]\) by `IsGalois.card_aut_eq_finrank`. An element fixed by \(\sigma\) is
fixed by every power of \(\sigma\), so by the whole Galois group, and lies in
\(L\) by `IsGalois.mem_range_algebraMap_iff_fixed`. A field is reduced, so
`IsCyclicAlgebra σ (orderOf σ)` holds.

## The two certified lifts

Fix `k`, `z` and a class `π`, and choose a supercuspidal representative `A` of
`π`. Let `A'` be `GeneralLinear.SupercuspidalRep.twist` of `A` by
`determinantUnramifiedCharacter (k + 1) z`, the character
\(g\mapsto z^{\operatorname{ord}_L(\det g)}\). Its class is, by definition,
`Numerical.supercuspidalUnramifiedTwist S.base k z π`. The certification
applied to `A` gives a σ-lift \(\tau\) of `A` (intertwiner \(I\), constant
\(c\)) whose supercuspidal support is `(Ch k π).map (supercuspidalSupportDatum M)`.
Applied to `A'` it gives a σ-lift \(\tau'\) of `A'` (intertwiner \(I'\),
constant \(c'\)) whose support is the image of `Ch k` of the twisted class.
A supercuspidal support (`IsSupercuspidalSupport`, through
`IsCuspidalConstituent`) contains irreducibility of the representation, so
\(\tau\) and \(\tau'\) are irreducible.

## Twisting the lift and uniqueness

Let \(\omega\) be `unramifiedCharacterContinuous z` of \(L^\times\).
`Langlands.BaseChange.sigmaLiftFieldTwist` (Henniart–Lemaire II.2.9,
Remarque (4)) shows that the twist of \(\tau\) by
\(\chi_E=\omega\circ N_{M/L}\circ\det\) is admissible and is a σ-lift, with an
intertwiner and the same constant \(c\), of the twist of `A` by
\(\omega\circ\det\). The latter is the representation of `A'`, by unfolding
the definitions. The twist of \(\tau\) is irreducible
(`Langlands.isIrreducible_twist_iff`). The uniqueness premise, applied to
`A'` (irreducible and admissible as a supercuspidal object), \(\tau'\) and the
twist of \(\tau\), gives an equivalence between \(\tau'\) and
`Langlands.twist χE τ.representation`.

## The pulled-back character

The residue cardinality relation `Weil.Local.extensionResidueCardinality`
gives `IsResidueDegree L M f`. Then
`Langlands.BaseChange.ord_localNorm_eq_residueDegree_mul` gives
\(\operatorname{ord}_L(N_{M/L}x)=f\cdot\operatorname{ord}_M(x)\) for
\(x\in M^\times\). Since the local norm is `Units.map (Algebra.norm L)`, this
shows \(\omega\circ N_{M/L}=\) `unramifiedCharacter (z ^ f)` of \(M^\times\)
as monoid homomorphisms:
\(z^{\operatorname{ord}_L(N x)}=z^{f\operatorname{ord}_M x}=(z^f)^{\operatorname{ord}_M x}\).
Let \(\chi_M\) be this character as an
`Induction.SmoothCharacter` (its kernel is open by
`isOpen_ker_unramifiedCharacter`).

## Comparing supports

`PadicField.TopologicalData.IsSupercuspidalSupport.characterTwist` makes the
image of the support of \(\tau\) under `CuspidalDatum.characterTwist χM` a
support of the smooth twist of \(\tau\) by \(\chi_M\circ\det\). By the character
identity above, the action of this twist equals `Langlands.twist χE τ.representation`;
composing the resulting equality of actions (`Langlands.equivOfRepresentationEq`)
with the inverse of the uniqueness equivalence gives an isomorphism onto
\(\tau'\) (`SmoothRep.mkIso`). `IsSupercuspidalSupport.of_iso` transports the
support to \(\tau'\), and `Langlands.glSupercuspidalSupportUniqueness`
(Zelevinsky 1980, Proposition 1.10) applied to the irreducible \(\tau'\) gives

```text
(Ch k (twisted class)).map datum = ((Ch k π).map datum).map (characterTwist χM)
```

with `datum = supercuspidalSupportDatum M`.

## Reading back the classes

`supercuspidalSupportDatum` records the rank \(j+1\) and the class of a
rank-tagged entry \(\langle j, c\rangle\). It is injective (private lemma
`supercuspidalSupportDatum_injective`: equal ranks give \(j=j'\), and equal
classes as a heterogeneous equality give the entries' equality,
`Sigma.ext`). So `Multiset.map` by it is injective
(`Multiset.map_injective`). After `Multiset.map_map`, it remains that
`characterTwist χM` of the datum of \(\langle j,c\rangle\) is the datum of
\(\langle j,\) `supercuspidalUnramifiedTwist S.top j (z ^ f) c`\(\rangle\).
Both sides have rank \(j+1\) and class `GeneralLinear.SupercuspidalClass.twist`
of \(c\) by \((\)`unramifiedCharacter (z ^ f)`\()\circ\det\), so the equality holds
by definition.
