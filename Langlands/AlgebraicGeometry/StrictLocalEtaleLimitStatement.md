# Statement: strictly local limits of affine etale neighbourhoods exist

Worker 875.

`Langlands.AlgebraicGeometry.StrictLocalEtaleLimitExistenceStatement.{u}` is a
`Prop`-valued definition. It asserts that for every affine scheme `S` in universe
`u` and every point `s`, there is an actual `StrictLocalEtaleLimit S s`.
This module does not prove the statement or add axioms.

The data package is defined in
[`StrictLocalEtaleLimit`](StrictLocalEtaleLimit.md). Its ring is Henselian local
with separably closed residue field. Its index category is small in universe
`u` and cofiltered. Every diagram object is an affine scheme with an etale
structural map to `S`. The spectrum of the local ring has an actual limiting
cone, compatible with a specified map to `S` taking its closed point to `s`.
The assertion retains no strict-henselization universal property, residue-field
identification, flatness of the limit map, or noetherianity.

The source is the Stacks Project, Algebra, Lemmas
[10.155.2, tag 04GP](https://stacks.math.columbia.edu/tag/04GP) and
[10.155.11, tag 04GW](https://stacks.math.columbia.edu/tag/04GW), registered as
`stacks-strict-henselization-etale-limit`, directory SHA-256
`d422dc52c8c2ddf0c47d11da87fc8f15b98a07709ef875e4e3e59514172ede61`.
The retained official HTML snapshots were accessed on 17 November 2026.

This statement is a derived existential consequence. For `S = Spec R`, take
the strict henselization of the localization of `R` at the prime corresponding
to `s`. Lemma 04GP supplies the strictly Henselian local ring. Lemma 04GW
presents it as a filtered colimit of etale `R`-algebras with pointed residue
embeddings. Apply spectra to obtain a cofiltered affine diagram and its limit;
its closed point maps to `s`. A small skeleton of the finitely presented
etale algebras and their pointed data provides an index category in universe
`u`. Transport along an affine scheme's spectrum identification handles the
stated affine base. These constructions are proof obligations, not implemented
results of this module.

The eight comments on the source section
[10.155, tag 0BSK](https://stacks.math.columbia.edu/tag/0BSK) were read. They
concern corrected wording and a prime-avoidance citation; the last concern
about comparable primes over the maximal ideal is retracted by its author.
No unresolved correction to the cited existence or presentation claims was found.

This generic existence statement supports spreading finitely presented data
from strict-local bases to etale neighbourhoods. It does not assert the
multiplicative-type fibral criterion, fpqc descent, or the extension theorem.
