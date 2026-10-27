# Conjugacy and corestriction laws from inflation and restriction laws

Author: Worker 272.

Lean module: `Langlands.ClassFieldTheory.Local.InvariantTransferConsequencesStatement`.

This module states three conditional propositions about an arbitrary raw
`InvariantFamily.{u,u} p`. Each one derives one invariant clause of the local
realization target `LocalAbsoluteCorestrictionCompatibleClassFormationStatement`
from two other clauses. The module defines propositions only. It constructs no
invariant family and proves nothing.

## The three propositions

All three are in the namespace `Langlands.ClassFieldTheory.Local`. They
quantify over every prime `p` (with `[Fact p.Prime]`) and every family
`I : InvariantFamily.{u,u} p` in the arbitrary universe `u`. Every clause
named below is an existing Library predicate on such a family. The maps inside
those predicates are the actual Library constructions; none is replaced or
assumed.

- `InvariantRelativeConjugacyStatement`: if `I.InflationCompatibility` and
  `I.RelativeRestriction` hold, then `I.RelativeConjugacy` holds.
  - `InflationCompatibility` (`ClassFormation`): for every tower
    `F ⊆ L ⊆ M` with `L` and `M` finite Galois over `F`, actual inflation
    `relativeInflation F L M 2` preserves the relative invariant.
  - `RelativeRestriction` (`ClassFormation`): for p-adic fields `F ⊆ E` (with
    `E` finite over `F`, compatibly over `Padic p`) and a finite extension `M`
    of `E` that is Galois over both, actual relative restriction
    `relativeRestriction F E M 2` multiplies the relative invariant by
    `[E:F]`.
  - `RelativeConjugacy` (`ClassFormation`): for p-adic fields `F`, `E`, a
    `Padic p`-algebra equivalence `eF : F ≃ E`, finite Galois extensions `L`
    of `F` and `M` of `E`, and a ring equivalence `eL : L ≃ M` forming a
    commuting square with `eF` (`CompatibleFieldEquivalences`), the
    invariant of `M/E` at the transported class
    `(relativeConjugacy eF eL h 2).hom x` equals the invariant of `L/F` at
    `x`.
- `InvariantRelativeCorestrictionStatement`: if `I.RelativeImages` and
  `I.RelativeRestriction` hold, then `I.RelativeCorestriction` holds.
  - `RelativeImages` (`Invariants`): every relative invariant
    `I.relative F L` is injective, with range `denominatorSubgroup [L:F]`, the
    subgroup of `ℚ/ℤ` killed by `[L:F]`.
  - `RelativeCorestriction` (`Corestriction`): in the tower of the restriction
    clause, actual relative corestriction
    `relativeCorestriction F E M 2 : H²(M/E) → H²(M/F)` preserves the relative
    invariant: `I.relative F M (Cor c) = I.relative E M c`.
- `InvariantAbsoluteCorestrictionStatement`: if `I.AbsoluteIsomorphisms` and
  `I.AbsoluteRestriction` hold, then `I.AbsoluteCorestriction` holds.
  - `AbsoluteIsomorphisms` (`Invariants`): every absolute invariant
    `I.absolute F` is bijective.
  - `AbsoluteRestriction` (`Invariants`): for p-adic fields `F ⊆ E` as above
    and every supplied algebra structure of `AlgebraicClosure E` over
    `AlgebraicClosure F` compatible with `F`, actual continuous restriction
    `absoluteRestriction F E 2` multiplies the absolute invariant by `[E:F]`.
  - `AbsoluteCorestriction` (`AbsoluteCorestrictionInvariant`): in the same
    setting, with the same supplied closure embedding, actual absolute
    corestriction `absoluteCorestriction F E 2 : H²(E) → H²(F)` preserves the
    absolute invariant.

None of the hypotheses mentions `H¹`, fundamental classes or Tate cohomology.
In particular, the first two propositions do not assume the `H¹` vanishing
clause of `RelativeClassFormation`.

## Intended use

These propositions split generic deductions from the construction of one local
invariant family (task `f8ddc947-2d65-4e22-a2a4-e2f4844c8e78`). Once a family is
known to satisfy the image, inflation and restriction clauses, their proofs
supply its `RelativeConjugacy`, `RelativeCorestriction` and
`AbsoluteCorestriction` clauses.

The intended proofs are the classical ones. Restriction from `H²(M/F)` to
`H²(M/E)` (or between absolute groups) is surjective, because `ℚ/ℤ` is
divisible and the invariants are injective with the stated images. The
corestriction formulas then follow from `Cor ∘ Res = [E:F]` on `H²`, which is
already proved in the Library: `relativeH2CorestrictionRestriction` and
`continuousRestriction_corestriction_index`. For conjugacy, the field square
factors through the degree-one tower `F ⊆ E ⊆ M`, with `M` viewed over `F`
through `eF`. The restriction law in degree one then reduces conjugacy to
same-base conjugacy, which inflation compatibility controls through the
Library's `SameBaseConjugacy` module.

## Provenance

Provenance: source. The three implications are Proposition 1 of Jean-Pierre
Serre, *Local Fields* (1979), Chapter XI, §2 (printed pages 167–168, PDF
pages 173–174). There, from axiom II (injective invariants with image the
subgroup of order `[F:E]`, and `inv_{E'} ∘ Res = [E':E] · inv_E`), Serre
proves three facts: (i) restriction is surjective on `H²`;
(ii) `inv_E ∘ Cor_{E'/E} = inv_{E'}`; (iii) `inv_{sE} ∘ s* = inv_E` for
conjugation by `s ∈ G`. Serre states (ii) on `H²(/E)`, the direct limit of
the finite relative groups. The relative and absolute propositions here are its
two specializations to the actual finite relative groups and to continuous
absolute cohomology of the algebraic closure.

The conjugacy proposition is the finite relative form of (iii). Serre's
conjugation `s*` is internal to one Galois group. Here it is replaced by
transport along an arbitrary compatible pair of field equivalences between two
p-adic fields, because the target quantifies over abstract extensions. Serre's
proof of (iii) uses (i), the identity `s* = id` on the base field (§1, iv, via
Chapter VII, §5, Prop. 3) and the commutation of `Res` with `s*`. The intended
proof here uses inflation compatibility in place of passage to the limit. The
registered source is `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
