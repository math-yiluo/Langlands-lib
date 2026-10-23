# Sylow detection for positive-degree group cohomology: proof

Authors: Worker 58 (original draft of the three pointwise theorems) and
Worker 259 (closed wrappers, adaptation and this description).

This module proves the two closed propositions of
`Langlands.Cohomology.SylowDetectionStatement`:

- `Langlands.Cohomology.sylowDetection : Langlands.Cohomology.SylowDetection.{u}`;
- `Langlands.Cohomology.sylowSubsingleton : Langlands.Cohomology.SylowSubsingleton.{u}`.

Both use Mathlib's actual ordinary group cohomology `groupCohomology` and the
actual restriction maps
`groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype A)) n`. The ring `k`
and the finite group `G` live in one arbitrary universe `u`. There is no
finiteness hypothesis on the coefficients or on any cohomology group. The
proof transports classes to the Library's Tate cohomology and back. Only the
standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.

## Pointwise theorems

The section `Pointwise` fixes `k G : Type u` with `[CommRing k] [Group G]
[Finite G]`. Its theorems assume `[NeZero n]` instead of `0 < n`.

### Index annihilation

`index_nsmul_eq_zero_of_restriction_eq_zero A H n x hx` states the following.
Let `H : Subgroup G` and `x : groupCohomology A n`. If the restriction of `x`
to `H` is zero, then `H.index • x = 0`.

The Library's Tate maps require `Fintype` instances, so the proof first
chooses `Fintype G`, `Fintype H` and `Fintype (G ⧸ H)` from finiteness. These
local instances only build the maps. The statement does not mention them.

Let `e` be the linear equivalence underlying the positive-degree comparison
`(TateCohomology.isoGroupCohomology n).app A`, from Tate cohomology in degree
`n` to ordinary cohomology. Let `eH` be the same equivalence for the restricted
representation `Rep.res H.subtype A`. The published identity
`Langlands.Tate.restriction_groupCohomology` states that Tate restriction
`Langlands.Tate.restriction H A n` equals `e`, then ordinary restriction, then
the inverse of `eH`. Applied to `e.symm x`, the hypothesis `hx` therefore shows
that the Tate restriction of `e.symm x` is zero. The published identity
`Langlands.Tate.corestriction_restriction` states that Tate corestriction
after Tate restriction is multiplication by `H.index`. Hence
`H.index • e.symm x = 0`. Applying `e`, which commutes with `nsmul`, gives
`H.index • x = 0`.

The module sets `backward.isDefEq.respectTransparency false`, as the Library's
Tate comparison modules do. Without it, rewriting fails to identify
`groupCohomology A n` with `(groupCohomology.functor k G n).obj A`. These two
types are definitionally equal.

### Detection

`eq_zero_of_sylow_restriction_eq_zero A n x hx` is pointwise detection. Its
hypothesis `hx` says that for every natural number `p`, if `p.Prime` then
every `P : Sylow p G` restricts `x` to zero. The conclusion is `x = 0`.

The proof shows that `addOrderOf x = 1`, using
`AddMonoid.addOrderOf_eq_one_iff`. By `Nat.eq_one_iff_not_exists_prime_dvd`,
it suffices to rule out a prime `p` dividing `addOrderOf x`. Given such a `p`,
the proof chooses some `P : Sylow p G`; Sylow subgroups always exist. Index
annihilation gives `P.1.index • x = 0`. Then
`addOrderOf_dvd_iff_nsmul_eq_zero` shows that `addOrderOf x` divides
`P.1.index`, so `p` divides `P.1.index`. This contradicts `Sylow.not_dvd_index`.

The argument also covers additive order zero. Every prime divides zero, so this
case is ruled out by the same contradiction. The proof therefore assumes
nothing about finiteness of `x`'s order or of the cohomology group.

### Subsingleton corollary

`subsingleton_of_sylow A n h` is the pointwise subsingleton form. It assumes
that `groupCohomology (Rep.res P.1.subtype A) n` is a subsingleton for every
prime `p` and every `P : Sylow p G`. The proof shows that every class `x` is
zero. Each restriction of `x` lies in a subsingleton, so it equals zero, and
detection gives `x = 0`. Any two classes are therefore both zero. This helper
is retained for the dependent prime-section `H^1` proof.

## Closed theorems

`sylowDetection` introduces the quantified `k`, `G`, their instances, `A`, `n`,
the hypothesis `hn : 0 < n`, the class `x` and the Sylow hypothesis. It turns
`hn` into `NeZero n` and applies `eq_zero_of_sylow_restriction_eq_zero`.
`sylowSubsingleton` introduces its quantifiers the same way and applies
`subsingleton_of_sylow`. Each closed theorem is unapplied, and its type is
exactly the published constant.

## Provenance

This is a derived proof of a derived statement, not a transcription of a source
proof. Its source is the Sylow step in Emil Artin and John Tate, *Class Field
Theory*, AMS Chelsea, 2009, Chapter XIV, section 2, Lemma 1, Case 2, printed
p. 148 (PDF p. 157). The registered source is
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. That
passage uses, without proof there, the fact that restriction to a `p`-Sylow
subgroup is injective on the `p`-primary part of cohomology, and then bounds
cohomology orders. The usual reason for that fact is that corestriction after
restriction is multiplication by the index. This module applies that index
identity directly to the additive order of one class, not to cohomology
orders. The module proves detection only. It proves no finiteness or order
bound and no arithmetic vanishing statement.
