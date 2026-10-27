# Graded quotients of the actual localized image filtration

`Langlands.Jacquet.Localization.ImageFiltrationGradedStatement` is a
proposition definition. This file states the graded comparison and supplies no
proof of it.

For an arbitrary topological group `G`, the localizing subgroup `U` must satisfy
`IsLimitOfCompactSubgroups U`: every compact subset of `U` is contained in an
actual compact subgroup of `U`. The character `θ : U →* ℂˣ` is locally constant.
The subgroup `M` normalizes `U` and preserves `θ` under the existing conjugation
action. These are the precise hypotheses of the existing character-localization
exactness result. No local compactness or total disconnectedness of `G` is
assumed.

The input `A` is an actual smooth complex representation of `G` and `s` is any
actual finite zero-to-full invariant filtration of `A`. The conclusion supplies
a filtration `t` of the actual quotient `Coinvariants A.ρ U θ`, equipped with
its actual `M` action. Its length and order are exactly those of `s`, and its
step at `k` is exactly the image of `s.subrepresentation k` under the existing
character quotient map. Thus the output cannot replace those subspaces by
unrelated representatives. Each successive quotient of `t` is equivalent as an
`M` representation to the actual character localization of the corresponding
successive quotient of `s`.

The group and carrier universes `uG` and `uV` are independent. All finite lengths,
including zero, and zero representations are included. The input need not be a
composition series and need not have finite length. No finite dimension,
admissibility, semisimplicity, splitting, or pre-existing graded equivalence is
assumed. No naturality in an external category, normalized Jacquet comparison,
or multiplicity formula is claimed.

## Internal provenance and proposed proof route

This is an internal consequence of the existing constructions and exactness,
not a separately attributed transcription of a literature theorem.
`LocalizationFiltration` already constructs the actual image filtration and
proves its monotonicity and endpoints. Character-localization exactness makes
the localized inclusion of each original invariant step injective, identifying
that localization with the actual image step. The adjacent original steps and
their actual quotient form a short exact sequence. Localizing that sequence and
transporting its upper and lower terms to their images identifies the kernel of
the upper-step projection with the lower image step. The first isomorphism
theorem therefore gives precisely the asserted equivalence of actual graded
representations. This proposed route explains the statement; its formal proof
is a separate obligation.

The full graded comparison is distinct from `FiltrationCollapseStatement`,
which asserts a linear equivalence with one surviving localized factor when
all other factors vanish. It is also distinct from the existing normalized
induction filtration. In the relative generic comparison argument, the present
statement supplies actual filtrations needed before Jordan–Hölder additivity
can sum constituent contributions. It proves no relative generic comparison or
head result by itself.
