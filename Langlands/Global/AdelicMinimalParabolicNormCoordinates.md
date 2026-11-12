# Positive coordinates on the norm-one part of a minimal parabolic

Author: Worker 83.

This module states a structural prerequisite for the chamber form of adelic
Siegel reduction. It does not prove the coordinate statement or the chamber
reduction theorem. The three theorems at the end are conditional consequences
of the coordinate property.

## The actual spaces and statement

Fix a number field `F`, a connected reductive affine group scheme `G` of
finite type, and an actual `IsSiegelAlgebraicSetup F G T i ν T₀ j`.
Write `P`, `N` and `M` for the canonical schemes
`Standard.parabolicScheme i ν ∅`, `Standard.unipotentScheme i ν ∅` and
`Standard.leviScheme i ν ∅`.

`standardParabolicNormOneImage` is the subgroup of `normOneSubgroup F G`
whose elements lie in the actual image `P(𝔸_F)` in `G(𝔸_F)`.
The norm-one condition here uses the characters of **G**. This space
usually differs from the image of `normOneSubgroup F P`, which uses every
character of **P**.

`HasMinimalParabolicNormCoordinates` asks for a homeomorphism

`N(𝔸_F) × (M(𝔸_F)¹ × A_{T₀}) ≃ₜ P(𝔸_F) ∩ G(𝔸_F)¹`

whose ambient value is exactly `ι_N(n) * ι_M(m) * positiveMap(a)`.
All maps, intrinsic positive points and norm-one subgroups are the existing
Library constructions. The domain uses the product topology; this is a
homeomorphism of spaces, with no assertion that the ordinary product group
law is respected. In particular the unipotent action is retained.

`MinimalParabolicNormCoordinatesStatement` quantifies over all number fields
in universe `u`, all `G` with the same hypotheses as
`AdelicSiegelChamberReductionStatement`, and every actual algebraic setup.
No compactness theorem, fundamental set, decomposition or splitting of `G`
is a premise. There is no compact subgroup `K` in this structural statement.
It includes nonsplit and anisotropic groups and the case of no simple
relative roots.

## Provenance and outstanding mathematical obligation

This is a **derived structural interface**, not a verbatim theorem from
Springer. Springer, *Reduction theory over global fields* (1994), §2.1,
printed p.211, uses the Levi decomposition of `P`, its character-norm kernel,
and the split torus in order to write the parabolic factors used in (F).
The passage to the Library's `M(𝔸_F)¹` and intrinsic positive points of the
derived split torus is explained, but not proved, in the paired Markdown of
`AdelicSiegelChamberReduction`, in the discussion of rewritings (1) and (2).

The coordinate statement makes that missing comparison an explicit proof
target, with topological control for compact sets. Its expected proof must
combine the actual Levi projection with character restriction and the
positive/norm-one decomposition of the minimal Levi. It must also show that
the ambient norm-one condition removes precisely the central split component
of `G`. The setup supplies the derived torus and the central split component
up to a surjective product morphism; identifying their positive real
coordinates is part of the obligation. The statement does not treat these
unproved comparisons as assumptions.

## Implemented conditional consequences

`exists_factors` applies the inverse of the supplied homeomorphism to the
given norm-one parabolic point and uses its specified forward formula.

`exists_iwasawa_factors` first writes `g = p k` by the supplied Iwasawa
predicate. A compact subgroup lies in `G(𝔸_F)¹`, by the published
`compactSubgroup_le_normOneSubgroup`. Thus `p = g k⁻¹` is norm-one.
`exists_factors` supplies `p = n m a`, giving the ordered equality
`n m a k = g`. No uniform bound on roots is deduced from Iwasawa
decomposition: that bound and the rational translation remain the
fundamental-set problem.

`compact_coordinate_covers` takes the three projections of the inverse
homeomorphism. Their images of a supplied compact set are compact, by
continuity. The forward formula recovers each point using those coordinate
sets. This provides compact coordinate control inside the parabolic; moving
an arbitrary ambient compact set into `P(𝔸_F) K` still requires a compact
lifting argument.

## Source

T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
Sci. (Math. Sci.) 104 (1994), 207–216. Registered source:
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
Used: §2.1, printed pp.211–212 (PDF pages 5–6, counted from one),
the Levi decomposition, parabolic character-norm kernel, and (F).
The complete paper was read. No Springer errata entry is registered.
