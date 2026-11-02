# Ordered actual-unit cocycles and glued line bundles

For every scheme `X : Scheme.{u}` and family `U : ι → X.Opens` with
`ι : Type u`, this module translates the published ordered Čech cochains
of actual structure-sheaf units to the published transition-unit gluing
construction. Its namespace is
`Langlands.AlgebraicGeometry.Picard.UnitCechLineBundle`.

The coefficient presheaf `unitP` is exactly
`NilpotentUnitReduction.unitsPresheaf X.presheaf`: its value on an open
`W` is `Additive ((Γ(X, W))ˣ)`. It is not a group of chosen local
trivializations or an abstract substitute for the actual units. No
nilpotence hypothesis is used here.

For an ordered one-cochain `z`, `pairUnits U z i j` restricts `z ![i,j]`
from the ordered intersection to `U i ⊓ U j` and removes the additive
notation. The restriction lemma `res_pairUnits_val` identifies its
underlying ring section on every smaller open. `unitVal` is the
underlying ring value of an additively written unit; it is injective.
The lemma `pairUnits_injective` shows that these pairwise units determine
all the ordered cochain components, including repeated indices.

If `d z = 0`, `isCocycle_pairUnits` proves the actual multiplicative
transition identity on triple overlaps. Its proof applies `unitVal` to
the published additive cocycle identity and uses the restriction formula.
For a full cover, expressed by `(⨆ i, U i) = ⊤`, `lineBundle U hU z hz`
is the actual published `CocycleGluing.glued (pairUnits U z)` equipped
with its proved local freeness of rank one. No finiteness, affineness,
separation, or compactness assumption is imposed on the cover or scheme.

For an ordered zero-cochain `a`, `vertexUnits U a i` is the actual unit
on `U i`. The construction `vertexCochain U b` converts every family of
such units back to an ordered zero-cochain, and
`vertexUnits_vertexCochain` proves that its vertex units are exactly `b`.
Restriction and negation formulas are proved directly from the
presheaf homomorphisms.

The gauge convention in `CocycleLineBundleGauge` is
`b_i * g_ij = h_ij * b_j` after restriction to the overlap. The ordered
Čech differential has the convention `(d a)_ij = a_j - a_i`. Therefore
`d a = w - z` gives the gauge with vertices `(vertexUnits U a i)⁻¹`.
The lemmas `isGauge_of_d_eq_sub` and `d_eq_sub_of_isGauge` prove both
directions for this same gauge. Their proofs restrict the differential
to each pair, identify the gauge equation with an additive equality via
`unitVal`, and rearrange that equality in the actual abelian group of
units. Pairwise injectivity recovers the full ordered cochain equality
in the reverse direction. For an arbitrary gauge `b`, the zero-cochain
`-(vertexCochain U b)` has inverse vertex units equal to `b`.

Consequently `exists_isGauge_iff` says that a gauge exists if and only if
`w - z` is a zero-cochain differential. Combining it with the published
gauge classification proves `nonempty_iso_glued_iff`: for two closed
ordered unit one-cochains on the same family, their glued sheaves of
modules are isomorphic exactly when their difference is a coboundary.
This last equivalence needs no cover assumption; the earlier full-cover
hypothesis makes these glued sheaves actual line bundles.

This is an internal construction from the published actual-unit
presheaf, ordered Čech restriction/differential formulas, and the
published transition-cocycle gluing and gauge classification. Its proof
route is described above; it does not claim to translate an external
source theorem. It gives a fixed-family isomorphism criterion. It does
not assert that every line bundle has a cocycle on this family, construct
a map from actual sheaf cohomology to Picard classes, prove refinement
compatibility or naturality, or establish Picard representability.
