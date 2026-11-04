# Standard-integral composition at the common ambient source scale

This internal derived adapter specializes the existing countable-topology
composition theorem to intrinsic Haar measures normalized by one compact open
`Q` of the original ambient group. Its motivating source is Waldspurger (2003),
`waldspurger-2003-plancherel`, I.1, printed p.240 / PDF page 6 (index 5),
for the common special-compact normalization, and IV.1, printed p.279 / PDF
page 45, for the complementary-unipotent iterated-integral setup. The rational
composition identity IV.1(12), printed p.283 / PDF page 49, remains a later
application with separate geometry, convergence and continuation obligations.

The compact open, original closed subgroups `U₀`, `U₁`, `U₂`, `V`, `W`, and
actual ordered charts `D` are supplied. The ambient group is nonarchimedean,
Hausdorff, locally compact and second countable. All individual subgroup and
quotient Borel structures remain explicit. The representation uses the
canonical `SmoothRep` of the common Levi with independent ambient-group and
representation-carrier universes.

`sourceFirstCompactOpen` pulls `Q` back to the actual first complement
`V.subgroupOf U₁` along its original ambient inclusion. The theorem
`firstCompactComplement_source` proves that the already defined change
between the two actual copies of `V` carries precisely this compact open to
the nested complement's source compact open. The proof is extensional
reflexivity: the maps preserve the literal ambient element.

`comp_hasIntegral_at_sourceScale` uses `subgroupCompactOpenHaar` on `U₁`
and `U₂`, `sourceIntersectionHaar` on their actual kernel intersections,
and the three actual nested source measures of `StandardIntertwiningSourceFactors`.
These are intrinsic measures on their displayed carriers. Five right-invariance
premises remain explicit for the first kernel intersection, middle intersection,
nested endpoint kernel and both actual complement copies. They do not follow
from closedness alone. `sourceEndpointRightInvariant` derives the endpoint
intersection's right invariance from the supplied nested-kernel right
invariance and the exact kernel measure equality. The endpoint compatibility
premise installs this derived fact locally; it requires no sixth
right-invariance hypothesis.

Four actual quotient measures are supplied, with four `IsCompatible` premises
at exactly these source scales: the nested intersection quotient and the
quotients for `U₀` in `U₁`, `U₁` in `U₂`, and `U₀` in `U₂`. Three genuine
local Cartesian image identities remain hypotheses. They use inverse images
of the same ambient `Q` in the first, intersection and second charts. No
local product identity is inferred from a group homeomorphism alone.

The implemented proof derives compactness of `R`, `S`, `B`, `T`, `C` from the
closed embeddings and compactness of `Q`, using `compactOpenPreimage_isCompact`.
It derives the four mass-one identities for `R`, its first-kernel part, `S`
and its nested-kernel part from the public intrinsic source normalization
lemmas. The first-complement equality rewrites the first local geometry into
the exact form expected by the countable-topology adapter. The exact
`intersectionKernelMeasure_source` equality rewrites endpoint compatibility,
without altering its quotient measure. The two exact source-factor equalities
rewrite `OrderedScalarIntegrable` to the existing normalized-factor form.
The proof then applies `comp_hasIntegral_of_secondCountable`, which derives
the remaining regularity, S-finiteness and product Borel facts internally.

Both actual `HasIntegral` witnesses, their same intermediate induced section
`F`, and the same output function `J` are retained. The absolute scalar
integrability hypothesis tests the original-carrier function against all smooth
functionals with the intrinsic source Haar measures on the original `V` and
`W`. The conclusion is `HasIntegral` for the same endpoint quotient measure
supplied in endpoint compatibility. No quotient measure is selected, replaced
or rescaled after receiving either integral witness.

This unit does not construct the special maximal compact of the source,
realize the ordered charts or local product identities for reductive rational
points, prove right invariance or compatible quotient-measure existence in
those applications, prove integral convergence or original-carrier
representability, or prove rational continuation. It assumes no irreducibility
of parabolic induction and closes no whole-task Plancherel condition.
