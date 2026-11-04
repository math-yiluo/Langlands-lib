# Independence of the adelic topology from arithmetic spreads

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.6 following Remark 3.5 and equation (3.5.1), explains
that the arithmetic direct limit is intrinsic to the generic-fiber
scheme and that increasing the initial finite set has no effect.
Section 4, printed p.9, combines this comparison with Theorem 3.6 to
give the adelic points a topology functorial in the field-scheme.
This target formulates independence of both the chosen arithmetic
model and the specified generic-fiber isomorphism as literal equality
of topologies on the same actual point set.

`CurvePlaceSpreadTopologyIndependenceStatement` quantifies two arbitrary
finite sets S and U of actual curve places and models X over the
original outside-S integer ring and Z over the original outside-U
integer ring. Both structure morphisms are locally of finite type and
quasi-compact, expressing finite type. A scheme Y over the original
field F is supplied, together with arbitrary isomorphisms from the
actual pullback generic fibers of X and Z to Y. The two topologies
`curvePlaceSpreadAdelePointTopology` defined using these data must be
equal on `CurvePlaceAdelePoints k F Y`.

`NumberFieldSpreadTopologyIndependenceStatement` states the same
assertion for an arbitrary number field K, its actual outside-S
integer subalgebras and `NumberFieldAdelePoints K Y`. These are points
over the full `Adeles K`, including all infinite factors. S and U
index only the finite places; the arithmetic level construction
already includes every infinite place.

The generic-fiber objects and point equivalences are the actual
pullback constructions of `AdelicGenericFiberPoints`. Their integer
actions, field actions, and specified generic-fiber isomorphisms are
retained. Each topology being compared is independently defined from
its model's arithmetic final topology. Equality is a conclusion, with
no continuity, comparison homeomorphism or eventual model isomorphism
assumed. In particular S and U need not be comparable, X and Z need
not arise by base change from one another, and the generic-fiber
isomorphisms may differ even when the two models coincide.

No affineness or separatedness hypothesis is imposed on the models
or on Y. The curve clause assumes a perfect constant field k, a
function field F over k, and a compatible tower of k- and
rational-function-field algebra structures. This includes the source's
positive-characteristic global fields and extends the assertion to
perfect constant fields. The number clause assumes an arbitrary
number field. Both clauses allow empty S and U and an arbitrary common
universe.

The precise formulation and broader scope are derived: the integer
rings are Noetherian by `AdelicSIntegersNoetherianProof`, including
empty initial sets, so these finite-type models are quasi-separated
and of finite presentation. The actual integer-ring colimit and
scheme-model isomorphism descent then supply a common finite stage
where a prescribed generic-fiber isomorphism descends. Initial-set
invariance and functoriality under an actual same-base model
isomorphism give the required topology equality. This describes the
mathematical route supporting the target, rather than assuming those
results in its hypotheses.

`AdelicSpreadTopologyIndependenceStatement` is the conjunction of the
two clauses. This unit supplies a proposition interface; its proof
remains a separate obligation. It does not assert existence of an
arithmetic spread for every finite-type field-scheme, equality with an
independently defined affine evaluation topology, or the other
topological properties of section 4.
