# Principal rational points in actual adelic groups

Let `F` be an arbitrary number field and `G` an actual affine group scheme over
`Spec F`. The actual principal map `rational` is injective: equality of adelic
points implies equality of every regular-function value; injectivity of the
field-to-adele ring map recovers equality of rational regular values, and affine
point evaluation is faithful. The principal map into the norm-one subgroup is
therefore also injective.

A global regular function evaluated on a principal rational point is a
principal additive adele. `principalCoordinate` packages this value in the
existing subgroup `principalAdeles F`, with its actual subspace topology.
It is continuous by regular-function continuity and restriction to the
principal subgroup.

Assume additionally that the structure morphism of `G` is locally of finite
type. The actual global-section algebra is then finitely generated. A finite
polynomial presentation and the previously proved affine point/algebra point
homeomorphism supply finitely many regular evaluations giving a topological
embedding into a finite power of the adele ring. These evaluations restrict
to a continuous injection of the principal rational subgroup into a finite
product of the existing principal additive adeles. The published
`principalAdeles_discreteTopology` makes that finite product discrete, so the
actual principal rational subgroup is discrete. It is closed because a
discrete subgroup of a Hausdorff topological group is closed.

The number field is countable as a finite-dimensional rational vector space.
The principal additive adeles are a surjective image of this countable field,
and the finite-coordinate injection proves countability of the principal
rational subgroup. Injectivity of the actual principal map then proves
countability of the rational group itself. No second-countability assumption
on the adelic coefficient ring is used.

`rationalNormOneSubgroup` is precisely the image of the actual principal map
into the norm-one group. Its continuous injective inclusion in the full
principal subgroup transfers discreteness and countability; the Hausdorff
topological group structure again gives closedness.

The source assertion is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Section 2.6, printed pages 67–68, especially the
principal discreteness and closedness sentence following (2.19). Exercise 2.2
on printed page 73 supplies the general coefficient-embedding route.
The implemented proof reuses the independently published additive-adele
argument and the finite-coordinate regular-evaluation topology rather than
choosing a faithful matrix representation. Countability and the norm-one
subgroup transfer are internal consequences of these constructions. No
connectedness, smoothness or reductivity assumption is needed for this unit.

The split-centre quotient, restricted-product comparison, Haar and quotient
measures, finite volume, and reduction theory remain separate obligations.
