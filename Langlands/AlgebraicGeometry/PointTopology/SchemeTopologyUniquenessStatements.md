# Source axioms and uniqueness on actual nonaffine scheme points

This unit states the uniqueness assertion in Brian Conrad, *Weil and
Grothendieck approaches to adelic points*, December 31, 2011, Proposition 3.1,
printed page 4. The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The formulation with a base ring `R` and a possibly different value ring `S`
is a derived relative extension, specializing to the source when `S = R`.

## Actual assignments and requirements

`SchemePointTopologyFamily R S` assigns an arbitrary topology to the actual
`RingPoint R X S`, for every scheme `X` over `Spec R` whose structure map is
locally of finite type. It has no assumed compatibility fields and no
restriction to affine, separated, quasi-compact or finitely presented schemes.
`schemePointTopologyFamilyToAffines` restricts such an assignment to the
existing finite-type affine family. `evaluationSchemePointTopologyFamily`
is the independently defined `schemePointTopology` assignment, built from
all actual affine-open point charts, on this full locally finite type domain.

`SchemePointTopologyAxioms` lists precisely the five requirements of the
source, counting closed and open immersions separately:

- Continuity of actual postcomposition for every relative scheme morphism.
- The actual point comparison for every limiting relative pullback cone is a
  homeomorphism onto the compatible-pair subtype of the product. The common
  point on the cone's base scheme varies; it is not a single fixed fiber.
- Closed immersions induce embeddings, without requiring closed images.
- Open immersions induce open embeddings.
- Evaluation of the coordinate on the actual affine line identifies its point
  topology with the given topology on `S`.

The pullback condition includes an explicit locally finite type instance for
its apex, just as the existing affine axiom does. Actual pullbacks of the
specified schemes have this property. It introduces no finite-presentation or
separation requirement. The comparison function is the existing actual cone
comparison; its historical `affineScheme` prefix imposes no affine condition.

## Uniqueness target and relative provenance

`SchemePointTopologyUniquenessProperty R S` asserts that every assignment
satisfying these five axioms equals the named affine-chart final assignment.
`R` and `S` are commutative rings in an arbitrary common universe, with their
specified `Algebra R S`. Only `S` has a topology. The statement retains the
source setting: `S` is a local topological ring with `IsOpenUnits S`, which
means that its existing value-and-inverse unit space is an open subspace of
`S`. It assumes neither Hausdorffness nor local compactness of `S`.

The derived relative formulation is justified by the already proved affine
four-axiom characterization for `S`-valued `R`-algebra points, in which base
coefficients evaluate to constants. Restricting the five requirements to
finite-type affine schemes gives exactly those four axioms. Hence every
actual affine chart has its existing evaluation topology. Such charts remain
locally of finite type. Their point inclusions are open embeddings by the
open-immersion axiom, and they cover all points because `S` is local. A
cover by these open subspaces determines the topology and forces equality
with the named final topology on the same carrier.

This is a uniqueness statement. It does not assert that the canonical
assignment satisfies every axiom; existence, including nonaffine fiber-product
compatibility, remains a separate obligation. It does not assume that existence
or the desired chart compatibility as a field of the family. The remaining
Hausdorffness, compactness, arithmetic and algebraic-space assertions of the
paper are outside this unit.
