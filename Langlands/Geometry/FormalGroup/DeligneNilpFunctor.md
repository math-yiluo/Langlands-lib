# The actual admissible Deligne class functor on Nilp

This module constructs a covariant functor on actual nilpotent coefficient
algebras. Its value is the existing quotient of admissible four-data
objects on `Spec B` by genuine four-data isomorphisms. Its map is actual
scheme pullback, with the coefficient identification proved from
naturality of the Spec/global-sections isomorphism.

The source motivation is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4), defining `Nilp` and
the four data `eta,T,u,r` at the page boundary, followed by conditions
(a), (b), (c) at the beginning of p.110. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The scalar comparisons and functor laws below are derived infrastructure.
This module retains the documented scope of the imported admissibility
predicate; it does not assert an independent identification with all of
Drinfeld's moduli interpretation.

## Parameters and objects

Let `O` be a commutative ring in universe `u`, let `d` be positive, and
let `π : O`. Let `F` be an `O`-algebra field in the same universe, with
`hπ : algebraMap O F π ≠ 0`. No local field hypothesis is needed by
these constructions.

`FormalGroup.Nilp O π` is the existing full subcategory of commutative
`O`-algebras whose image of `π` is nilpotent. All `O`-algebra
homomorphisms between these algebras are retained. For its object `B`,
the imported `nilpGlobalScalar π B` is the actual homomorphism

```text
O → B → Γ(Spec B, ⊤),
```

where the second map is the inverse of `Scheme.ΓSpecIso`. Its value on
`π` is nilpotent by the existing `nilpGlobalScalar_nilpotent` theorem.
The functor's value `NilpSheafIsoClass d π F hπ B` is the existing
`SheafDatum.IsoClass` for that scalar map. Its representatives have an
actual framed graded coefficient lattice, structural graded tangent
sheaf, Pi-compatible locally generating map `u`, and proofs of the
constructed three-condition admissibility predicate. The quotient
relation requires existence of a genuine isomorphism preserving all four
data. The values lie in `Type (u + 1)`.

## Scalar-aware scheme pullback

`SheafDatum.IsoClass.pullbackTo` applies the existing actual class
pullback along `f : S' ⟶ S` and transports its result along a proved
equality `pulledGlobalScalar f φ = φ'`. The equality is the only
coefficient identification used. It is not a supplied comparison of
sheaf data.

`pullbackTo_id` reduces to the proved identity law for the underlying
class pullback. The proof of the scalar equality is irrelevant.
`pullbackTo_comp` eliminates the two successive scalar equalities and
applies the proved composition law for actual class pullbacks. The
remaining composite scalar equality is definitionally reflexive, up to
proof irrelevance. `pullbackTo_congr` proves independence of the
presentation of the actual base morphism by eliminating its equality.

## Algebra morphisms and actual global scalars

For `f : B ⟶ B'`, `nilpSpecMap f` is exactly `Spec.map` of its
underlying ring homomorphism. Its direction is `Spec B' ⟶ Spec B`.
`nilpSpecMap_id` follows from the identity law of `Spec.map`.
`nilpSpecMap_comp` uses functoriality of forgetting algebra scalars and
the contravariant composition law for `Spec.map`.

`nilpGlobalScalar_naturality` proves

```text
pulledGlobalScalar (nilpSpecMap f) (nilpGlobalScalar π B)
  = nilpGlobalScalar π B'.
```

The proof evaluates `Scheme.ΓSpecIso_inv_naturality` on the actual image
of `a : O` in `B`. The `O`-algebra homomorphism property identifies its
image under `f` with the image of `a` in `B'`. Reversing this equality
gives precisely the equality of global scalar maps. No compatibility of
these global sections is assumed.

## The constructed functor

`nilpSheafClassMap` is `pullbackTo` along `nilpSpecMap`, using the
preceding proved scalar equality. Thus an algebra map acts on a
representative by actual inverse image of its lattice and frame and
structural pullback of its tangent sheaf and map `u`; the preservation of
the admissibility conditions and of genuine isomorphisms is supplied by
the imported constructed pullback.

`nilpSheafClassMap_id` first replaces the actual identity Spec map by
the scheme identity using `pullbackTo_congr`, then applies
`pullbackTo_id`. `nilpSheafClassMap_comp` identifies the Spec map of the
algebra composite with the reverse composite of Spec maps and applies
`pullbackTo_comp`. Two reversals, from Spec and from sheaf pullback, give
the covariant direction

```text
classMap (f ≫ g) x = classMap g (classMap f x).
```

`nilpSheafClassFunctor` packages these actual object and map
constructions with the two proved laws.

## Scope

The existing admissibility predicate uses the constructed constant-locus
and total residue-fibre conditions and all-integer stalkwise determinant
normalization. Its documented remaining comparisons are unchanged:
integral injectivity, tensor/stalk comparison, and equivalence with an
independently constructed exterior-power subsheaf equality. No existence
theorem for these classes is proved here. This module constructs neither
the normalized `PGL(d,F)` action nor the equivalence with special formal
modules nor representability. It takes no representing object, universal
object or uniformization isomorphism as input.
