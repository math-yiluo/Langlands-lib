# Pointed-morphism rigidity over an arbitrary base

`Langlands.AbelianScheme.pointedMorphismRigidity.{u}` proves exactly the
published proposition
`Langlands.AbelianScheme.PointedMorphismRigidity.{u}`. For every scheme
`S : Scheme.{u}`, actual group schemes `A H : GroupScheme S`, and morphism
`f : A.X ⟶ H.X`, assume that `A` is smooth, proper and geometrically
connected over `S`, that `H` is locally of finite presentation,
quasi-compact and quasi-separated over `S`, and that
`η[A.X] ≫ f = η[H.X]`. The conclusion is `IsMonHom f`, namely preservation
of the actual unit and multiplication in `Over S`.

The base and universe are arbitrary. Neither group scheme is assumed
commutative, and the proof uses the given group objects rather than an
explicit-commutativity bundle. It imposes no separatedness hypothesis on
`H`. The published target and its imports are unchanged.

## Implemented proof

Let `P = A.X ⊗ A.X` be the categorical product in `Over S`, and put
`e = lift η[A.X] η[A.X]`. Form the multiplicativity defect

```text
d : P ⟶ H.X,
d = (μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f)).
```

The product and division are the group operations on morphisms into the
given group object `H`. The order of the two factors is fixed as written.
The helper `isMonHom_of_defect_eq_one` uses `div_eq_one`, the definition
of this morphism multiplication, and categorical product identities to
deduce preservation of multiplication from `d = 1`. Together with the
given unit equation, this gives `IsMonHom f`.

The helper `defect_section` uses the group unit laws and the given
pointedness equation to prove `e ≫ d = 1`. On underlying schemes this
says `e.left ≫ d.left = η[H.X].left`. Also `e` is a section of `P.hom`,
because it is a morphism from the monoidal unit in `Over S`.

For each point `s : S`, let
`F = Over.pullback (S.fromSpecResidueField s)`. Apply the published theorem
`Langlands.AbelianScheme.fieldPointedMorphismRigidity`, imported from
`Langlands.AbelianScheme.FieldPointedMorphismRigidityProof`, to the
pulled-back group objects and `F.map f` over `S.residueField s`.
Smoothness, properness, geometric connectedness and the three
finite-presentation properties survive base change. The monoidal
functor's unit formula transports the pointedness equation. Thus
`F.map f` satisfies `IsMonHom`.

The helper `map_defect_eq_one` now proves `F.map d = 1`. It rewrites
source multiplication as the product of the two projections, then uses
functoriality of composition, multiplication and inverse, followed by
multiplication preservation for `F.map f` and group cancellation. This
avoids a separate comparison between the pulled-back product object and
the product of the pulled-back objects.

The helper `pointwise_eq_of_fiber_map_eq` turns these fibre equalities
into equality of the underlying point maps of `d` and the unit. For
`x : P.left`, it uses the fibre over `P.hom x`, composes the equality of
pulled-back morphisms with the projection to `H.X.left`, evaluates at
`P.hom.asFiber x`, and applies `Scheme.Hom.fiberι_asFiber`. This step
does not infer equality of scheme morphisms from pointwise equality.

The structure map `P.hom` is smooth and proper by base change and
composition. It is geometrically connected by
`GeometricallyConnected.comp`; smoothness supplies the universal
openness used by the composition instance. The published theorem
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`,
imported from
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof`,
therefore gives `IsIso (P.hom.app U)` for every open `U` of `S`.

Apply the published theorem
`Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions`, imported
from `Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof`,
to `P.hom`, its section `e.left`, and `d.left`. The pointwise equality
above and the section value of the defect supply its topological
constancy hypothesis. The theorem compares the structure-sheaf maps as
well and gives the equality of scheme morphisms

```text
d.left = P.hom ≫ e.left ≫ d.left.
```

The section value identifies the right-hand side with
`P.hom ≫ η[H.X].left`, which is the unit morphism from `P` to `H.X`.
Extensionality in `Over S` gives `d = 1`, and the defect criterion
finishes the proof.

## Provenance and contributions

Worker 143 designed and implemented this assembly. Its three substantial
geometric inputs are reused through their published theorem names: field
pointed-morphism rigidity by Workers 334 and 143, relative global
functions by Worker 299, and section/global-functions factorization by
Workers 266 and 143. Their companion Markdown files explain their
proofs and sources. The private helpers here are elementary group,
functoriality and fibre-evaluation calculations.

This is an internal derived proof of the stronger target recorded in
the statement's companion Markdown. Lan's 2008 thesis, Corollary
1.3.1.6, printed p.108 (PDF p.148), is its inspiration; Definition
1.3.1.1, printed p.103 (PDF p.143), gives the source geometric conditions
without commutativity. The thesis convention on PDF p.36 (printed
p.xxxvi), the 2021-03-14 errata pp.1 and 8, and the revised Corollary
1.3.1.6, printed pp.70–71 (PDF pp.98–99), show that Lan's source result
requires a separated target. The present arbitrary-base target omits
that requirement. Its global factorization step supplies an independent
route that does not require target separatedness.

The field prerequisite uses the automatic separatedness of group schemes
over fields; this does not assert separatedness over the original base.
The relative-global-functions prerequisite follows the route behind
Stacks Tag 0E0L, with its implemented Čech-algebra replacement documented
in that proof. The factorization theorem is an internal scheme and
sheaf argument. Thus neither Lan's locally noetherian reduction nor the
standing assumptions of GIT Chapter 6 are silently imposed on the
arbitrary-base theorem proved here.
