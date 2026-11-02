# Representability and smoothness of actual finite-algebra units

`Langlands.AlgebraicGeometry.FiniteAlgebraUnits.RepresentabilityStatement.{u}`
is a proposition about the constructions imported unchanged from
`Langlands.AlgebraicGeometry.Units.FiniteAlgebra`. It quantifies over every
field `k : Type u`, every commutative `k`-algebra `A : Type u`, every natural
number `n`, and every basis `b : Module.Basis (Fin n) k A`. Its conclusion is
the conjunction

```lean
IsIso (candidateMap b) ∧ AlgebraicGeometry.Smooth (candidate b).hom
```

The basis is the sole finiteness input. There is no nontriviality,
positive-rank, reducedness, separability, or extra projectivity hypothesis
on `A`, and no assumption identifying a global-functions algebra with `k`.
The field may be imperfect.

Write `R = MvPolynomial (Fin n) k` and
`g = genericElement b = ∑ i, X i ⊗ b i` in `R ⊗[k] A`.
The published `determinant b` is the determinant `d` of multiplication by
`g`, equivalently its finite-free norm. The actual `candidate b` is
`Spec (Localization.Away d)` with its canonical structure map to `Spec k`.
Geometrically it is the principal open `D(d)` in affine `n`-space over `k`.
The construction already supplies `universalUnit b` on the actual fibre
product of this candidate with `Spec A`. Under the canonical
`fibreCoordinates b`, its underlying function is
`∑ i, algebraMap R (Localization.Away d) (X i) ⊗ b i`, as proved by
`universalUnit_formula`.

The intended representability argument is internal and derived from these
constructions. For any commutative `k`-algebra `B`, the base-changed basis
identifies an element `a` of `B ⊗[k] A` with `n` coefficients in `B`.
Multiplication by `a` is an endomorphism of a finite free `B`-module.
It is invertible exactly when its determinant is a unit. An element `a`
is a unit exactly when multiplication by `a` is invertible: a unit acts
with its inverse, while the inverse endomorphism applied to `1` gives an
inverse to `a`. The determinant is the evaluation of `d` at those
coefficients. The universal property of away-localization therefore
identifies these unit elements with points of the displayed principal open.
This argument applies to coefficient rings with nilpotents as well.

The first conjunct concerns the specific published natural transformation
`candidateMap b`. Its source is the actual lifted scheme Yoneda presheaf
of `candidate b` on the entire category `Over (Spec k)`. Its target
`presheaf k A` takes a scheme `T` over `Spec k` to
`ULift (Γ(T.left ×_(Spec k) Spec A, ⊤)ˣ)`.
For every morphism `h : T ⟶ candidate b`, `candidateMap_app` identifies
the value with the ordinary pullback of that same `universalUnit b` along
the induced morphism of actual fibre products. Thus the asserted
isomorphism fixes the canonical comparison, its universal element, and
its restriction maps.

An argument on affine tests alone does not supply this asserted
isomorphism. The intended extension takes an affine open cover of an
arbitrary `T`. On each affine open the coefficient and determinant
argument applies. Uniqueness of the coefficients makes them agree on
overlaps, and the corresponding morphisms into `D(d)` glue; equality of
units is also local. This must give an inverse to the actual
`candidateMap b` and respect restriction for every test scheme.
The statement retains empty, nonreduced, and non-quasi-compact tests,
without a chosen alternative comparison or a conditional
representability premise.

The second conjunct is smoothness of the structure map of this actual
candidate. The intended geometric argument identifies it with the
composite of the open immersion `D(d) → affine n-space` and the smooth
affine-space projection to `Spec k`; open immersions are smooth and
smooth morphisms compose. Rank zero is included: the published
`determinant_rank_zero` gives `d = 1`, and the candidate is isomorphic
over `k` to `Spec k`. A rank-zero basis allows the zero algebra.
Nilpotents in `A` and inseparability impose no restriction on this
principal-open argument.

This is an internal derived assertion, with provenance in the three
published modules `Units.RelativeGlobalUnits`,
`Units.FiniteAlgebraDeterminant`, and `Units.FiniteAlgebra`, together with
the usual finite-free determinant criterion, localization, and affine
geometry. No outside literature theorem is claimed to state this exact
interface. The preceding paragraphs explain the intended mathematical
conclusions. This statement module supplies only the Prop-valued
definition; it supplies no Lean proof of either conjunct. The
proper-scheme global-functions comparison and its use for Picard
representability remain separate work.
