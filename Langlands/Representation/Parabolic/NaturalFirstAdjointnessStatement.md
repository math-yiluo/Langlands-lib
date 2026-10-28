# Natural normalized first adjointness

The proposition `Langlands.Parabolic.NaturalNormalizedFirstAdjointnessStatement`
has universe parameters `uF`, `uV`, and `uW`. It is the conjunction of
`StandardNaturalFirstAdjointnessClause` and
`RefinedNaturalFirstAdjointnessClause`, with the same universes. It specifies
natural families of first-adjointness (Frobenius reciprocity) equivalences.
This file supplies no proof of either family.

## Scope and actual representations

Both clauses quantify every prime `p`, algebraic `PadicField.{uF} p`,
supplied `F.TopologicalData T`, natural rank `n`, and block shape `B`.
The refined clause also quantifies every `BlockRefinement B`. The topology
is `T.topology`, with its GL, product-Levi, and subgroup topologies.
The three universes are independent: `uF` for the field, `uV` for the
carrier of the ambient representation, and `uW` for the carrier of the
inducing representation.

In the standard clause the ambient input is any bundled complex representation
`π : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`. The inducing input is any
`σ : Rep.{uW} ℂ (B.Levi F.Carrier)` of the actual product Levi. In the refined
clause, `π` is a representation of the whole coarse product Levi
`B.Levi F.Carrier`. Then `σ` is a representation of the whole actual subgroup
`refinedLevi F.Carrier B S`. Each family member requires proofs of
`IsSmooth π.ρ` and `IsSmooth σ.ρ`. Every representation mentioned in an
equation below is therefore smooth. Since smoothness is a proposition, the
choice of proofs is immaterial by proof irrelevance.
There is no admissibility, finite-length, finite-dimensional-carrier,
irreducibility, compact-quotient, tensor-decomposition, or factorwise
hypothesis. No adjunction or duality is supplied as a premise.
Rank zero, empty shapes, and one-block shapes are retained. In the standard
clause a one-block shape `B` has trivial radical. In the refined clause the
refined radical is the product of the inner radicals of the shapes `S i`, so
it is trivial when every `S i` has one block. A one-block coarse shape `B`
can still have a nontrivial refined radical. For example, if `B = (2)` and
`S 0 = (1,1)`, the refined radical is the upper unipotent subgroup of `GL_2`.
The refined clause quantifies every refinement `S`, including these cases.

## The functors

In the standard clause, `i(σ)` is `T.normalizedParabolicInduced B σ.ρ`. Its
carrier is `Induction.SmoothFunctions` for the actual upper parabolic
`B.parabolic F.Carrier`, with inducing representation
`twist (T.parabolicHalfModulus B) (σ.ρ.comp (B.leviProjection F.Carrier))`.
Thus a vector is a function `φ : GL_n → σ` satisfying
`φ(q g) = δ_P(m_q)^(1/2) σ(m_q) φ(g)` and fixed under right translation by
some open subgroup. Here `m_q` is the Levi projection of `q`, and `δ_P` is
the positive upper modulus `T.leviModulus B`. The group acts by right
translation.

`r(π)` is `T.normalizedJacquet B π.ρ`. Its carrier is the existing
`B.JacquetModule π.ρ`: coinvariants of the restriction of `π` to the actual
parabolic, by its internal unipotent radical. Its quotient map is
`B.jacquetMk π.ρ`. The product Levi acts on a class `[v]` by
`δ_P(m)^(-1/2)` times the class of the action of the embedded block-diagonal
matrix.

In the refined clause the functors are `T.normalizedRefinedInduced B S` and
`T.normalizedRefinedJacquet B S`. Induction uses `refinedParabolic`,
`refinedLeviProjection`, and the positive `T.refinedParabolicHalfModulus B S`.
The Jacquet carrier is `RefinedJacquetModule B S π.ρ`. It is the ambient
coinvariant quotient of `π` by the actual refined unipotent subgroup, with
quotient map `refinedJacquetMk B S π.ρ`. Its refined Levi action uses the
inverse half of the same refined modulus. All functors and maps are the
existing Library constructions; no replacement functor is introduced.

## The family and its laws

For each fixed field, topology, shape, and refinement, the clause asserts one
family of complex-linear equivalences

`E π σ hπ hσ : Hom(π, i(σ)) ≃ₗ[ℂ] Hom(r(π), σ)`

indexed by all smooth inputs in the given universes. Here `Hom` is
`Representation.IntertwiningMap`. The family is quantified before its laws, so
one family must satisfy all three laws below.

1. **Evaluation.** For each `f : π → i(σ)` and `v ∈ π`, the class of `v`
   maps to the value of `f v` at the identity:
   `E f (B.jacquetMk π.ρ v) = Induction.eval (B.parabolic F.Carrier) _ (f v) 1`.
   The refined clause uses `refinedJacquetMk B S π.ρ v` and
   `Induction.eval (refinedParabolic F.Carrier B S) _ (f v) 1`.
2. **Naturality in the ambient variable.** For an intertwiner `a : π' → π`
   between smooth representations, `f : π → i(σ)`, and every quotient vector
   `x ∈ r(π')`, the equation is
   `E_{π'} (f.comp a) x = (E_π f).comp (r(a)) x`.
   Here `r(a)` is `T.normalizedJacquetMap B a`, or
   `T.normalizedRefinedJacquetMap B S a` in the refined clause.
3. **Naturality in the inducing variable.** For an intertwiner `b : σ → σ'`
   between smooth representations, `f : π → i(σ)`, and every quotient vector
   `x ∈ r(π)`, the equation is
   `E_{σ'} ((i(b)).comp f) x = b.comp (E_σ f) x`.
   Here `i(b)` is `T.normalizedParabolicInducedMap B b`, or
   `T.normalizedRefinedInducedMap B S b` in the refined clause.

The naturality equations are stated on arbitrary quotient vectors `x`, not
only on classes of representatives. By extensionality, they are equalities of
intertwiners. The evaluation law alone determines each `E f`, because the
quotient map is surjective. It is kept explicit so that consumers can use the
concrete formula.

## Original source and derived formulation

The source is W. Casselman, *Introduction to representations of p-adic
groups*, Chapter III, revision April 29, 2019, registered as
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
Page 1 fixes the conventions. There `G` is the group of rational points of
a Zariski-connected reductive group. Normalized induction is right translation
on smooth functions with `f(p g) = δ_P(p)^(1/2) σ(p) f(g)`. Page 1 introduces
it for admissible `σ`; the Library construction takes the smooth vectors of
the covariant functions for any `σ`. Page 4 defines the normalized Jacquet
module with the factor `δ_P^(-1/2)`. On the same page,
Proposition III.3.5 gives Frobenius reciprocity: for a smooth representation
`π` of `G` and a representation `σ` of `M`, composition with evaluation at
`1` gives `Hom_G(π, Ind(σ)) ≅ Hom_M(π_N, σ)`. With the two
normalizations, the modulus factors cancel, so the identification is plain
evaluation, as in the evaluation law above.

The proposition is an internal formulation of this evaluation reciprocity,
not a verbatim theorem of the source. Neither naturality equation appears in
the source. They are consequences of the evaluation formula: precomposition
by `a` and postcomposition by `b` commute with evaluation at `1` and with
passage to Jacquet classes. The combined statement is also internal.
It asks for one coherent family for actual `GL_n` and its standard block
parabolics, and a second one for refined parabolics of a coarse product Levi.
The source covers both cases separately, because a finite product of general
linear groups is connected reductive and the refined parabolic is a parabolic
of it, with Levi `refinedLevi` and radical the product of the inner radicals.
The refined clause applies to arbitrary representations of that whole group,
without any reduction to tensor products.

Smoothness of `σ` is required by the target task. Proposition III.3.5 itself
assumes only that `π` is smooth and that `σ` is a representation of `M`.
In this respect the hypotheses here are stronger than the source's.

## Relationship to existing targets

The generic `Langlands.Jacquet.characterReciprocity` in
`Langlands.Representation.Jacquet.ReciprocityProof` and the standard
`NormalizedFrobeniusClause` in
`Langlands.Representation.Parabolic.NormalizedJacquetStatement` are unchanged.
This proposition adds the naturality laws and the refined product-Levi clause
needed by the normalized second-adjointness assembly.

The published construction in `Langlands.Representation.Parabolic.NaturalFirstAdjointness`
supplies `Langlands.Parabolic.FirstAdjointness.equiv` and `refinedEquiv`. Its lemmas
`equiv_apply_mk`, `equiv_comp`, `equiv_inducedMap`, and their refined analogues
are intended for a separate proof of this proposition. This statement module
does not import that construction.
