# Valuative existence after a dominating extension: proof

Author: Worker 60.

`spaceValuativeExtensionExistence` proves
`SpaceValuativeExtensionExistenceStatement.{u}`
(`SpaceValuativeExtensionExistenceStatement.lean`). This is the separated
form of Stacks Project, *Morphisms of Algebraic Spaces*, Lemma 67.42.2(1)
(Tag 0A3X), printed pp. 89–90, using the extension diagram of
Definition 67.41.1 (Tag 03IX), printed pp. 82–83. It keeps the extra
quasi-compactness hypothesis of the statement.

The registered source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, file
`spaces-morphisms.pdf`, SHA-256
`46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.

## Statement proved

Let `f : X ⟶ Y` be a quasi-compact, separated, universally closed morphism
of algebraic spaces over an arbitrary scheme `S`. Let `A` be a valuation ring
with fraction field `K`, both in universe `u`, and let `s : Spec A ⟶ S`.
Let `x` be a section of `X` over `Spec K` and `y` a section of `Y` over
`Spec A` with `f(x) = y|_K`. Then `HasDominatingValuativeLift f A K s x y`
holds.

## Route of the Lean proof

The proof does not follow the source route through a specialization and a
valuation-ring extension. The Library already proves the stronger lift with
no extension: `spaceValuativeExistence : SpaceValuativeExistenceStatement.{u}`
in `SpaceValuativeExistenceProof.lean`. Its proof goes directly through
universal closedness, an étale chart and fppf descent. It does not import
the present target or `HasDominatingValuativeLift`.

Applied to the same data `S, X, Y, f`, the same three hypotheses and the same
`A, K, s, x, y` and the equation `f(x) = y|_K`, it gives a section `a` of `X`
over `Spec A` (structure map `s`) with `a|_K = x` and `f(a) = y`.

The witnesses for `HasDominatingValuativeLift` are the trivial extension:

- `B = A` and `L = K`, with their given instances;
- `i = RingHom.id A`, which is local (`IsLocalHom` instance of the identity),
  and `j = RingHom.id K`. The square
  `(algebraMap A K).comp (RingHom.id A) = (RingHom.id K).comp (algebraMap A K)`
  holds by `rfl`;
- the section over `B` is `X.pullback e a`. Here `e` is the morphism
  `Over.homMk (Spec.map (CommRingCat.ofHom (RingHom.id A))) rfl` from
  `Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ s)` to `Over.mk s`.
  The predicate asks for a section over the first test scheme, which is not
  syntactically `Over.mk s`.

The first equation of the predicate compares two pullbacks to the test
scheme `Spec K` over `S` with structure map
`Spec.map (ofHom (RingHom.id K)) ≫ Spec.map (ofHom (algebraMap A K)) ≫ s`.
After `pullback_comp` and `a|_K = x`, both sides are pullbacks of `a` along
morphisms of `Over S` with the same source and target. Their underlying
scheme morphisms are both `Spec.map (ofHom (algebraMap A K))` after `simp`
removes the identity spectra. The two pullbacks are therefore equal.

The second equation is `f(a|_e) = y|_e`. It follows from
`mapSections_naturality` and `f(a) = y`.

## Use of the consumer statement

One constraint of Task 5519 says not to assume an unproved statement or the
consumer `SpaceValuativeExistenceStatement`. It was written while the consumer
was unproved. The consumer enters this proof only through its published
theorem `Langlands.AlgebraicGeometry.AlgebraicSpace.spaceValuativeExistence`
(Worker 198). That theorem has an independently reviewed proof in the
Library at the workspace base `ed924aef420de137b4cbaa3b063a3618afcd73fd`.

An operator ruling of 2026-11-13 decides this case. It answers request
`3f2cf39c31b95526b126be48762ffe0a` and is recorded as a constraint of
Task 5519 revision 2. The ruling says that citing this published theorem is
not assuming an unproved statement or the consumer, so the target may be
derived from it. The import closure must still contain no proof of this
target, and it does not: `SpaceValuativeExistenceProof.lean` and its imports
neither import this module nor prove this target. The statement pair
`SpaceValuativeExtensionExistenceStatement.{lean,md}` and its import closure
are unchanged.

## Checks

`lean_check` of
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExtensionExistenceProof`
in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lake build) reports
no errors or warnings. The axioms of `spaceValuativeExtensionExistence` are
`propext`, `Classical.choice` and `Quot.sound`.
