# The semisimple anisotropic kernel of an actual Tits index: statements

Author: Worker 4741 (Task 5568).

Source: J. Tits, *Classification of algebraic semisimple groups* (1966),
§2.2, printed p.39 (proceedings PDF p.44), and the second-to-last paragraph
of §2.3 on the same page, with the notation of §2.1 (printed pp.38–39,
PDF pp.43–44). Registered source
`tits-1966-classification-algebraic-semisimple`; PDF SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.

Every declaration below is in `Langlands.GroupScheme`. The three
statements are unproved `Prop`-valued definitions, not axioms or theorems.
They build on the actual index data `TitsIndexData` of
`Langlands.GroupScheme.Reductive.TitsIndex`, which is used unchanged.

## Source content

In §2.1 Tits fixes a semisimple `k`-group `G`, a maximal `k`-split torus
`S`, a maximal torus `T ⊇ S` defined over `k`, compatible orders on
`X*(S)` and `X*(T)`, the simple roots `Δ` of `G` with respect to `T`, and
the subset `Δ₀ ⊆ Δ` of simple roots vanishing on `S`. In §2.2 he calls the
derived group `𝒟𝒵(S)` of the centralizer `𝒵(S)` the *semisimple
anisotropic kernel* of `G`. He notes that `Δ₀` is the set of simple roots
of `𝒟𝒵(S)` with respect to the maximal torus `T ∩ 𝒟𝒵(S)` and a suitable
ordering. In §2.3, the index is `Δ` with its Dynkin diagram, `Δ₀` and the
star action. The index of the semisimple anisotropic kernel is obtained from
that of `G` by removing the vertices not in `Δ₀` and the strokes ending at
them.

The name "semisimple anisotropic kernel" contains two facts that Tits
does not prove at this point: `𝒟𝒵(S)` is semisimple, and it is
anisotropic over `k`. `TitsAnisotropicKernelStatement` states both.
`TitsAnisotropicKernelIndexStatement` states the root-system and index
claims of §2.2 and §2.3.

## `TitsIndexData.KernelComparison d ι e`

Hypotheses: a field `k : Type u`; actual `k`-group schemes `G` and `D`,
each with affine and locally-finite-type structure morphism (instance
arguments); `d : TitsIndexData G`; a homomorphism `ι : D ⟶ G`; and
`e : TitsIndexData D`. It is a `Prop` asserting that there exist

- a homomorphism `τ : e.pinning.torus ⟶ d.pinning.torus` of commutative
  `k`-group schemes, from the maximal torus `T_D` of `e` to the maximal
  torus `T` of `d`, and
- an equivalence `φ` from the absolute root index of `e` onto the
  subtype of absolute roots `a` of `d` with `d.rootRestriction a = 0`,

with the following six conjuncts:

1. `groupHom τ ≫ d.pinning.inclusion = e.pinning.inclusion ≫ ι`: the
   square of `k`-group homomorphisms `T_D → T → G` and `T_D → D → G`
   commutes. So `T_D → D` factors through `T ∩ D`. When `T ∩ D` is a
   torus, maximality of `T_D` in `D` then forces `T_D = T ∩ D`, Tits's
   maximal torus.
2. For every root `b` of `e`, its character equals the base change of
   `τ` to `k_s = SeparableClosure k` followed by the character of
   `φ b`. Thus each root of `D` is the actual restriction of the
   corresponding root of `G` along `τ`.
3. For every root `b` of `e`, its cocharacter followed by the base change
   of `τ` equals the cocharacter of `φ b`. Coroots of `D` are pushed
   forward to the corresponding coroots of `G`.
4. The integral pairings agree: `⟨b, c^∨⟩` for `e` equals
   `⟨φ b, (φ c)^∨⟩` for `d`. This follows from conjuncts 2 and 3. It
   is kept explicit so that consumers of the Dynkin diagram need not
   derive it.
5. `b` lies in the base of `e` exactly when `φ b` lies in the base of
   `d`. Since `φ` is onto the roots with zero restriction, this
   identifies the simple roots of `e` with `Δ₀`, the vertices of
   `d.zeroVertices`.
6. For every `σ : SeparableClosure k ≃ₐ[k] SeparableClosure k` and every
   simple root `b` of `e`, `φ` carries the Library star action of `σ`
   for `e` on `b` to the star action of `σ` for `d` on `φ b`.

So the based absolute root datum of `D`, with its Cartan pairings and
its full star action on simple vertices, is the subdiagram of `d` on
`Δ₀`. The comparison uses actual characters and cocharacters over
`k_s`. It is not just an equality of abstract diagrams. Star invariance
of `Δ₀` is not a hypothesis. Conjuncts 5 and 6 imply it, since every
vertex of `Δ₀` is `φ b` for a simple root `b` of `e`. The sibling
target `TitsIndexStarInvariantStatement`
(`Reductive.TitsIndexRelativeStatement`, same task) states the
invariance on its own.

`KernelComparison` is not phrased through `TitsIndexEquiv`. That notion
compares two complete indices, and the subdiagram on `Δ₀` is not itself a
`TitsIndexData`. On simple vertices, conjuncts 4–6 give the Cartan-pairing
and star-action parts of such an equivalence onto `Δ₀`.

## `TitsAnisotropicKernelStatement`

For every field `k : Type u` and actual `k`-group scheme `G` with
affine, locally-finite-type structure morphism, every
`d : TitsIndexData G`, every `M` and `j : M ⟶ G` with
`(torusCentralizer d.splitInclusion).IsRepresentedBy j`, and every `D`
and `i : D ⟶ M` with `IsDerivedSubgroup i`, the conclusion is
`IsSemisimple D ∧ IsAnisotropic D`.

- `torusCentralizer d.splitInclusion` is the Library centralizer
  subgroup functor of the maximal split torus `S` chosen in `d`. It is
  tested after every refinement of the test scheme. `IsRepresentedBy j`
  says `j` is a monomorphism of schemes with range functor equal to it.
  So `M` is an actual representative of `𝒵(S)`.
- `IsDerivedSubgroup i` says `i` is a closed subgroup whose range functor
  is the scheme-theoretic `derivedSubgroup M`. So `D` is the actual
  `𝒟𝒵(S)`.
- `IsSemisimple D` is the Library notion: connected reductive with finite
  scheme-theoretic centre. `IsAnisotropic D` is `splitRank D = 0`.

## `TitsAnisotropicKernelIndexStatement`

Same hypotheses as `TitsAnisotropicKernelStatement`. The conclusion is

`∃ (_ : IsAffineHom D.X.hom) (_ : LocallyOfFiniteType D.X.hom)
  (e : TitsIndexData D), d.KernelComparison (i ≫ j) e`.

`TitsIndexData D` requires these two instances on `D`, so they are part
of the conclusion rather than hypotheses. This way the statement covers
every actual representative and does not narrow its scope. Note that
`e` already contains `IsSemisimple D` and a maximal split torus of `D`.
When `D` is anisotropic, as `TitsAnisotropicKernelStatement` asserts,
that torus is trivial and the positivity compatibility in `e` is
vacuous.

Together with conjunct 1 of `KernelComparison`, this is Tits's claim that
`Δ₀` is the set of simple roots of `𝒟𝒵(S)` with respect to the maximal
torus `T ∩ 𝒟𝒵(S)` and a suitable order. Conjuncts 4–6 are the §2.3
claim that the index of the anisotropic kernel is the subdiagram on `Δ₀`
with the restricted star action. The suitable order and the maximal
torus of `D` are existentially chosen inside `e`. The statement fixes
`d` but does not require `e.pinning.torus` to be the scheme-theoretic
intersection: conjunct 1 places it inside `T ∩ D`, as explained above.

## `TitsAnisotropicKernelStructureStatement`

It is exactly `TitsAnisotropicKernelStatement.{u} ∧
TitsAnisotropicKernelIndexStatement.{u}`, with no further hypotheses.

## Simply connected covers and isogenies

The task asks whether a simply connected cover is involved. It is not.
Tits §2.2 defines the semisimple anisotropic kernel as the actual derived
group `𝒟𝒵(S)`. Both statements concern this actual `D`, given by
`IsDerivedSubgroup i`, and its actual based root datum, without passing
to a simply connected cover or to an isogenous group. The root datum of
`D` with respect to `T_D` is compared with that of `G` through the
actual characters and cocharacters of conjuncts 2 and 3. That is an
identification of root systems, Cartan pairings and star actions, not an
isomorphism of `D` with any other group. The reductive anisotropic kernel
`𝒟𝒵(S) · Z₀` and its almost-direct-product decomposition, also in §2.2,
are not formalized here.

## Scope and retained proof obligations

- All fields `k : Type u` are allowed, of any characteristic and at
  arbitrary universe. No local-field hypothesis appears. Quasi-split `G`
  is included (then `Δ₀ = ∅` and `D` is trivial), as are anisotropic `G`
  (then `S` is trivial and `M` and `D` are all of the semisimple `G`).
- The statements quantify over all actual representatives `M` and
  `D`. They do not assert that representatives exist. The Library has
  this ingredient for `M`: `IsSplitTorus.exists_cocharacter_centralizer_eq`
  (`Rational.SplitTorusCentralizerReduction`) identifies
  `torusCentralizer d.splitInclusion` with the dynamic centralizer of
  one cocharacter. That centralizer is represented by
  `Dynamic.Affine.centralizerHom` from `Dynamic.Affine.centralizerScheme`
  (`Dynamic.Affine.isRepresentedBy_centralizerHom`). For `D`, the target
  `DerivedSubgroupRepresentabilityStatement` (`Derived.StructureStatement`)
  is proved by `derivedSubgroupRepresentability` in
  [Derived/RepresentabilityProof](../Derived/RepresentabilityProof.md).
- Independence of `𝒟𝒵(S)` from the choice of `S` up to `k`-isomorphism
  (§2.2) is not asserted here. Independence of the index from all
  choices is the sibling target `TitsIndexIndependenceStatement`
  (`Reductive.TitsIndexChoiceStatement`).
- Expected proof ingredients include the published targets
  `SplitTorusCentralizerReductiveStatement` (the centralizer `M` is
  connected reductive), `DerivedSubgroupSemisimpleStatement` (so `D` is
  semisimple), and `DerivedMaximalTorusIntersectionStatement` (`T ∩ D` is
  a torus). The rest of the work is the anisotropy of `D` and the root,
  base and star-action comparison. These are listed as a guide only.
  Their definitions do not prove anything here.
- The two substantive proof units are `TitsAnisotropicKernelStatement`
  and `TitsAnisotropicKernelIndexStatement`.
