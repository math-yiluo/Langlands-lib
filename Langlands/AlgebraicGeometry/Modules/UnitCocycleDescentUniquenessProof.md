# Proof of descent uniqueness for line bundles with trivialized pullback

The entry theorem `Langlands.Scheme.Modules.unitCocycleDescentUniqueness` proves the exact
`UnitCocycleDescentUniquenessStatement`. It applies the conditional theorem
`UnitCocycleDescentUniqueness.uniqueness_of_homGluing` to the published gluing theorem
`OpenCoverHomGluing.openCoverHomGluing`. The proof descends local isomorphisms over open
subsets of `Y` on which both bundles are trivial, then glues them. It does not use a global
equalizer of `p_* p^*`.

## Compatibility with the trivializations

Let `t : T ⟶ Y` and `φ : t^* L ⟶ t^* L'`. A commutative square `h ≫ t = g ≫ p` with
`h : Z ⟶ T` and `g : Z ⟶ X` gives two maps `h^* t^* L ⟶ g^* O_X`. The first applies `h^* φ`,
then the canonical square comparison `squarePullbackIso` for `L'`, then `g^* α'`. The second
applies the square comparison for `L`, then `g^* α`. `CompatibleAt` says that these two maps
are equal. `Compatible p α α' t φ` says that this holds for every such square.

- `squarePullbackIso_precomp` and `squarePullbackIso_change_base` describe how the square
  comparison behaves under precomposition and under a change of base `u ≫ t = t'`. Both are
  derived from the published `compHom_assoc` and `squarePullbackIso_comp`. The comparison
  `compIso u t t' e N : u^* t^* N ≅ t'^* N` is `pullbackComp` followed by `pullbackCongr`.
- `compatibleAt_precomp` shows that compatibility at a square is inherited by its
  precomposites. So `compatible_of_universal` reduces `Compatible` to the single universal
  square formed by the projections of `X ×_Y T`, using `pullback.lift`.
- `Compatible.change_base` shows that if `φ` is compatible over `t`, then its transport
  `(compIso u t t' e L)⁻¹ ≫ u^* φ ≫ compIso u t t' e L'` is compatible over `t'`.

## Uniqueness and local existence

Suppose `t^* L` and `t^* L'` are trivial and the projection `pullback.snd p t` is an
epimorphism. Then `compatible_unique` shows that a compatible isomorphism is unique. At the
universal square, compatibility determines the pullback of `φ` along `pullback.snd p t`. The
published `pullbackIso_injective_of_trivializations` then identifies two such isomorphisms.

`exists_compatible` builds a compatible isomorphism when `p` is quasi-compact, flat and
surjective. It assumes that `t^* L` and `t^* L'` are trivial. The two trivializations of
the pullbacks of `L` and `L'` to `X ×_Y T` are `β` and `β'`. Each is the square comparison,
then the pullback of `α` (respectively `α'`), then `pullbackUnitIso`. The published
`equalCompositeUnitAut_square` rewrites the transported automorphisms of `β` and `β'` as
those of `α` and `α'`, which are equal by hypothesis. `compatible_of_equalCompositeUnitAut_eq`
turns this equality into the compatibility condition required by the published
`compatibleIsoDescent_of_trivializations`, applied to `pullback.snd p t` and `β ≪≫ β'⁻¹`.
The descended isomorphism has the prescribed pullback, which is compatibility at the
universal square, and `compatible_of_universal` concludes. Mathlib supplies the
quasi-compactness, flatness and surjectivity of `pullback.snd p t`, so the base-changed
projection is an effective epimorphism.

## Covering and gluing

In `uniqueness_of_homGluing`, `IsAffineHom p` supplies `QuasiCompact p`.
`structureAutScalar_injective` turns the scalar hypothesis into equality of the transported
automorphisms. For each `y : Y`, the open set `V y` is the intersection of the chosen
trivializing opens of `L` and `L'` at `y`. These sets cover `Y`, and
`Y.openCoverOfIsOpenCover` gives an open cover `𝒰`. By `nonempty_trivial_of_le` and
`nonempty_trivial_change_base`, both bundles are trivial after pullback along each `𝒰.f i`
and along every further base change. `exists_compatible` gives compatible isomorphisms
`E i` over each `𝒰.f i`.

On an overlap, let `w` be `pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i`. By
`Compatible.change_base`, the transports of `E i` and `E j` to `w` are both compatible.
Both bundles are trivial over `w`, so `compatible_unique` makes these transports equal.
`squarePullbackIso_hom_eq_compIso` rewrites this equality as the overlap condition of the
published `openCoverIsoGluing_of_homGluing`. That theorem, with the gluing hypothesis,
produces an isomorphism `L.obj ≅ L'.obj`, and `ObjectProperty.isoMk` makes it an
isomorphism in `LineBundle Y`.

## Provenance

The route follows the descent of isomorphisms for quasi-coherent modules along faithfully
flat morphisms in the Stacks Project, Descent, Proposition 5.2 (Tag 023T), localized to
opens where both line bundles are trivial. It differs from that reference by using base
change along `t` rather than preimages of affine opens, and by deriving agreement on overlaps
from the uniqueness of compatible isomorphisms. The helper lemmas are internal and introduce
no hypotheses beyond those of the target statement.
