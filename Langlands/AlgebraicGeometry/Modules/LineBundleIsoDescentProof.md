# Proof of faithfully flat descent of isomorphisms between line bundles

Module `Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof`, namespace
`Langlands.Scheme.Modules.LineBundleIsoDescent`.

## Main result

`lineBundleIsoDescent : LineBundleIsoDescentStatement.{u}` proves the Library
proposition `Langlands.Scheme.Modules.LineBundleIsoDescentStatement` (module
`Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStatements`). Let
`p : X ⟶ Y` be quasi-compact, flat and surjective, let `M` and `N` be locally
free of rank one on `Y`, and let `e : p^*M ≅ p^*N` intertwine the canonical
equal-composite comparisons `equalCompositeIso p a b h`. Then there is exactly
one `e₀ : M ≅ N` with `(Scheme.Modules.pullback p).mapIso e₀ = e`.

The proof reduces to the published case of trivial modules
(`UnitCocycleDescentUniqueness.compatibleIsoDescent_of_trivializations` and
`pullbackIso_injective_of_trivializations`, which underlie
`TrivialIsoDescentStatement`) by working Zariski-locally on `Y`. It then glues
with the published `openCoverIsoGluing_of_homGluing openCoverHomGluing`.

## Compatibility with `e` over a base change

For `t : T ⟶ Y` and `φ : t^*M ⟶ t^*N`:

- `CompatibleAt p e t φ g h hs`, for a factorization `hs : h ≫ t = g ≫ p` with
  `g : Z ⟶ X`, `h : Z ⟶ T`, says that `h^*φ` and `g^*e.hom` agree after the
  square comparisons `squarePullbackIso p h g t hs` (from
  `SquarePullbackComparison`).
- `Compatible p e t φ` says this holds at every factorization.

Lemmas:

- The existing `Langlands.Scheme.Modules.squarePullbackIso_naturality` from
  `RigidifiedClassesZariskiSeparatedProof` supplies naturality of square
  comparisons in the module.
- `hom_ext_of_openCover`: module morphisms whose pullbacks to every member of an
  open cover agree are equal (uniqueness part of `openCoverHomGluing`).
- `compatibleAt_precomp` and `compatible_of_universal`: compatibility is stable
  under precomposition, so it suffices to check it at the universal
  factorization `pullback.snd p t ≫ t = pullback.fst p t ≫ p` through
  `X ×_Y T`.
- `Compatible.change_base`: compatibility over `t` gives compatibility of the
  transported morphism over `u ≫ t = t'`.
- `compatible_pullback`: the pullback `t^*E` of a global `E : M ⟶ N` with
  `p^*E = e.hom` is compatible.
- `compatible_unique`: if `t^*M` and `t^*N` are trivial and `pullback.snd p t`
  is an epimorphism, two compatible isomorphisms agree. Their pullbacks along
  `pullback.snd p t` coincide, and the published
  `pullbackIso_injective_of_trivializations` applies.
- `squareTransport_compatible` and `exists_compatible`: if `t^*M` and `t^*N`
  are trivial and `p` is quasi-compact, flat and surjective, transporting `e`
  to `X ×_Y T` through the square comparisons gives an isomorphism that
  satisfies the hypothesis of `compatibleIsoDescent_of_trivializations` for
  `pullback.snd p t`. The descended isomorphism is then compatible.
  `equalCompositeIso_square` from `SquarePullbackComparison` verifies the
  equal-composite condition.

## Assembly

Cover `Y` by the opens `V y = U_M(y) ⊓ U_N(y)`, the intersections of chosen
trivializing opens of `M` and `N` at `y`, using `Y.openCoverOfIsOpenCover`.
On each member both modules are trivial (`nonempty_trivial_of_le`).

1. Uniqueness: two descents of `e` are compatible after pulling back to every
   cover member (`compatible_pullback`), so they agree there
   (`compatible_unique`) and hence globally (`hom_ext_of_openCover`).
2. Local existence: `exists_compatible` gives a compatible `E i` on every cover
   member.
3. Gluing: on an overlap, the two transports of `E i` and `E j` are compatible
   isomorphisms over the same base `w = pullback.fst ≫ 𝒰.f i` with trivial
   pullbacks (`nonempty_trivial_change_base`), so `compatible_unique` makes
   them equal. This is the overlap condition of the published isomorphism
   gluing, which produces `E₀ : M ≅ N`.
4. `p^*E₀ = e`: this is checked on the cover `𝒰.pullback₁ p` of `X`, using
   compatibility of `E i` at the factorization through `X ×_Y U_i`.
