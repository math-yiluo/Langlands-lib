# Point surjectivity of quotients by induced central tori

This module states that an fppf quotient of a connected reductive group by a
closed central induced torus is surjective on points with values in every
field extension. It also states the z-extension special case and proves that
the special case follows from the general statement. It proves neither
statement. The only proofs in the module are the reduction theorem and the
observation that an induced torus is a torus.

All declarations live in `Langlands.GroupScheme`, at an arbitrary universe
`u`. The field `k` and the extension field `K` both lie in `Type u`, because
`CommAlgCat.{u} k` requires this.

## Exact statements

`InducedTorusQuotientPointSurjectivityStatement` is the proposition

```text
∀ (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
  (Z : CommGroupScheme (Spec (CommRingCat.of k)))
  (H G : GroupScheme (Spec (CommRingCat.of k)))
  (i : Z.toGrp ⟶ H) (p : H ⟶ G),
  IsInducedTorus Z → IsClosedSubgroup i → IsCentral i →
    IsConnectedReductive H → IsConnectedReductive G →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
        Function.Surjective (H.affinePointsTarget p (CommAlgCat.of k K)).
```

In words: let `k` be any field and `K` any field extension of `k`. Let `H` and
`G` be connected reductive group schemes over `k`. Let `Z` be a commutative
group scheme over `k` that is an induced torus, with a closed central inclusion
`i : Z → H`. Let `p : H → G` be a homomorphism that is an fppf quotient whose
kernel is exactly the image of `i`. Then every `K`-point of `G` lifts to a
`K`-point of `H`.

`ZExtensionPointSurjectivityStatement` is the proposition

```text
∀ (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k))) (z : ZExtension G),
    Function.Surjective (z.H.affinePointsTarget z.p (CommAlgCat.of k K)).
```

It says that for every z-extension `1 → Z → H → G → 1` over any field `k`, and
every field extension `K/k`, the map `H(K) → G(K)` is surjective.

## Meaning of the hypotheses

Every predicate is an existing Library definition. None is replaced by a
supplied surjectivity field, a section, or a cohomology-vanishing witness.

* `IsInducedTorus Z` (KP Definition 2.5.1, in
  `Langlands.GroupScheme.Torus.Induced`) gives a finite Galois extension `E/k`.
  The base change `Z_E` is a split torus, and the character lattice of `Z_E`
  has a `ℤ`-basis permuted by `Gal(E/k)`.
* `IsClosedSubgroup i` says that the underlying morphism of `i` is a closed
  immersion.
* `IsCentral i` says that on every test scheme, the points of `Z` map into the
  centre of `H`.
* `IsConnectedReductive H` and `IsConnectedReductive G` say that each group is
  smooth, affine and connected over `k`, with trivial geometric unipotent
  radical.
* `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p` says that the
  underlying scheme morphism of `p` is flat, surjective and locally of finite
  presentation. It also says that the subgroup functor cut out by the actual
  scheme kernel of `p` equals the image of `i` on every test scheme over `k`,
  nonreduced tests included. So `1 → Z → H → G → 1` is exact as a sequence of
  fppf sheaves.
* `H.affinePointsTarget p (CommAlgCat.of k K)` is the actual homomorphism
  `H(K) → G(K)` given by postcomposition with `p`. Here a `K`-point is a
  morphism over `Spec k` from `Spec K` into the group scheme.

There is no restriction on `k` or `K`. The field `k` may have any
characteristic and need not be perfect. The extension `K/k` need not be
algebraic, separable or finite. The case `K = k` gives rational points of `k`.

### No separate torus hypothesis

The statement has no separate hypothesis that `Z` is a torus. The theorem
`IsInducedTorus.isTorus` proves `IsInducedTorus T → IsTorus T.toGrp`. Its
proof takes the splitting field `E` packaged in `IsInducedTorus` as the field
that `IsTorus` requires. So the induced-torus condition already contains the
geometric torus condition, and the scope is not narrowed.

## Why fppf surjectivity is not point surjectivity

The quotient predicate says that `p` is surjective as a morphism of schemes
and as a map of fppf sheaves. It does not say that `H(K) → G(K)` is surjective
for a field `K`, and this generally fails:

* The squaring map `Gm → Gm` over `ℚ` is flat, surjective and of finite
  presentation, with kernel `μ₂`. On `ℚ`-points it is `x ↦ x²`, and `2` is
  not a square in `ℚ`.
* The quotient `SL₂ → PGL₂` over `ℝ` has kernel `μ₂`. The class of
  `diag(-1, 1)` in `PGL₂(ℝ)` is not the image of any element of `SL₂(ℝ)`,
  since every lift has determinant `-1` times a square.
* The kernel being a torus is not enough. The norm map
  `R_{ℂ/ℝ} Gm → Gm` is an fppf quotient of connected reductive groups. Its
  kernel is the central, non-induced norm-one torus `R¹_{ℂ/ℝ} Gm`. On
  `ℝ`-points it is `z ↦ |z|²` from `ℂ^×` to `ℝ^×`, which misses `-1`.

So the proposition really needs a property of the kernel: it must be an
*induced* torus. The cohomological reason is explained below.

## Provenance

The provenance is **derived**: no single source states this proposition in
this generality.

The motivating source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The
printed page number is the PDF page number minus 31. In §11.5, printed
p. 429 (PDF p. 460), the source chooses a z-extension `1 → Z → G̃ → G → 1` of
a connected reductive group over the maximal unramified extension `K`
(written `k̆` elsewhere). It then writes: "The maps G̃(K)→ G(K) and
π1(G̃)→ π1(G) are surjective." The proof of Lemma 11.5.1, printed p. 430
(PDF p. 461), uses the exact row `1 → Z(K) → G̃(K) → G(K) → 1`. The source
states the point surjectivity only for that field and gives no proof. Its
1 November 2024 corrections contain no entry for §§11.4–11.5.

The present proposition extends this to an arbitrary base field `k` and an
arbitrary field extension `K/k`. It is the standard consequence of the torsor
interpretation of `H¹`, Shapiro's lemma and Hilbert's Theorem 90:

* KP §2.5(a), printed p. 86 (PDF p. 117), after Definition 2.5.1: `R_{E/F} Gm`
  is induced for every finite separable `E/F`, and "A general induced torus is
  a product of tori of this form". The proof of Lemma 2.5.4, printed p. 87
  (PDF p. 118), uses Shapiro's lemma and Hilbert's Theorem 90 to get
  `H¹(E, Gm) = 1`.
* Platonov–Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered
  as `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA256
  `c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`. Here
  the printed page number is the PDF page number minus 10. The long exact
  sequence (2.7), printed p. 72 (PDF p. 82), shows that for an exact sequence
  `1 → F → G → H → 1` the image of `G_K → H_K` is the kernel of the
  coboundary to `H¹(K, F)`. Lemma 2.4, printed p. 73 (PDF p. 83), states:
  "Let T be a quasisplit K-torus. Then H¹(K,T) = 1." It is proved there from
  Hilbert 90 and Shapiro's lemma.
* Milne, *Étale Cohomology* (1980), registered as
  `milne-1980-etale-cohomology`, SHA256
  `0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`. Here
  the printed page number is the PDF page number minus 14. Chapter III, §4,
  printed p. 120 (PDF p. 134), defines torsors and notes that torsors under a
  smooth group are étale-locally trivial. Theorem III.3.9, printed p. 114
  (PDF p. 128), identifies flat and étale `H¹` for smooth quasi-projective
  commutative group schemes. Proposition III.4.9 (Hilbert's Theorem 90),
  printed p. 124 (PDF p. 138), gives `H¹(X_fl, Gm) ≅ Pic(X)`.

The source arguments work with Galois cohomology over a separable closure.
The Library hypothesis, by contrast, is the fppf exactness predicate with the
kernel taken on all test schemes. The torsor argument below bridges the two.

## Intended proof (an obligation, not proved here)

Fix `g ∈ G(K)`, that is, `g : Spec K → G` over `k`.

1. Let `P = Spec K ×_G H` be the fibre of `p` over `g`. Since `p` is flat,
   surjective and locally of finite presentation, `P → Spec K` is an fppf
   cover.
2. The closed immersion `i` is a monomorphism. Since its image is the actual
   kernel of `p` on every test, `Z` is identified with `ker p`. The map
   `(h, h') ↦ (h, h⁻¹h')` then identifies `H ×_G H` with `H ×_k Z`, and hence
   `P ×_K P` with `P ×_K Z_K`. So `P` is a torsor under `Z_K` for the fppf
   topology.
3. By the Library decomposition `inducedTorusWeilDecomposition`, `Z` is
   isomorphic to `R_{A/k} Gm` for a finite product `A` of finite separable
   field extensions of `k`. Hence `Z_K` is isomorphic to `R_{A_K/K} Gm`, where
   `A_K = A ⊗_k K` is a finite étale `K`-algebra.
4. The torsor `P` gives a class in `H¹_fl(K, Z_K)`. This group vanishes by
   Shapiro's lemma and Hilbert 90: it equals `Pic(A_K)`, which is trivial
   because `A_K` is a finite product of fields. Equivalently, after passing
   to étale or Galois cohomology for the smooth group `Z_K`, it equals the
   product of the groups `H¹(L, Gm) = 1` over the factor fields `L` of `A_K`.
5. So `P` is a trivial torsor and has a `K`-point. Its image in `H` is an
   `h ∈ H(K)` with `p ∘ h = g`.

This argument does not use centrality, the reductivity of `H` or `G`, or any
property of `k` or `K`. Closedness is used only to identify `Z` with the
kernel. The unused hypotheses are kept because they describe the requested
setting and the z-extension use. A proof may ignore them.

## The z-extension specialization

`zExtensionPointSurjectivity_of_inducedTorusQuotient` proves

```text
InducedTorusQuotientPointSurjectivityStatement.{u} →
  ZExtensionPointSurjectivityStatement.{u}.
```

It applies the general statement to `z.Z`, `z.H`, `G`, `z.i` and `z.p`, using
the fields `induced`, `closed`, `central`, `source_reductive`,
`target_reductive` and `quotient` of `z.isZExtension`. The remaining field,
`derived_simplyConnected`, is not needed. With `k` the local field and `K` its
maximal unramified extension, this gives the surjectivity asserted in KP §11.5.
That surjectivity is the uniqueness input in the proof of Lemma 11.5.1.

The helper `IsInducedTorus.isTorus` is imported from `Langlands.GroupScheme.Torus.Induced`.
