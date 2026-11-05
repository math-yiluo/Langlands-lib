# Étale maps on rational points over henselian valued fields

`HenselianEtalePointStatement` states two assertions from Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), printed p.14. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad defines: "a valued field is a field `k` equipped with a nontrivial absolute
value, and it is henselian if this absolute value uniquely extends to every
algebraic extension". He then says that "a characterization of the henselian
property is that `k` is separably algebraically closed in `k̂`". Lemma 5.3 reads:
"Let `k` be a henselian valued field. For any étale map `Y' → Y` between locally
finite type `k`-schemes, the natural map `Y'(k) → Y(k)` is a local
homeomorphism."

## Henselian valued fields

`IsHenselianValuedField K` is a predicate on a nontrivially normed field `K`. The
norm of a Mathlib normed field is an absolute value: it is multiplicative, it
vanishes only at `0`, and it satisfies the triangle inequality. A nontrivially
normed field has an element of norm greater than `1`, so this absolute value is
nontrivial. The predicate says that for every field `L` that is an algebraic
extension of `K`, there is exactly one `v : AbsoluteValue L ℝ` with
`v (algebraMap K L x) = ‖x‖` for all `x : K`. Mathlib's `AbsoluteValue L ℝ` is
multiplicative, vanishes only at `0` and satisfies the triangle inequality, so
the extensions are absolute values of the same kind as the norm on `K`.

The extension `L` ranges over fields in the universe of `K`. This does not
weaken the condition. An algebraic extension of `K` has cardinality at most that
of `K` or of `ℕ`, so it is isomorphic over `K` to an extension in the universe of
`K`. Existence and uniqueness of an extended absolute value transfer along such
an isomorphism.

The predicate does not assume the field is non-archimedean, so the archimedean
henselian fields that Conrad discusses on p.14 are included. No completeness is
assumed.

## The two assertions

`HenselianSeparablyClosedInCompletionStatement` says that if `K` is henselian
then `separableClosure K (UniformSpace.Completion K) = ⊥`. The completion carries
Mathlib's `K`-algebra structure, given by the canonical map from `K`. The
equation says that every element of the completion that is separable over `K`
lies in the image of `K`. This is the forward direction of Conrad's
characterization, the one used in the proof of Lemma 5.3.

`HenselianEtalePointLocalHomeomorphStatement` is Lemma 5.3. Let `K` be henselian
and `X, Y` schemes over `Spec K`, both with locally finite type structure
morphisms. Let `f : X ⟶ Y` be a morphism over `Spec K` whose underlying scheme
morphism `f.left` is étale. Then postcomposition with `f` is a local
homeomorphism from `RingPoint K X K` to `RingPoint K Y K`. These carriers are the
actual `K`-points of `X` and `Y`, the morphisms from `Spec K` over `Spec K`. Each
carries the existing `schemePointTopology`, built from `K`'s norm topology. This
is the final topology for the inclusions of the points of all affine open
subschemes, each affine chart having the topology of evaluation on global
sections.

The target `HenselianEtalePointStatement` is the conjunction of these two
assertions in a common universe.

## Scope and provenance

The two assertions are Conrad's. The following material on p.14 is not stated
here:

- the converse of the characterization, that a field separably algebraically
  closed in its completion is henselian;
- the criterion from [Ber, 2.4.3] that in the non-archimedean case `k` is
  henselian exactly when its valuation ring is henselian;
- the decomposition of `k' ⊗_k k̂` into completions of `k'`, the classification
  of archimedean henselian fields, and the equivalence between finite étale
  algebras over `k` and over `k̂`.

Conrad's proof of Lemma 5.3 reduces to the universal monic polynomial and to the
complete case. It then uses the equivalence of finite étale categories to show
that the fibre over a `k`-point consists of `k`-points. These steps are proof
material and are not stated here.

Related Library statements have different hypotheses and conclusions.
`HenselianSmoothRationalPointOpenMapStatement` asserts openness, not local
homeomorphism, for smooth maps of affine schemes over ultrametric fields whose
norm valuation ring is a henselian local ring. `CompleteFieldSmoothPointOpenStatement`
asserts openness for smooth maps over complete fields, with the same
`schemePointTopology` used here.
