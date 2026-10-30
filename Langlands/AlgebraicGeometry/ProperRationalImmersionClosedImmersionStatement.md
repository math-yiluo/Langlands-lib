# Proper morphisms injective on rational points and tangent vectors

This module states, without proof, a closed-immersion criterion. Let `K` be an
algebraically closed field and let `f : X ⟶ Y` be a proper morphism of schemes
that are locally of finite type over `K`. Suppose that `f` is injective on
`K`-points, and that every rational tangent vector of `X` that `f` sends to
zero is itself zero. Then `f` is a closed immersion. The conclusion is about
the whole morphism `f`, and `Y` need not be proper.

The declaration is the Prop-valued definition
`Langlands.AlgebraicGeometry.ProperRationalImmersionClosedImmersionStatement`.
It is a statement only: the module proves nothing, and nothing here asserts that
the proposition has been proved. The formulation is derived from the proof of
Stacks Project Lemma 33.23.1 (Tag 0E8R); see the provenance section.

## The proposition

The universe `u` is arbitrary. The proposition quantifies over the following
data.

- A field `K : Type u` with `[IsAlgClosed K]`. Its characteristic is
  arbitrary.
- Schemes `X Y : Scheme.{u}` with structure morphisms
  `p : X ⟶ Spec (CommRingCat.of K)` and `q : Y ⟶ Spec (CommRingCat.of K)`,
  both with `[LocallyOfFiniteType _]`.
- A morphism `f : X ⟶ Y` with `[IsProper f]`. Mathlib's `IsProper f` means that
  `f` is separated, universally closed and locally of finite type; universal
  closedness includes quasi-compactness.
- The compatibility `f ≫ q = p`, so `f` is a morphism over `Spec K`.

Then the proposition is the implication `(P) → (T) → IsClosedImmersion f`,
where (P) and (T) are the following two hypotheses.

- (P), injectivity on rational points: for all
  `x y : Spec (CommRingCat.of K) ⟶ X` with `Picard.IsRationalPoint p x` and
  `Picard.IsRationalPoint p y`, if `x ≫ f = y ≫ f`, then `x = y`.
- (T), trivial rational tangent kernels: for every
  `x : Spec (CommRingCat.of K) ⟶ X` with `Picard.IsRationalPoint p x` and every
  `t : Spec (CommRingCat.of (DualNumber K)) ⟶ X` with
  `Picard.IsTangentVectorAt p x t`, if
  `t ≫ f = (Picard.dualNumberProjection K ≫ x) ≫ f`, then
  `t = Picard.dualNumberProjection K ≫ x`.

Both hypotheses are required at every rational point of `X`. Neither is a
condition at one chosen point.

The conclusion `IsClosedImmersion f` is Mathlib's class: the underlying map of
topological spaces is a closed embedding, and every stalk map of `f` is
surjective. It concerns the entire morphism `f`. It is not a statement about an
open neighbourhood of a point of `Y` or of `X`, and it is not only a topological
statement. It includes surjectivity of the actual stalk maps of the structure
sheaves. The topological condition does not imply it, even for reduced schemes,
as the cusp example below shows; for non-reduced `X` or `Y` it also controls
the nilpotent structure.

## The rational-point and dual-number formulation

The three predicates come from the imported module
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`, and are used
unchanged.

- `Picard.IsRationalPoint p x` is `x ≫ p = 𝟙 _`. So `x` is a `K`-point of `X`
  over `K`.
- `Picard.dualNumberProjection K : Spec K[ε] ⟶ Spec K` is the spectrum of the
  structure map `K → K[ε]`, where `K[ε]` is Mathlib's `DualNumber K`. Write `π`
  for it.
- `Picard.IsTangentVectorAt p x t` says `t ≫ p = π` and `ι ≫ t = x`, where `ι`
  is `Picard.dualNumberAugmentation K`, the closed point `Spec K ⟶ Spec K[ε]`.
  So `t` is a `K[ε]`-point of `X` over `K` whose closed point is `x`, a rational
  tangent vector at `x`.

The `K[ε]`-point `π ≫ x` is the zero tangent vector at `x`. The imported lemma
`Picard.isTangentVectorAt_dualNumberProjection_comp` shows that it is a tangent
vector at `x`. Because `f ≫ q = p`, the composite `t ≫ f` is a `K[ε]`-point of
`Y` over `K` whose closed point is `x ≫ f`. Similarly, `(π ≫ x) ≫ f` is the
constant `K[ε]`-point at `x ≫ f`, the zero tangent vector there. Hence (T) says
that the map `t ↦ t ≫ f` from tangent vectors at `x` to tangent vectors at
`x ≫ f` sends only the zero vector to zero. These two observations are
informal remarks and are not proved in this module.

The hypothesis `Picard.IsRationalPoint p x` in (T) is implied by
`Picard.IsTangentVectorAt p x t`, by the imported lemma
`Picard.IsTangentVectorAt.isRationalPoint`. It is kept to match the requested
interface. Similarly, `[LocallyOfFiniteType p]` follows from `[IsProper f]`,
`[LocallyOfFiniteType q]` and `f ≫ q = p`, because morphisms locally of finite
type are stable under composition. It is also kept to match the interface. No
other hypothesis is redundant in this way.

The classical criterion is stated with closed points and the tangent spaces
`T_x = Hom_K(m_x/m_x², K)`. The following comparison is informal background
and is not formalized here. Over an algebraically closed `K`, the closed points
of a scheme locally of finite type over `K` are exactly the points with residue
field `K`, by the Nullstellensatz. Each such point is the image of a unique
rational point. The rational tangent vectors at `x` correspond to the
`K`-linear functionals on `m_x/m_x²`, with `π ≫ x` corresponding to zero.
Composition with `f` corresponds to the linear tangent map `T_x X → T_{f(x)} Y`.
Under this dictionary, (P) is injectivity of `f` on closed points, and (T) is
injectivity of each tangent map at a closed point. Equivalently, each cotangent
map `m_{f(x)}/m_{f(x)}² → m_x/m_x²` is surjective.

## Scope

No further hypothesis is imposed. In particular:

- `Y` need not be proper, separated or quasi-compact over `K`.
  `X` need not be proper over `K` either; only `f` is proper.
- `X` and `Y` may be non-reduced, non-smooth, of dimension zero and empty. If
  `X` is empty, (P) and (T) hold vacuously, and so does the conclusion.
- There is no finite, quasi-finite, monomorphism, stalk-surjectivity or
  unramifiedness hypothesis on `f`, and no outer certificate. These properties
  are what the criterion produces, not what it assumes.
- Point injectivity only gives at most one rational point of `X` over each
  rational point of `Y`. The fibre over a closed point outside the image of
  `f` is empty.

The following examples are informal and not formalized. They show why the
remaining hypotheses are needed.

- Properness of `f`: the open immersion of `A¹ ∖ {0}` into `A¹` over `K`
  satisfies (P) and (T), but it is not a closed immersion.
- Hypothesis (P): the morphism `Spec (K × K) ⟶ Spec K` is finite, hence
  proper, and has no nonzero tangent vectors. It is not injective on rational
  points and not a closed immersion.
- Hypothesis (T): the normalization `Spec K[s] ⟶ Spec K[s², s³]` of the cusp is
  finite and bijective on rational points. Its tangent map at the origin is
  zero, and it is not a closed immersion.
- Algebraic closedness: for `K = ℝ`, the morphism `Spec ℂ ⟶ Spec ℝ` is finite.
  `Spec ℂ` has no `ℝ`-points, so (P) and (T) hold vacuously. It is not a closed
  immersion, because `ℝ → ℂ` is not surjective. Without algebraic closedness,
  rational points do not detect all closed points.

Conversely, a closed immersion is a monomorphism of schemes, so it is injective
on all `T`-valued points and satisfies (P) and (T). So (P) and (T) are
necessary for a closed immersion, and the proposition asserts that, for proper
`f`, they are also sufficient.
Mathlib's `IsClosedImmersion.iff_isProper_and_mono`, in
`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` (Stacks Tag 04XV), states
that a morphism is a closed immersion exactly when it is proper and a
monomorphism. So the conclusion is equivalent, for proper `f`, to `f` being a
monomorphism. Hypotheses (P) and (T) only test `K`-points and `K[ε]`-points.

## Expected proof route

The following route is informal and is not formalized in this module. A proof
may follow a different valid route.

1. Over every closed point of `Y`, the fibre of `f` is a proper `K`-scheme with
   at most one closed point, by (P). It is therefore finite, so `f` is
   quasi-finite at every point over a closed point of `Y`. The points where `f`
   is not quasi-finite form a closed set, whose image under the closed map `f`
   is closed. Since `Y` is Jacobson, a nonempty closed subset contains a closed
   point, so this image is empty. Thus `f` is locally quasi-finite and proper,
   hence finite. Mathlib supplies `IsFinite.of_isProper_of_locallyQuasiFinite`
   and, about one point,
   `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`, both in
   `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`.
2. For finite `f`, surjectivity of `O_Y → f_* O_X` can be checked at closed
   points of `Y`, since the support of the cokernel is closed. Over a closed
   point outside the image the stalk of `f_* O_X` is zero.
3. At a closed point `f(x)` of the image, the fibre is `{x}`. So the stalk of
   `f_* O_X` is `O_{X,x}`, a finite `O_{Y,f(x)}`-module. Both residue fields
   are `K`. By (T) the cotangent map is surjective, and Nakayama's lemma gives
   surjectivity of `O_{Y,f(x)} → O_{X,x}`.

This route explains why no properness of `Y` is needed. Every step uses only
the closed points of `Y` and the properness of `f`. A separate statement task
of the same project states a local version of the criterion, near the image of
one rational point. This module does not import or depend on it.

## Provenance

The formulation is derived (internal) provenance. It is not a verbatim theorem
of the source. The source is the registered original
`stacks-very-ampleness-support-2026-10-29`, the Stacks Project bundle "coherent
proper cohomology, maps into Proj, and separation of points and tangent
vectors". It was read in the retained official HTML snapshot `0E8R.html` of
2026-10-29 (SHA-256
`9f71521de6ebf4e26b87567ff9ea8238b956ba43aad013ffd52817c9b8a3acbf`), Section
33.23, "Separating points and tangent vectors", Lemma 33.23.1 and its proof.

Lemma 33.23.1 assumes that `k` is algebraically closed, `X` is a proper
`k`-scheme, and `V ⊂ H⁰(X, L)` separates points (1) and tangent vectors (2).
It concludes that `φ_{L,V} : X → P(V)` is a closed immersion. Its proof first
observes that `φ` is proper and injective on closed points. It then shows that
`φ` is finite, and finishes on stalks at closed points. There it uses the
equality of residue fields with `k`, injectivity of the tangent maps
`T_{X/k,x} → T_{P(V)/k,p}` from (2), the equivalent surjectivity of
`m_p/m_p² → m_x/m_x²`, and a Nakayama-type lemma.

This module isolates the general fact behind the second half of that proof.
The source's particular map `φ` into the projective space `P(V)` is replaced by
an arbitrary proper morphism `f` to an arbitrary scheme `Y` locally of finite
type over `K`. Conditions (1) and (2) on sections are replaced by the conditions
on `f` that the source derives from them: injectivity on closed points, here
(P), and injectivity of tangent maps, here (T). Closed points and tangent
vectors are expressed through `K`-points and `K[ε]`-points, as explained above.
The source assumes `X` proper over `k`; here only `f` is proper.

The source's README records a caveat. The proof says that the fibre of `φ` over
every closed point is a singleton. That is true only over closed points of the
image; outside the image the fibre is empty. This statement assumes only
injectivity (P), that is, at most one rational point in each fibre, and the
proof route above treats closed points outside the image separately. The
README's other caveat concerns base-point freeness of the linear system `V`.
It does not affect this statement, which has no linear system.

The section page has two comments. Comment #7149 (Manolis C. Tsakiris, 28 March
2022) reports the misprint "there exist" in condition (2), and comment #7299
(Johan, 4 May 2022) says it is fixed. The snapshot reads "there exists". The
misprint does not affect the mathematics.

The source's proof also cites Cohomology of Schemes Lemma 30.21.2, Varieties
Lemma 33.16.5 and Algebra Lemma 10.20.3. These are named only to describe the
source; they were not consulted for this statement. The Mathlib results named
above are cited for orientation and are not imported.
