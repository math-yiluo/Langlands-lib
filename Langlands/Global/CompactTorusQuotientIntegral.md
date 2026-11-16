# A compact torus criterion for fundamental-domain integrals

This internal measure-theoretic criterion combines the Library's
diagonal–unipotent coordinate shifts with right-invariant compact
neighborhoods and subgroup slices of an exact transversal.

Let `G` be a topological group with its Borel measurable structure and let
`M`, `U` be subgroups such that `M` normalizes `U`. Write `dm`, `du` for
measures on these subgroups and let
`δ : M →* ℝ≥0ˣ` satisfy `IsConjModulus`: conjugation by `m` pushes `du`
forward to `δ(m)⁻¹ du`. The predicate `HasCompactTorusBound dm δ f` says
that for every compact `C ⊆ G` there is a finite `B` such that

`∫_M δ(m)⁻¹ f(m c) dm ≤ B`

for every `c ∈ C`. Values and integrals lie in the extended nonnegative
reals. The predicate imposes no measurability or invariance condition;
those are separate premises of the result that uses it.

Suppose `Γ ≤ U` and a measurable set `s ⊆ G` is a strict transversal:
for every `g` there is exactly one `γ ∈ Γ` with `γ g ∈ s`. The acting
subgroup of `U` is `Γ.comap U.subtype`; it is assumed countable. Suppose
`t ⊆ U` is a fundamental domain for this subgroup with respect to the
left-invariant measure `du`, and `du(t) < ∞`. If `f : G → ℝ≥0∞` is
measurable and left `U` invariant, the first theorem proves

`∫_(M × U) 1_s(m u c) f(m u c) d(dm × du)
 = du(t) ∫_M δ(m)⁻¹ f(m c) dm`.

Here both subgroup measures are s-finite, and ambient multiplication is
jointly measurable. No positivity or normalization
of `du(t)` is assumed. Tonelli writes the product integral as iterated
integrals. Conjugation changes `m u` into `u m` and contributes `δ(m)⁻¹`.
The subgroup-slice indicator identity evaluates the resulting `U`
integral as `du(t) f(m c)`. Since `du(t)` is finite, it can be pulled
outside the remaining lower integral without a separate measurability
condition on `δ`.

For the finiteness theorem, assume additionally that `G` is Hausdorff,
locally compact and second countable, and has a Borel s-finite
left-invariant measure `dg` finite on compact sets. Both `dm` and `du`
are s-finite, left invariant and positive on nonempty open sets. Suppose
`K` is a compact subgroup and `G = M U K`, with the factorization stated
as a pointwise existence premise. Then `HasCompactTorusBound dm δ f`
implies

`∫_s f(g) dg < ∞`.

The proof chooses a compact identity neighborhood `C` invariant under
right multiplication by `K`. The continuous map `(m,u) ↦ (m u)⁻¹`
pulls `C` back to a neighborhood of `(1,1)`, whose product measure is
positive. Left multiplication in `m u` coordinates is represented by
the existing measure-preserving skew-product shifts. The
right-invariant-set factorization criterion therefore applies to
`1_s f`. The first theorem bounds its parameter integrals on `C` by
`du(t) B`, which is finite.

This is a derived internal result, with no external-source attribution.
It does not construct an adelic diagonal subgroup, compute an adelic
conjugation modulus, identify a particular quotient measure or prove
the Whittaker–Schwartz estimate. Those remain separate applications.
