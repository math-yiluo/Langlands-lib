# Smooth induction across a continuous split quotient

Worker 438 adapts Worker 777's published compact split-quotient construction to
actual smooth induction, and proves equivariance for the full ambient group
after inflation along the retraction. The entry construction is
`Langlands.Induction.smoothSplitQuotientEquiv`.

Let `r : G →* L` and `s : L →* G` be continuous homomorphisms of topological
groups with `r (s l) = l`. Let `H ≤ G` contain `ker r`, and let `σ` be an
`R`-linear representation of `H` on which each `h` with `r h = 1` acts
trivially. The construction identifies actual smooth induction from `H` to
`G` with the inflation along `r` of actual smooth induction from `H.comap s`
to `L`, with coefficients `σ.comp (s.subgroupComap H)`. The coefficient ring
is any commutative ring; the group, quotient, coefficient ring and both modules
in the naturality law have independent universes. Closedness, local compactness
and coefficient smoothness are unnecessary.

The forward function is `f ↦ f ∘ s`, constructed as
`smoothSplitQuotientRestrict` with the preimage under `s` of a uniform open
stabilizer of `f`. The inverse is `k ↦ k ∘ r`, constructed as
`smoothSplitQuotientExtend` with the preimage under `r` of a uniform open
stabilizer of `k`. Covariance for the inverse uses the published
`splitQuotientRetract` and `splitQuotient_action_retract`. Kernel triviality
and `splitQuotient_apply_section` give `f (s (r g)) = f g`, proving one
inverse law; the other uses `r (s l) = l`.

For full `G`-equivariance, the same identity at `s l * g` identifies
`f (s l * g)` with `f (s (l * r g))`. Thus the source right translation by `g`
corresponds to target right translation by `r g`. The two evaluation lemmas
record the formulas, and naturality is the pointwise equality
`T(f(s l)) = (T ∘ f)(s l)`.

This is an internal smooth-function and inflation variant of the published
`Langlands.Representation.Induction.SplitQuotientProof`, with its group-theoretic
lemmas imported directly. The source context is the ordinary-induction case
of Bernstein–Zelevinsky 1977, sections 1.8 and 1.9(c), printed pp.444–445,
registered source `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The explicit arbitrary-ring split-quotient formulation is internal, rather than
a separately numbered assertion there. It uses no geometric lemma,
classification, character independence, adjointness or cuspidal-support result.
The normalized standard-parabolic and exact Aubert comparisons remain further
obligations.
