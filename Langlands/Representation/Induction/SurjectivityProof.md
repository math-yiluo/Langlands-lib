# Surjectivity of smooth induction from a closed subgroup

Worker 440 proves the published proposition
`Langlands.Induction.SmoothInductionSurjectivityStatement.{uG,uV,uW}` as
`Langlands.Induction.smoothInductionSurjectivity`.
The statement and every imported Lean/Markdown pair are unchanged.

## Exact scope

The theorem retains the statement's complete telescope: independently quantified
`G : Type uG`, `V : Type uV`, and `W : Type uW`; a Hausdorff topological group
`G`; compact open subgroups cofinal among open subgroups; a closed subgroup
`P`; smooth complex representations `sigma` and `tau` of `P`; and an actual
surjective intertwiner `q : sigma.IntertwiningMap tau`. Its conclusion is
surjectivity of the existing `smoothInducedMap P q`.

The representations have no topology on their coefficient spaces. Induction is
ordinary unnormalized induction, with covariance `f(p*x) = sigma(p)(f(x))` and
right translation `(g*f)(x) = f(x*g)`. There is no compactness assumption on
`P \ G`, no finite double-coset cover, and no finite-dimensionality,
admissibility, or finite-length assumption. No lift or section is supplied as
an extra premise. The Hausdorff assumption remains in the exact target, though
the argument below does not use it. The theorem proves only surjectivity of
smooth induction; the other exactness clauses and compact-induction results
remain outside its scope.

## Implemented proof

Let `f : SmoothFunctions P tau` be arbitrary. Its smoothness supplies one open
right stabilizer `U` for the entire function. Cofinality supplies a compact
open `K` contained in `U`, so `f` is fixed by `K`.

The helper `isCompact_conjOpenSubgroup` proves that
`conjOpenSubgroup P K x`, the subgroup of `P` with
`x⁻¹ * p * x ∈ K`, is compact in the subspace topology for every `x : G`.
Indeed its underlying set is the preimage under `P → G` of the compact image
of `K` under `k ↦ x*k*x⁻¹`. The inclusion `P → G` is a closed embedding
because `P` is closed, and the preimage of a compact set under a closed
embedding is compact. The set equality is established in Lean in both
directions. The helper requires only a topological group and the explicit
closedness and compactness hypotheses.

The published `eval_mem_fixedVectors` puts `f(x)` in the fixed vectors of
`tau` under this compact open subgroup of `P`. Apply the published
`Compact.fixedVectorSurjectivity` to the group `P`, the two smooth
representations, and `q`. This produces a vector `v(x)` fixed by
`conjOpenSubgroup P K x` with `q(v(x)) = f(x)`. Classical choice selects
such vectors; none is an input assumption.

For each element `d` of Mathlib's `DoubleCoset.Quotient P K`, choose its
representative `d.out`. The published `compactDoubleCosetSection` at
`d.out` and `v(d.out)` supplies a covariant, right-`K`-invariant section
`s_d`, whose value at `p*d.out*k` is `sigma(p)(v(d.out))`. Its underlying
`SmoothFunctions` value is all this proof needs. The single-double-coset
constructor and its factorization-independence argument are reused directly.

Define the global function by

```text
F(x) = s_[x](x),   where [x] is the double coset P*x*K.
```

Mathlib's `DoubleCoset.mk_mem_mul` gives `[p*x] = [x]`, so the covariance
of `s_[x]` proves `F(p*x) = sigma(p)(F(x))`. Likewise,
`DoubleCoset.mk_mul_mem` gives `[x*k] = [x]`, and
`compactDoubleCosetSection_mul` proves `F(x*k) = F(x)` for the same
subgroup `K` at every point. The existing `smoothFunctionOf` therefore
bundles `F` as an element of `SmoothFunctions P sigma`.
This construction uses arbitrary many double cosets and no infinite sum.

Finally, `DoubleCoset.out_eq'` and `DoubleCoset.eq` express each
`x` as `p*d.out*k`, where `d = [x]`. The published section-evaluation law
identifies `F(x)` with `sigma(p)(v(d.out))`. Intertwining and the chosen
lifting identity give

```text
q(F(x)) = tau(p)(f(d.out)) = f(p*d.out*k) = f(x).
```

The second equality follows from covariance and right-`K`-invariance of
`f`. Subtype extensionality and function extensionality turn these pointwise
identities into equality under the actual `smoothInducedMap P q`.
Representative independence is enforced by the genuine quotient identities
and by the published section's evaluation law, rather than assumed.

## Provenance and dependencies

This is an internal derived proof from the published modules
`Induction.SurjectivityStatement`, `Induction.CompactLocalSection`, and
`Compact.SurjectivityProof`, together with Mathlib's `GroupTheory.DoubleCoset`.
The evaluation and conjugate-stabilizer API comes transitively from the
published `Induction.CompactQuotientProof`. Only the single-double-coset
constructor is used; the stronger hypotheses of `compactLocalSection` are
not imposed. The project import closure consists of 18 modules including
this proof, covering smooth representations, induction, compact averaging,
scalar twists, representation categories, and compact open neighborhoods.
It has no classification or uniqueness proof dependency.

The target's external provenance is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472: §1.1 (printed page 442 / PDF page 3), §1.2 (443 / 4),
§1.8(a) (444 / 5), the ordinary-induction remark and Proposition 1.9(a)
(445 / 6). These passages were read in the registered original
`bernstein-zelevinsky-1977-induced-i`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
No project errata note for this source was present when checked.

For correspondence, specialize the source's §1.8 to the trivial subgroup
`U`, trivial character, and `M = P`. The modulus and character factors
become one, leaving exactly the covariance and common right stabilizer used
here. Proposition 1.9(a) states exactness; this proof establishes its
smooth-surjectivity consequence under the target's weaker compact-open
cofinality condition. The source assumes an l-group, which implies this
cofinality by applying its identity-neighborhood condition to each open
subgroup. The implemented proof is the compact fixed-vector argument
explained above; it does not transcribe the proof referred to in the source.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`), the module
compiled with no errors or warnings. A Lake-build declaration inspection
reported the theorem's three independent universe parameters `uG`, `uV`,
`uW`, with only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
These are development checks. Exact-target acceptance, independent semantic
review, and Library publication are separate requirements.
