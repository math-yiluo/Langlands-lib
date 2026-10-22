# Generator-form Frobenius reciprocity

Worker 174 proves the existing proposition
`Langlands.Weil.RepresentationInductionReciprocity` by the closing theorem
`Langlands.Weil.representationInductionReciprocity`. The only project import is
`Langlands.Weil.Representation.RestrictionInduction`; its statement pair and
imports are unchanged.

The theorem quantifies over an arbitrary group `G`, subgroup `H`, complex
modules `V` and `U`, representations `ρ` of `H` and `σ` of `G`, and an
intertwiner `f : ρ.IntertwiningMap (σ.comp H.subtype)`. It constructs the unique
actual intertwiner from `ρ.ind H.subtype` to `σ` whose value at
`Representation.IndV.mk H.subtype ρ 1 v` is exactly `f v`. The universes
`uG`, `uV`, and `uU` are independent. There are no finite-index,
finite-dimensionality, topology, continuity, or semisimplicity assumptions.

## Implemented proof

Write `[h ⊗ v]` for `IndV.mk H.subtype ρ h v`. The private construction
`inductionExtension` first defines a linear map on `ℂ[G] ⊗[ℂ] V` by

`[h ⊗ v] ↦ σ(h⁻¹)(f(v))`.

More precisely, `Finsupp.lift` extends the family of linear maps
`v ↦ σ(h⁻¹)(f(v))` across the group algebra, using
`MonoidAlgebra.coeffLinearEquiv`, and `TensorProduct.lift` produces the
linear map on the tensor product. The diagonal action of `a ∈ H` sends a
tensor generator to `(a*h) ⊗ ρ(a)(v)`. Its image under this map is

`σ(h⁻¹) σ(a⁻¹) f(ρ(a)(v)) = σ(h⁻¹) σ(a⁻¹) σ(a) f(v) = σ(h⁻¹) f(v)`.

Here `a` in the target action denotes its image under `H.subtype`.
The first equality uses the intertwining equation for `f`. This invariance
is proved on generators by linear extensionality and supplied to
`Representation.Coinvariants.lift`, which descends to Mathlib's actual
induced carrier. No alternative induction object is introduced.

The resulting map intertwines the `G` actions: Mathlib sends `[h ⊗ v]`
under `g` to `[h*g⁻¹ ⊗ v]`, whose image is
`σ(g*h⁻¹)(f(v)) = σ(g)(σ(h⁻¹)(f(v)))`. Linear extensionality and
simplification prove this in the intertwiner structure. The private lemma
`inductionExtension_mk` records the generator formula. Taking `h = 1`
gives exactly the required generator equality.

For uniqueness, `IntertwiningMap.ext` and `IndV.hom_ext` reduce equality to
all generators `[h ⊗ v]`. Such a generator is the translate by `h⁻¹` of
`[1 ⊗ v]`. Equivariance of any competing `F` therefore forces
`F([h ⊗ v]) = σ(h⁻¹)(F([1 ⊗ v])) = σ(h⁻¹)(f(v))`, the constructed value.
The closing `example` assigns the entire unapplied theorem constant to
`RepresentationInductionReciprocity.{uG,uV,uU}`.

## Provenance and scope

The quotient-lift expression and its two generator calculations adapt
Amelia Livingston's `Rep.indResHomEquiv` in Mathlib's
`Mathlib/RepresentationTheory/Induced.lean`, lines 132–154. Its bundled
`Rep` arguments use a common universe `max w v' u`. This proof writes its
low-level construction directly for unbundled representations so that the
source and target carriers retain their independent universes. The
uniqueness argument uses `Representation.IndV.hom_ext` and
`Representation.ind_mk` from the same file, lines 69–88. The adaptation
retains the upstream copyright and Apache-2.0 notice in the Lean file;
Worker 174 supplied the independent-universe adaptation, exact-target
closing theorem, and this explanation.

Source ID: `mathlib-induced-5ed296525643`.
Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.
Source file SHA-256:
`f462f392700d339611a2fb1480192d0a870efa20c06d248a96122b90fc6a79b2`.
[Upstream source at the pinned commit](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/RepresentationTheory/Induced.lean).

This is a proof of the already published algebraic reciprocity target.
It makes no claim about a right adjunction, the other finite-index
induction targets, a local extension aggregate, or a Langlands correspondence.
