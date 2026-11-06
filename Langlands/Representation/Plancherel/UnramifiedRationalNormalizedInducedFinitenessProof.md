# Flatness and fixed-space finiteness of actual universal normalized induction

Workers 1754 and 1582.

`universalInducedCoefficientFiniteness.{u, uV}` proves exactly the published
proposition `UniversalInducedCoefficientFinitenessStatement.{u, uV}` from
[`UnramifiedRationalNormalizedInducedFiniteness`](UnramifiedRationalNormalizedInducedFiniteness.md).
It proves flatness of the full universal normalized induced module over
`RegularAlgebra r` and finite projectivity over that same algebra of each
compact-open fixed module of its actual right-translation action. The
intermediate fixed-space lemmas establish the stronger conclusion of finite
freeness for this universal family.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passage, printed pp.187–191 / PDF pp.193–197, was read in full.
The VI.8.1 Proposition and Remark on pp.187–188 relate flat admissible
coefficient modules to finite projectivity of compact-open fixed modules.
The universal unramified tensor example on p.189 identifies its compact
fixed spaces by scalar extension. VI.8.2, especially (VI.8.2.1) on
pp.189–190, describes induced fixed spaces using a finite double-coset
transversal. These are the source ingredients implemented here.

**The actual coefficient algebra and action.** For a norm family `ν`, write
`B = unramifiedRegularFunctions ν` and
`eν(m) = unramifiedEvaluationRegular ν m`. In the final application,
`ν = parabolicLeviRationalNormCharacters r` and `B = RegularAlgebra r`.
The index ranges over every rational character of the supplied actual
Levi scheme; the proof makes no finite selection of norms.

For the supplied semidirect decomposition `h` of the actual parabolic
subgroup into its Levi and unipotent subgroups, write `m = h.projection`
and let `c(q)` be the complex value of
`HaarModulus.closedHalfCharacter U hU P h.le_normalizer q`.
The universal inducing action `τ` on `B ⊗[ℂ] E` is exactly

```
τ(q)(b ⊗ v) = algebraMap ℂ B (c(q)) •
               ((eν(m(q)) * b) ⊗ π(m(q)) v).
```

Thus the positive half-modulus is taken on the full parabolic. The carrier
`UnramifiedNormalized.UniversalInduced ν h hU π.representation` is the
published space of covariant functions with a uniform open right
stabilizer. Its covariance is `f(q * x) = τ(q)(f(x))`; its group action
sends `f(x)` to `f(x * g)`. The `B`-module structure acts pointwise on
function values and comes from the existing submodule structure. The
local additive-group and module instances in this file expose these
existing structures.

**`tensorFixedEquiv`.** This algebraic helper works for a field `k`, a
commutative `k`-algebra `B`, a representation `ρ` of any group on a
`k`-vector space `E`, and a subgroup `Q`. Its second representation `τ`
on `B ⊗[k] E` must satisfy the explicit hypothesis
`τ(q) = (ρ(q)).baseChange B` for every `q : Q`. It constructs the
`B`-linear equivalence

```
B ⊗[k] fixedVectors ρ Q ≃ₗ[B] fixedVectors τ Q.
```

The map is the scalar extension of the inclusion of fixed vectors,
restricted to the fixed submodule in the codomain. Tensor induction
proves that this restriction is well defined. Its injectivity follows
because tensoring an injective linear map over a field preserves
injectivity. For surjectivity, choose a `k`-basis of `B` and express the
given invariant tensor as a finitely supported family of coordinates in
`E`. The private lemma `tensor_coordinates_baseChange`, proved by tensor
induction, identifies the coordinates after applying a scalar-extended
linear map. Consequently each coordinate is `ρ(Q)`-invariant. The finite
sum of basis tensors with those invariant coordinates gives a preimage.
This proof imposes no finiteness condition on the basis, `E`, or `Q`.
It is an internal algebraic proof of the scalar-extension step used in
Renard's universal example.

**`flat_of_smooth_fixed_flat`.** For a commutative ring `R` and a locally
compact nonarchimedean group, this helper proves flatness of a smooth
`R`-linear representation from flatness of all its compact-open fixed
modules. It implements the sufficient direction of the VI.8.1 Remark
using Mathlib's finite-relation criterion for flatness.

For a relation `∑ i, a i • x i = 0` involving finitely many vectors,
smoothness supplies an open fixing subgroup for each vector. Intersect
these finitely many subgroups and use `compactOpenSubgroupBasis` to
choose a compact open subgroup `K` inside their intersection. The entire
relation therefore lies in `fixedVectors ρ K.toSubgroup`. Flatness of
this submodule provides a trivial-relation presentation there; its
inclusion into the original module supplies the required presentation
of the original relation. The proof uses only this sufficient direction
and requires no Noetherian hypothesis on `R`.

**`universalInducing_fixed_finite_free`.** The generic representation
theory in this part uses a locally compact nonarchimedean group `G`,
subgroups `P`, `M`, `U`, a continuous family `ν`, the supplied
semidirect decomposition `h`, closedness `hU` of `U`, continuity `hr` of
`h.projection`, and an admissible smooth complex representation `π` of
`M`. For every compact open subgroup `Q` of `P`, this theorem proves
both `Module.Finite B` and `Module.Free B` for the literal
`fixedVectors` of the universal inducing action on `Q`.

First take the normalized complex inducing representation
`ρ = Aubert.General.inducingRepresentation h hU π`; its action is
`ρ(q)(v) = c(q) • π(m(q)) v`. The imported theorem
`Aubert.General.inducingRepresentation_isAdmissible h hU hr π hπ`
proves that its `Q`-fixed complex vector space is finite dimensional.
This input is a proved consequence of admissibility of `π`.

For each unramified character `χ`, the imported
`Induction.compactSubgroup_le_unramifiedPullback_ker` shows
`χ(m(q)) = 1` on `Q`: each continuous positive norm is trivial on a
compact subgroup, so its image lies in the full common norm kernel.
Extensionality as functions of `χ` then gives `eν(m(q)) = 1` in the
actual algebra `B`. On `Q` the displayed universal inducing action is
therefore exactly `(ρ(q)).baseChange B`. The tensor balancing identity
moves the complex half-modulus scalar between the tensor factors; the
normalization remains part of `ρ`.

Apply `tensorFixedEquiv` to obtain the `B`-linear equivalence from
`B ⊗[ℂ] fixedVectors ρ Q.toSubgroup` to the actual universal inducing
fixed module. A finite-dimensional complex vector space is finite free,
and its scalar extension is finite free over `B`. Transport across the
equivalence proves both conclusions. This is the universal tensor
example of VI.8.1 with the normalized inflated parabolic action retained.
Renard orders the factors as `E ⊗[ℂ] B`; the Library uses `B ⊗[ℂ] E`.

**`universalInduced_fixed_finite_free`.** Suppose additionally that `P` is
closed and that the literal quotient `Induction.LeftQuotient P` is
compact. For a compact open ambient subgroup `K`, set
`Qx = Induction.conjOpenSubgroup P K x`. It is the open subgroup of
`P` consisting of `q` with `x⁻¹ * q * x ∈ K`, namely
`P ∩ x K x⁻¹` in subgroup coordinates. The imported
`Induction.isCompact_conjOpenSubgroup` uses closedness of `P` and
compactness of `K` to prove compactness of `Qx`. The preceding theorem
therefore proves that each coefficient fixed module at `Qx` is finite
free over `B`.

The private helper `smoothInduced_fixed_finite_free` applies the
published finite evaluation construction over a general commutative
coefficient ring. `Induction.exists_finset_doubleCoset_representatives`
derives a finite transversal `t` from compactness of the actual
`P \ G`. `Induction.fixedEvaluationEquiv` then identifies the fixed
submodule of the full smooth induced representation with

```
(i : t) → fixedVectors τ (Induction.conjOpenSubgroup P K i).toSubgroup.
```

The forward map evaluates the actual induced function at each
representative. The inverse in the imported construction is the finite
sum of covariant compact double-coset sections with the prescribed
values. Covariance and right `K`-invariance determine every value from
these evaluations. Thus this is an equivalence for the full function
carrier. A finite product of finite free modules is finite free, and
the helper transports finite generation and freeness back through the
equivalence.

This implements the finite double-coset mechanism of (VI.8.2.1).
Renard writes a finite direct sum of invariants under the projected
Levi stabilizers. Here the finite product is equivalent to a finite
direct sum, and the implemented factors are fixed vectors under the
literal parabolic stabilizers for the already normalized action `τ`.
The proof applies directly to those factors and does not require a
separate identification with invariants under projected Levi subgroups.
The transversal and evaluation equivalence are proved constructions
applied in the proof.

**`universalInduced_flat`.** The published full induced action is smooth
by `UnramifiedNormalized.isSmooth_universalInducedRepresentation`.
The preceding theorem makes each compact-open fixed module free over
`B`, hence flat. Applying `flat_of_smooth_fixed_flat` proves flatness
of the actual full `UniversalInduced` carrier over `B`. This follows
the fixed-space route to induction flatness in VI.8.2.

**The rational-point theorem and its binders.** The final theorem
introduces exactly the binders of
`UniversalInducedCoefficientFinitenessStatement.{u, uV}`.
Connected reductivity of the ambient group scheme gives ambient
affineness. The proof installs the canonical rational-point topology.
Compatibility of `r` gives
`r.isCompatible.parabolic.isClosedSubgroup`, hence the closed immersion
underlying `p`. That immersion is monic, so its range subgroup functor
is represented by `p`. The local-field hypothesis supplies `T2Space F`;
`isClosed_rationalPoint_subgroup` then proves closedness of the literal
subgroup `ParabolicPoints p` in the canonical ambient topology.
Closedness of this parabolic point subgroup is derived in the wrapper.

Apply the generic flatness and fixed-space theorems to
`parabolicLeviRationalNormCharacters r`, using its published
continuity theorem. Their coefficient algebra and induced carrier
reduce to the existing `RegularAlgebra r` and
`Induced r h hU π.representation`. For each compact open `K`, the
finite-free result gives `Module.Finite`; freeness supplies
`Module.Projective`. Together with flatness this is exactly
`UniversalInducedCoefficientFiniteness r h hU π.representation`.

The theorem retains all the target's hypotheses: the arbitrary
nonarchimedean local field `F : Type u`; connected-reductive ambient
group scheme; supplied `A`, `M`, `P`, `U` and maps `p`, `l`, `a`, `n`;
affineness of the Levi; the actual parabolic root presentation;
geometric unipotent-radical condition on `n`; local compactness and the
nonarchimedean group structure for the canonical ambient rational-point
topology; the actual semidirect decomposition; closedness of the
actual unipotent image; continuity of its actual Levi projection;
compactness of the literal parabolic left quotient; and admissibility
of the supplied `π : SmoothRep.{0, u, uV} ℂ
(parabolicLeviPointSubgroup p l)`. The independent universes `u` and
`uV` are retained. Smoothness comes from `SmoothRep`; no
finite-dimensionality of its entire carrier is used.

The scalar-extension coordinate argument, finite-relation proof of
flatness, and adaptation to literal scheme-point subgroups are internal
implementations of the cited source route. Finite freeness of these
specific universal fixed modules proves the required finite
projectivity directly, without invoking Noetherianity or the general
finite-presentation argument in Renard's VI.8.1 Proposition.
The conclusion is the coefficient-finiteness conjunction for the
published actual universal induced model. The base-change and
specialization assertions later in VI.8.2 and the Jacquet-family
assertions in VI.8.3 are separate results.
