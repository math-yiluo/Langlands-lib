# The Weil group of a prescribed intermediate field

Author: Worker 100. This is one derived definition and construction unit, with a
small common-closure wrapper in
`Langlands.LocalFactor.CommonClosureIntermediateWeil`.

## Inputs and result

Fix a prime `p`, a `PadicField.{u} p` object `F`, and
`E : LocalClassField.FiniteIntermediateExtension F.Carrier`. Thus `E.field` is a
specified finite intermediate field of `AlgebraicClosure F.Carrier`, with its
literal subtype inclusion. Put `EP = E.asPadicField (p := p)`.
`intermediateWeilEquiv F E` has type

```lean
localWeilGroup EP ≃ₜ*
  pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)
```

Both sides carry the existing actual Weil pullback and subgroup topologies.
`EP` uses the canonical local-field structures. The codomain fixes this same
`E.field`, rather than the image field of an unrelated closure lift. There is
no extra closure equivalence, continuity, norm-preservation or inertia hypothesis.
The construction depends on a choice of a closure extension; no uniqueness,
choice independence or tower functoriality is asserted.

## Closure extension and the Galois action

`intermediateEmbedding F E` is the actual `Padic p`-algebra inclusion
`F.Carrier →ₐ[Padic p] E.field`. The finite intermediate-field structure supplies
the scalar tower and finite-dimensional structure used by the published
extension APIs.

`intermediateClosureEquiv F E`, denoted `b`, is an `E.field`-algebra isomorphism
from `AlgebraicClosure E.field` to `AlgebraicClosure F.Carrier`. The latter is
algebraic over `E.field` by `Algebra.IsAlgebraic.tower_top`; both fields are
algebraically closed. Mathlib's `IsAlgClosed.lift` provides an algebra
homomorphism, and `Algebra.IsAlgebraic.algHom_bijective₂` proves its bijectivity.
The theorem `intermediateClosureEquiv_algebraMap` is its scalar compatibility:
`b (algebraMap E.field _ x) = (x : AlgebraicClosure F.Carrier)`.

Let `a` be the published `extensionClosureEquiv F EP (intermediateEmbedding F E)`,
which goes in the opposite direction. `intermediateClosureCorrection F E` is
the absolute Galois element `c = b ∘ a`. Its fixing of `F` follows from
`extensionClosureLift_algebraMap` and the preceding scalar compatibility.
`intermediateClosureCorrection_fieldEmbedding` proves that `c` sends every
point of the old `extensionFieldEmbedding` to the literal corresponding point
of `E.field`.

`intermediateGaloisMap` sends `τ ∈ G_E` to
`c * extensionGaloisMap F EP (intermediateEmbedding F E) τ * c⁻¹`.
Its continuity follows from the published Galois map and continuous group
operations. `intermediateClosureEquiv_galoisMap` proves
`j_G(τ)(b(x)) = b(τ(x))`, by the old closure-lift compatibility and cancellation
of the correction. `intermediateGaloisMap_apply` equivalently expresses this
as `j_G(τ)(y) = b(τ(b⁻¹(y)))`.

`intermediateClosureCorrection_conj_mem` proves that `c τ c⁻¹` fixes `E.field`
if and only if `τ` fixes the old `extensionIntermediateField`. The proof
checks each field element, using the proved correction formula and the
published description of the old field as the image of
`extensionFieldEmbedding`. It assumes no equality between the two fields.

## The Weil map and its topology

The private lemma `frobenius_central` proves that each integer Frobenius
commutes with every profinite integer. The equality holds on the dense image
of the commutative integer group and extends by continuity.
`galoisConjugationWeil F σ` therefore sends a pullback pair `(τ,m)` to
`(σ τ σ⁻¹,m)` and remains in the same Weil pullback. Its inverse conjugates
by `σ⁻¹`; continuity follows from the ambient product and subgroup topologies.
Its projection is conjugated and its degree is unchanged.

`intermediateWeilMap` composes this conjugation for `c` with the published
`extensionWeilMap`. The projection and degree formulas are
`localProjection_intermediateWeilMap` and `localDegree_intermediateWeilMap`.
`intermediateWeilMap_range` proves that its range is exactly
`pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)`: the published
`extensionWeilMap_range` and `extensionGaloisMap_range` characterize the old
image, and `intermediateClosureCorrection_conj_mem` transports that condition.
For the reverse inclusion, inverse conjugation gives an element of the old
Weil image and hence a preimage.

`intermediateWeilMap_injective` and `intermediateWeilMap_isEmbedding` compose
the published properties of `extensionWeilMap` with the conjugation
homeomorphism. `intermediateWeilEquiv` packages the injective map as an
equivalence onto its range using `MonoidHom.ofInjective`, then uses the proved
range equality. The inverse is continuous because composition with the
embedding is the continuous subtype inclusion. The equations
`intermediateWeilEquiv_apply` and `intermediateWeilMap_equiv_symm` describe both
directions. `intermediateWeilEquiv_projection` and
`intermediateWeilEquiv_symm_projection` give the ambient Galois projection in
both directions, using the constructed `intermediateGaloisMap`.

## Degree, norm and inertia

Write `r = extensionResidueDegree F EP (intermediateEmbedding F E)`, the actual
relative residue degree. `intermediateWeilEquiv_degree` states

```text
deg_F(intermediateWeilEquiv F E w) = r * deg_EP(w).
```

The degrees here are geometric integer degrees. The norm theorem
`intermediateWeilEquiv_normCharacter` states
`localNormCharacter F (intermediateWeilEquiv F E w) = localNormCharacter EP w`.
The proofs reuse `localDegreeInt_extensionWeilMap` and
`localNormCharacter_extensionWeilMap`, since conjugation leaves the degree
coordinate unchanged. In particular the norm proof already uses the actual
residue-cardinality identity `q_EP = q_F ^ r`, not an assumed preservation
condition. The corresponding `intermediateWeilEquiv_symm_degree` and
`intermediateWeilEquiv_symm_normCharacter` express these formulas on an element
of the fixing subgroup.

`intermediateWeilMap_mem_localInertia` and
`localInertia_eq_comap_intermediateWeilMap` prove exactly
`j_W⁻¹(I_F) = I_EP`. They reuse the proved extension inertia criterion, whose
degree argument uses positivity of `r`.
`intermediateInertia F E` is ambient inertia pulled back to the actual fixing
subgroup. The two membership lemmas for `intermediateWeilEquiv` and its inverse
identify it with standalone inertia. `localInertia_inf_intermediateFixing`
also expresses the ambient intersection as the image of `I_EP`.
`intermediateInertiaEquiv` is the restriction of the continuous Weil
equivalence in both directions; its forward and inverse coercion formulas
are `intermediateInertiaEquiv_apply` and
`intermediateInertiaEquiv_symm_apply`.

No assertion about upper ramification groups, Herbrand functions, conductors,
epsilon factors or DH81 laws is made here.

## Provenance and checks

This is an internal construction from the published APIs, not a new
literature theorem. The imports use `ExtensionGalois`, `ExtensionWeil` and
`ExtensionWeilRange` transitively, and `ClassFieldTheory.Local.ReciprocitySystem`
for the prescribed intermediate field and its `asPadicField`. The old
chosen-image construction, also used by `ReciprocityTransport`, is unchanged.
All new code and documentation are by Worker 100; published dependencies are
imported by Lean name. The closure extension, conjugacy calculation, exact
range and restriction to inertia above describe the implemented proofs.

The paired wrapper identifies the target with `CommonClosure.weilSubgroup`
and its inertia with `CommonClosureWeilDeligne.inertia`. Private checks assign
the unapplied closure, Galois, Weil and inertia constructors, and the main
compatibility theorems, to their complete intended signatures. Separate
consumer examples apply the forward and inverse continuous maps to
`FiniteRepresentation.continuousRestrict` and
`ExactGrothendieckGroup.continuousRestrict`, including
`CommonClosure.Virtual.{uF,uV}` with independent field and carrier universes.
The generic exact quotient construction is reused unchanged.
