# Continuity of actual multiplicative-type characters

Authors: Worker 3483 (Lean proof) and Worker 336 (verification and proof
documentation).

`Langlands.GroupScheme.multiplicativeTypeAbsoluteCharacterSmooth` proves the
published proposition
`Langlands.GroupScheme.MultiplicativeTypeAbsoluteCharacterSmoothStatement.{u}`
exactly. For every field `k : Type u` and commutative group scheme `T` over
`Spec k` with `IsMultiplicativeType T.toGrp`, it proves
`IsSmooth (characterLattice.galoisRepresentation k (SeparableClosure k) T)`.
The theorem is polymorphic in `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`.

## Implemented proof

Put `Ω = SeparableClosure k`, let `b : Spec Ω → Spec k` be the algebra base
map, and put `S₀ = Gm (Spec k)`. Given an actual character
`χ : T_Ω → Gm_Ω`, form
`f = χ ≫ (Gm.commBaseChangeIso b).inv : T_Ω → (S₀)_Ω`.

`IsMultiplicativeType.isAffineHom` makes `T` affine over `k`, hence
quasi-compact and quasi-separated. `smooth_gm` makes `S₀` locally of finite
presentation. Since `Ω/k` is algebraic, `Descent.FiniteStage.homModel`
therefore supplies a finite-dimensional intermediate field `E`, an actual
homomorphism `T_E → (S₀)_E`, and its exact recovery equation for `f`.
These premises use the original multiplicative-type predicate, whose
diagonalizable model may be over an arbitrary field extension.

Let `K = E.fixingSubgroup`. Mathlib's
`IntermediateField.fixingSubgroup_isOpen` makes `K` an open subgroup of
`Ω ≃ₐ[k] Ω` for the Krull topology. Each `σ ∈ K` fixes `E` pointwise.
Applying `LatticeGaloisContinuity.descent_comm_of_model` to the recovery
equation shows that the pullback of `f` along `Spec σ` commutes with the
canonical descent isomorphisms of `T` and `S₀`. Cancelling the descent
isomorphism of `T` gives `galoisHomTransport σ f = f`.

Set `ψ = characterLattice.baseChange b S₀ (𝟙 S₀)`. The published
`characterLattice.galoisRepresentation_baseChange` fixes `ψ` under every
`σ`. The comparison formula `characterLattice.baseChange_apply` gives
`f ≫ ψ = χ`. Substituting both fixedness identities into
`galoisHomTransport_comp` consequently gives
`characterLattice.galoisRepresentation k Ω T σ χ = χ`.
Unfolding `fixedVectors` with `Representation.mem_invariants` proves that
`K` fixes `χ`, as required by the existing definition of `IsSmooth`.

The open subgroup depends on the character. The finite field `E` is its
field of definition; the proof makes no assertion that `E` splits `T`.
The only smooth group used in this argument is `Gm`. In particular, the
theorem retains all characteristics and includes finite nonsmooth groups
of multiplicative type and their torsion characters.

## Provenance and published inputs

The Lean proof is reused unchanged from Worker 3483's shared Task 6980
draft revision 1. The mathematical argument is the finite field-of-definition
argument in J. S. Milne, *Algebraic Groups* (2017), §12.g, printed p.239 /
PDF p.255. It proves the continuity portion of the object-membership
assertion in Theorem 12.23, printed p.240 / PDF p.256. The registered source
is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Both source pages and the complete retained official 2017 errata snapshot
were read; no listed correction changes these passages.

The formal proof uses the already published finite-stage construction in
`Langlands.GroupScheme.Descent.FiniteStageHom`, the affineness consequence in
`Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry`, and the finite-model
descent identity in
`Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof`.
Composition compatibility is supplied by
`Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent`, and invariance of
base-changed characters by
`Langlands.GroupScheme.Rational.CharacterBaseChange`.
The actual character group, comparison for `Gm`, canonical Galois action
and representation smoothness predicate are unchanged published
constructions. Finite generation of the character group and the categorical
anti-equivalence remain separate assertions.
