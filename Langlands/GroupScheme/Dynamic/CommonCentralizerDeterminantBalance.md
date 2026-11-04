# Actual common-centralizer actions and torus determinant balance

This internal deduction constructs actual conjugation actions by a
homomorphism whose image lies in the centralizers of the displayed
cocharacters. The acting homomorphism need not represent the whole
centralizer. Representability of each acted-on subgroup is explicit.

Centralizers lie in their dynamic parabolics, which normalize the corresponding
identity-limit subgroups. This gives normalization of each full unipotent
subgroup and of the intersection of two of them. For an
unipotent/centralizer intersection, conjugation preserves the centralizer
component by its subgroup laws. Factoring the conjugation morphism through the
representing monomorphism constructs the three displayed actual automorphic
actions. Their inclusion formulas hold on every test scheme over any base.

A factorization of the original torus map through the acting homomorphism
identifies the restricted actions with ambient torus conjugation. Over any
field, the actual tangent-region and determinant formulas of
`CommonTorusIntersectionDeterminants` then identify the determinant restrictions
with the positive, positive/zero and common positive weighted characters.
Affineness, locally finite type, splitness and finite Lie coordinates remain
explicit where needed. No whole-Levi character detection is asserted.

For the final two theorems, let `zeta` and `eta` be any two cocharacters
of the same split torus with monomorphic map `i` into `G`, and assume the
published predicate `HasRelativeRootSystem i`. Let `iZ : Z ⟶ G` have image
in both centralizers, and let `j : T ⟶ Z` satisfy `j ≫ iZ = i`.
The five represented subgroups are precisely

- `U`, the identity-limit subgroup of `zeta`;
- `V`, the identity-limit subgroup of `eta`;
- `A = U ∩ centralizer(eta)`;
- `B = V ∩ centralizer(zeta)`;
- `C = U ∩ V`.

These are equalities of subgroup functors on every test scheme, supplied by
the corresponding `IsRepresentedBy` hypotheses. All five actions in the
theorems are the actual conjugation actions constructed in this module.
With arbitrary finite Lie coordinates on each represented model, write
`D_U`, `D_V`, `D_A`, `D_B`, `D_C` for their algebraic determinant
characters on `Z`. Then
`characterRestrict_centralizingDeterminant_balance` proves

`j*(D_U + D_V) = j*(D_A + D_B + 2 • D_C)`.

The proof substitutes the three determinant restriction formulas, using the
full-unipotent formula twice and the positive/zero formula with the
cocharacters interchanged for `B`. The actual weighted root-sign identity
`HasRelativeRootSystem.positiveWeightCharacter_balance` supplies the result;
commutativity of conjunction identifies the second axis predicate.
In particular both zero-pairing axis contributions are retained.
`rationalCharacterEval_centralizingDeterminant_product_square` evaluates
this algebraic-character equality at any `t ∈ T(k)` and uses compatibility
of evaluation with addition and restriction. At `j(t)` it proves the exact
identity in `kˣ`

`D_U(j(t)) D_V(j(t)) = D_A(j(t)) D_B(j(t)) D_C(j(t))²`.

There is no restriction on the characteristic, cocharacter regularity,
distinctness of the two cocharacters, or root-system rank. The explicit
affine, locally finite type, split-torus, monomorphism, representation and
finite-coordinate hypotheses remain as displayed in Lean.

This is an internal deduction from actual subgroup normalization,
`AutomorphicAction.ofNormalizedConjugation`, the actual tangent and
determinant results of `CommonTorusIntersectionDeterminants`, and the
weighted sign balance of `CommonTorusDeterminantBalance` (imported through
the intersection module). Those sign-balance results use actual opposite
weight multiplicities from `RootSystemDeterminantRestriction`. Neither the
proof bodies nor their imported-module closure use the geometric lemma,
representation-theoretic adjointness, cuspidal support, character independence,
or Langlands classification. Here equality of rational characters is an
algebraic-character calculation, without a representation-character
independence theorem.

The identities have only the stated torus restriction and image-point
scope. Extending them to all of `Z`, obtaining the whole-common-Levi
identity, comparing Haar moduli and their positive half-powers, and proving
the normalized geometric filtration and exact-K0 expansion remain separate
obligations. No such result is supplied or assumed by these theorems.
