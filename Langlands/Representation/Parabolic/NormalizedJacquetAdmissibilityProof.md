# Admissibility of the normalized product-Levi Jacquet representation

Author: Worker 320.

The theorem `Langlands.Parabolic.normalizedJacquetAdmissibility.{uF,uV}`
proves exactly `Langlands.Parabolic.NormalizedJacquetAdmissibilityClause`
from `Langlands.Representation.Parabolic.NormalizedJacquetStatement`.
For an admissible complex representation `rho` of `GL_n(F)`, it proves
admissibility of

```
twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
  (leviCoinvariants B (rho.comp (B.parabolic F.Carrier).subtype))
```

Every prime, p-adic field, supplied compatible topology, natural rank
including zero, ordered positive block shape, and carrier in an independent
universe is retained. There is no finite-type, irreducibility, finite-dimensional
carrier, canonical-lift, or Jacquet-admissibility hypothesis. The proof leaves
the target pair and all existing dependencies unchanged.

## Implemented proof

Write `P` for the actual block parabolic, `N` for its radical as an ambient
matrix subgroup, `M` for the embedded block-diagonal subgroup, and `Lprod`
for the product Levi. Let `Qp` be the actual radical quotient after restriction
to `P`, and `Qa` the ambient coinvariant quotient by `N`.

`jacquetModuleEquiv_leviCoinvariants` proves equivariance of the existing
linear equivalence `B.jacquetModuleEquiv rho : Qp ≃ₗ[ℂ] Qa` for the actual
product-Levi and embedded-Levi actions. The product element `m` corresponds
to `B.leviEquiv F.Carrier m` in `M`. Surjectivity of the quotient map reduces
this identity to a representative `v`; both sides are the class of
`rho(B.leviEmbedding F.Carrier m)v`. This compares both carriers and actions,
rather than identifying the two quotient types implicitly.

`isSmooth_leviCoinvariants` proves smoothness directly. Represent a quotient
vector by `v` and choose an open ambient subgroup `K` fixing `v`. Its preimage
under the continuous product-Levi embedding is an open subgroup of `Lprod`.
The quotient action formula shows that this subgroup fixes the class of `v`.
No compactness is needed for this step.

`exists_iwahori_levi_subset` handles an arbitrary open subgroup `L` of
`Lprod`. The existing homeomorphic group equivalence `B.leviEquivContinuous`
transports its identity neighborhood to `M`. The subtype topology on `M`
expresses that neighborhood as containing the intersection of `M` with an
ambient identity neighborhood `U`. The published
`exists_compactOpenSubgroup_hasBlockIwahoriFactorization` chooses a compact
open ambient subgroup `K` inside `U`. Consequently every `m` in `M ∩ K`
corresponds to an element of `L`. The proof does not assume that `L` is
compact or extend it to an ambient open subgroup.

`isAdmissible_leviCoinvariants` first uses the smoothness result. To prove
finite dimensionality of the `L`-fixed space, choose `K` as above and a
strictly contracting block-scalar tuple `a` from the published
`deepChamberNonempty T 1`. Depth one is exactly the strict inequality used
here. Admissibility of `rho` makes `X = V^K` finite dimensional. Its actual
compressed-operator stable-image submodule `S` is therefore finite dimensional.
The published `Jacquet.blockStableImageJacquetBijective` says that the actual
map

```
S -> fixedVectors (Jacquet.action rho N M hMN) (K.toSubgroup.comap M.subtype)
```

is bijective. Its surjective part and `Module.Finite.of_surjective` give
finite dimensionality of this embedded-Levi quotient fixed space. No
canonical-lift property is assumed: the existing theorem is applied to the
constructed `K`, its proved factorization, the constructed tuple, and the
input admissibility.

The proof then restricts `B.jacquetModuleEquiv rho` to the `L`-fixed submodule
of `Qp`. Equivariance and the containment `M ∩ K ⊆ L` under the Levi
identification show that its image lies in the preceding finite-dimensional
fixed space of `Qa`. The restricted linear map remains injective because
the original map is a linear equivalence. `Module.Finite.of_injective` proves
finite dimensionality of the `L`-fixed space. This is the passage from
sufficiently small compact open subgroups to every open Levi subgroup.
Over `ℂ`, the Library's `Module.Finite` condition is finite dimensionality.

Finally `normalizedJacquetAdmissibility` applies
`Langlands.isAdmissible_twist_iff` to the actual inverse-half character.
`Jacquet.isOpen_ker_inverseHalfCharacter`, applied to the proved
`T.isOpen_ker_leviModulus B`, supplies its open kernel. The character is the
complex image of the inverse positive square root of the explicit block
modulus. The twist compatibility theorem uses smaller open subgroups inside
that kernel, where twisted and untwisted fixed vectors coincide, and also
preserves smoothness. This establishes the exact normalized target.

## Original source and provenance

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019. The registered source is
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The original pages 6–7 were read, including a visual check of page 7.
No separate project errata note for this source was present; the correction
warning in the original itself was checked.

Lemma III.5.4 on page 6 identifies the nilpotent part of the compact-fixed
space with its Jacquet kernel. The discussion following it obtains an
invertible complement over a field. Page 7 explicitly restricts the
coefficients to a field before Proposition III.5.5, which proves the canonical
projection from that complement to the Levi-fixed quotient is an isomorphism.
Theorem III.5.6 then concludes Jacquet admissibility. The warning after
III.5.7 records an incorrect earlier argument for arbitrary Noetherian
coefficients. This proof is over `ℂ` and uses the published finite-dimensional
stable-image bijectivity theorem; it makes no such general-ring extension.

The source motivates the route. The new equivariance and topology lemmas
are derived comparison arguments for the project's two concrete Levi and
quotient presentations. Canonical lifting, existence of small Iwahori
subgroups, contraction, and twist compatibility are imported proved results,
not source assertions used as assumptions. The all-open-subgroups conclusion,
rank-zero case, and independent field/carrier universes are present in Lean;
no pairing, duality, finite-generation, or normalized-induction theorem is
proved or assumed by this module.
