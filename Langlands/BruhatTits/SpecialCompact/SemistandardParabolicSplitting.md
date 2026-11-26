# Compact factorization along every semistandard dynamic parabolic

This module extends the factorization `K ∩ P_J = (K ∩ M_J)(K ∩ U_J)` of a
special compact subgroup from the standard parabolics to the dynamic
parabolic of every cocharacter of the fixed maximal split torus.

The source fact is Renard, Théorème V.5.1(2)–(3), printed p.122
(PDF p.128): every relative Weyl class has a representative in `K`, and
`K` factors along every standard parabolic. These are the two properties
`HasWeylRepresentatives` and `HasParabolicFactorization` in
`BruhatTits.SpecialCompact.Properties`. J.-L. Waldspurger, *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)* (2003),
I.1, printed p.240 (PDF p.6), uses the resulting factorization for every
semistandard parabolic. The deduction is a derived argument: conjugate
by a Weyl representative in `K`.

## Setting

`k` is an arbitrary field, `G` is a connected reductive group scheme over
`k` with affine structure morphism, and `i : S → G` is a maximal split
torus. `ν` is a generic cocharacter and `K` is a subgroup of `G(k)`. No
topology is used. For a cocharacter `ξ` of `S`, `Z(ξ)` and `U(ξ)` are
the rational points of the published dynamic centralizer and unipotent
subgroup functors of `groupHom ξ ≫ i`.

## Declarations

- `cocharacterAut_normalizingAut_eq_of_mk_eq`: two normalizing points
  with the same class in `relativeWeylGroup i` act identically on
  cocharacters. Their quotient lies in `centralizerPoints i`, so its
  torus automorphism is the identity by `IsNormalizingPoint.unique`.
  The published `normalizingAut_mul` then applies.
- `mul_mem_iff_of_weylRepresentatives`: assume `HasWeylRepresentatives
  i K` and `HasParabolicFactorization i ν K`. Then for every cocharacter
  `ξ` of `S`, every `m ∈ Z(ξ)` and every `u ∈ U(ξ)`,
  `m u ∈ K ↔ m ∈ K ∧ u ∈ K`.

## Proof of `mul_mem_iff_of_weylRepresentatives`

The published chamber move
`HasRelativeRootSystem.exists_normalizerPoint_dominant`, applied to the
root system given by the published `relativeRootSystem`, yields a
normalizing point `n`. The cocharacter `n · ξ` pairs nonnegatively with
every positive relative root of `ν`. A representative `n' ∈ K` of the
same Weyl class acts in the same way, so `ξ' = n' · ξ` is dominant.
With `J` the set of simple roots vanishing on `ξ'`, the cocharacter
`ξ'` satisfies `IsStandardCocharacter i ν J ξ'`. The published
`standardCocharacter` identifies the standard parabolic, Levi and
radical for `J` with the dynamic subgroups of `ξ'`. The published
`groupHom_cocharacterAut_comp`, `Dynamic.mem_centralizer_conj` and
`Dynamic.mem_unipotent_conj` show that conjugation by `n'` carries
`Z(ξ)` and `U(ξ)` into `Z(ξ')` and `U(ξ')`.

If `m u ∈ K`, then `(n' m n'⁻¹)(n' u n'⁻¹) ∈ K ∩ P_J`. The factorization
of `K` writes this element as `a b` with `a ∈ K ∩ M_J` and `b ∈ K ∩ U_J`.
Uniqueness of the Levi–radical decomposition, the published
`dynamic_opposite_factorization_unique` with trivial first factor, gives
`a = n' m n'⁻¹`. Hence `m ∈ K`, because `n' ∈ K`, and then
`u = m⁻¹(m u) ∈ K`. The converse is closure under multiplication.

By the published `RationalDynamicSource.compact_split_iff_limit_stable`,
the conclusion is equivalent to stability of `K` under the dynamic limit
of `P(ξ)`, the form used by the source-gamma theorems.
