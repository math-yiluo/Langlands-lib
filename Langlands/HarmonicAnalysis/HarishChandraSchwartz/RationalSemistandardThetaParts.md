# Group and proper parts of the full semistandard spectral index

This module splits the full index `RationalSemistandardTheta` of
`RationalSemistandardSpectralFamily` into the group part `Theta_G` (`P = G`) and
the proper part `Theta - Theta_G` (`P ≠ G`). It defines restriction and
extension by zero for these parts, and conditional constructors into the
finite-support direct sum. It is a definitions-and-elementary-laws module.
It states no finiteness theorem and assumes no finiteness.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed p.321
(PDF p.87), registered as `waldspurger-2003-plancherel`.

- Before Theorem VIII.1.2, `Theta_G` is the set of `Im X(G)`-orbits in
  `E_2(G)`, identified with a subset of `Theta` by `O ↦ (O,G)`.
- Remark VIII.1.3 has two variants. The full variant uses `Theta^H`, resp.
  `Theta`. The proper variant ("resp. et propre") uses
  `Theta^H - Theta^H_G`, resp. `Theta - Theta_G`, and assumes VIII.1.2 only for
  Levi subgroups of proper semistandard parabolics.
- VIII.2 defines `psi[O,P] = 0` if `P = G` and `psi[O,P] = psi_f[O,P]` if
  `P ≠ G`.

## Group/proper predicate

`SemistandardSpectralIndex.IsProper p` is `p.parabolic ≠ ⊤`. Here `⊤` is the
subgroup functor of all points of `G`, on every test scheme. This is the
source's `P ≠ G`, read on the intrinsic all-test parabolic of the index. The
lemmas `isProper_iff` and `not_isProper_iff` unfold it.

`rationalSemistandardThetaGroup a ha mu` is the set of full indices `t` with
`t.1.parabolic = ⊤`. `rationalSemistandardThetaProper a ha mu` is the set of
`t` with `t.1.IsProper`. They are complementary by definition
(`compl_rationalSemistandardThetaGroup`, `compl_rationalSemistandardThetaProper`).
Their union is `Set.univ` and they are disjoint.

The module does not construct the source map `O ↦ (O,G)` from orbits in
`E_2(G)`. It also does not prove that an index with `P = G` has Levi `G` and
trivial radical. The group part is the literal subset `P = G` of the intrinsic
index, which is what the proper variant of VIII.1.3 removes. No uniqueness of
the triple over `P = G` is used.

`RationalSemistandardProperTheta a ha mu` is the subtype of the proper part.

## Restriction to the proper index type

- `rationalSemistandardProperRestrict` restricts raw full families along
  `Subtype.val`. It is complex-linear, with `_apply` the evaluation formula.
  `rationalSemistandardProperRestrict_support` gives its support as the
  preimage of the full support.
- `finite_rationalSemistandardProperRestrict_support_iff`: the restricted
  family has finite support iff `support f ∩ Theta_proper` is finite. The proof
  takes images and preimages along the injective `Subtype.val`.
- `rationalSemistandardProperSmoothRestrict` maps the smooth finite-support
  space `rationalSemistandardThetaSmoothSections a ha mu d` to the
  finite-support space on the proper index type with the same component
  submodules. It is `FiniteSupportSections.restrictSubmodule` along the
  injective `Subtype.val`.

## Extension by zero (the shape of VIII.2's `psi`)

`rationalSemistandardThetaProperPart a ha mu` is the complex-linear
endomorphism of the full product that keeps components at `P ≠ G` and puts
zero at `P = G`. `rationalSemistandardThetaGroupPart` does the opposite. Neither
needs a support or smoothness hypothesis. Applied to the actual full Fourier
family `psi_f`, the proper part is VIII.2's `psi` as a raw family. This module
does not refer to `psi_f`, and it does not claim VIII.2's membership
`psi ∈ C^infinity(Theta)^inv`.

Proved laws:

- `_apply_of_mem`, `_apply_of_not_mem`, `_apply_of_mem_group`: the component
  formulas.
- `rationalSemistandardThetaProperPart_add_groupPart`: `f` is the sum of its
  proper and group parts.
- `rationalSemistandardThetaSupport_properPart` and `_groupPart`: the support of
  each part is the support of `f` intersected with that part of the index.
- `rationalSemistandardThetaProperPart_eq_self_iff`: `f` equals its proper part
  iff its support lies in the proper part. `rationalSemistandardThetaProperPart_idem`
  follows.
- `rationalSemistandardProperRestrict_properPart`: restricting to the proper
  index type does not see the group part.
- `rationalSemistandardThetaProperPart_mem_componentSpace`: if every proper
  component of `f` lies in its coherent smooth component space, so does every
  component of the proper part. At group indices the component is `0`.
- `rationalSemistandardThetaSmoothProperPart` is the proper part as a linear
  endomorphism of the smooth finite-support space, since support can only
  shrink. `_val` gives its underlying family.

## Conditional finite-support constructors

The full Fourier family is a product before the VIII.1 finiteness results. A
raw family enters the direct sum only with explicit proofs.

- `rationalSemistandardThetaSmoothOfFinite a ha mu d f hf hs` needs
  componentwise coherent smoothness `hf` at every index and finiteness `hs` of
  the full support. This is the full variant.
- `rationalSemistandardThetaProperSmoothOfFinite a ha mu d f hf hs` is the
  proper-supported variant. It needs smoothness only at proper indices and
  finiteness only of `support f ∩ Theta_proper`. Nothing is required at
  `P = G`. Its value is the proper part of `f`.
- `rationalSemistandardProperSmoothOfFinite a ha mu d f hf hs` takes the same
  inputs and gives a finitely supported family on the proper index type.
- `rationalSemistandardProperSmoothRestrict_properSmoothOfFinite`: restricting
  the second construction gives the third.
- `rationalSemistandardThetaSmoothProperPart_smoothOfFinite`: the proper part of
  a fully finite smooth family is the proper-supported constructor applied to
  the same family.
- `_add` and `_smul` for both full-index constructors: they are additive and
  complex-homogeneous in the family, for any choice of the proof arguments.

Smoothness and finite support are inputs here. They carry no covariance. Any
membership in an invariant carrier must use the separate smoothness and VII.1.4
covariance targets of the owning tasks.

## Standard slice

Under the hypotheses `hG`, `hi`, `hnu` of the published standard slice in
`RationalSemistandardSpectralFamily`:

- `rationalSemistandardStandardIndex_mem_proper_iff`: a standard index lies in
  the proper part iff `standardParabolic i nu (rootSet i nu I) ≠ ⊤`. This holds
  by definition.
- `rationalSemistandardStandardRestrict_properPart_of_mem` and `_of_not_mem`:
  the standard slice of the proper part keeps the proper standard components
  and vanishes elsewhere.
- `rationalSemistandardStandardRestrict_properPart_support`: its support is the
  preimage of `support f ∩ Theta_proper`.
- `rationalSemistandardStandardSmoothRestrict_smoothProperPart_val`: the
  smooth standard restriction of the smooth proper part, by evaluation.

No identification of the standard group index with the full root subset is
asserted. The standard hypotheses are exactly those of the existing standard
slice; none is strengthened.

## Provenance

The two parts and the extension by zero follow the source definitions quoted
above. The subtype restriction, the support and linearity laws, and the
constructors are internal derived interfaces for these definitions. All proofs
use the published `FiniteSupportSections` laws, set algebra, and the
definitional component formulas.
