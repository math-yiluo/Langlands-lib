# Reduction sequences for equivariant derived sections of ℓ-divisible systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.DerivedReductionSequence` (Worker 61:
`derivedPowSMulNatTrans`, `derivedReductionNatTrans`,
`derivedReductionδNatTrans`, `map_powSMulMap_comp_map_projection`,
`map_projection_comp_derivedReductionδ`,
`derivedReductionδ_comp_map_powSMulMap`, `powSMulShortComplex_shortExact`,
`powSMul_limit_comp_π_eq_zero`, `π_comp_derivedAdicδ`,
`derivedAdicδ_comp_powSMul`, `derivedAdicReductionSequence`,
`derivedAdicReductionSequence_shortExact`, the three `limMap` lemmas
`limMap_derivedPowSMulNatTrans_comp_levelShiftLimitIso`,
`limMap_derivedReductionNatTrans_comp_constLimitIso` and
`limMap_derivedReductionδNatTrans`, and in the namespace
`Langlands.Cohomology` `levelShiftLimitIso`, `constLimitIso` and
`limit_exact_of_finite`),
`Langlands.Cohomology.EquivariantDerivedSections` (Worker 13:
`EquivariantDerivedSections.compactDerived` and
`EquivariantDerivedSections.globalDerived`, with the left exactness of
`CompactSections.functor` and `sectionRepresentation`),
`Langlands.Cohomology.SmoothSheafCohomology` (Worker 13:
`SmoothSheafCohomology.compactDerived`,
`SmoothSheafCohomology.invariantCompactSections`,
`SmoothSheafCohomology.invariantCompactDerived`),
`Langlands.Cohomology.LeftExactHomology` (Worker 61:
`LeftExactHomology.derivedNatTrans` and the instance
`LeftExactHomology.isIso_derivedNatTrans`) and
`Langlands.Representation.Category.ExactInclusion` (the instances
`toRep_preservesFiniteLimits` and `toRep_preservesFiniteColimits` for the
inclusion `Langlands.SmoothRep.toRep` of smooth representations into all
representations). Through their imports it uses the published
`DivisibleSystem` (`Langlands.Cohomology.DivisibleSystem`, Worker 61: `tower`,
`obj`, `powSMul`, `comp_powSMul`, and the abbreviation
`SmoothSheafDivisibleSystem R G X ℓ` for `DivisibleSystem` in
`SmoothTopologicalSheaf R G X`), `shortComplex_exact_of_evaluation`
(`Langlands.Cohomology.DivisibleSystem.Colimit`, Worker 61),
`cokernelKernelShortComplex_shortExact`
(`Langlands.Cohomology.DivisibleSystem.ReductionSequence`, Worker 61), the
exactness lemmas `DerivedPlus.rightDerived_exact₁`, `rightDerived_exact₂`,
`rightDerived_exact₃` (`Langlands.Cohomology.RightDerivedSequence`, Worker
61), Worker 13's `TopologicalSheaf`, `CompactSections.functor`
(`Langlands.Sheaf.Equivariant.CompactSupport`), `sectionRepresentation`
(`Langlands.Sheaf.Equivariant.FunctionSheaf`), `SmoothTopologicalSheaf`
(`Langlands.Sheaf.Equivariant.SmoothAbelian`), `smoothSheafCompactSections`
(`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`) and
`Langlands.SmoothRep` (`Langlands.Representation.Category.Abelian`), and
Worker 3's unproved statement `MittagLefflerShortExactLimitStatement`
(`Langlands.Cohomology.InverseLimit.Statement`), which appears only as a
hypothesis.

From Mathlib it uses `Rep` with `forget₂ (Rep k G) (ModuleCat k)`,
`preservesSmallestLimits_of_preservesLimits`, `preservesLimitNatIso`,
`Functor.whiskeringRight`, `evaluation`,
`ShortComplex.exact_map_iff_of_faithful`, `ShortComplex.exact_of_iso`,
`ShortComplex.mapNatIso`, `ShortComplex.isoMk`, `ShortComplex.ShortExact`,
`Functor.rightDerived`, `asIso`, `lim`, `Functor.mapIso`,
`Functor.isoWhiskerLeft`, `cokernel.mapIso`, `kernel.mapIso`,
`Representation.equivOfIso` and `Finite.of_equiv`.

`limit_exact_of_finite_rep` is in the namespace `Langlands.Cohomology` and
`compactDerivedToRepIso` in `Langlands.Cohomology.SmoothSheafCohomology`; all
other declarations are in `Langlands.Cohomology.DivisibleSystem`.

## Conventions

As in the published `DerivedReductionSequence`: `f ≫ g` is `f` followed by
`g`; `powSMul ℓ r M` is multiplication by `ℓ ^ r`; `M / ℓ ^ r` is its
cokernel and `M[ℓ ^ r]` its kernel (Milne's `M^(ℓ^r)` and `M_{ℓ^r}`); `m`, `r`
are levels and `q` the degree; `T : DivisibleSystem C ℓ` has levels
`T m = T.obj m`; `R^q F = F.rightDerived q`; `lim_m R^q F(T m)` is the limit
of the inverse system `T.tower ⋙ F.rightDerived q`. The `HasDerivedCategory`
instances needed by the published long exact sequence of right derived
functors are arguments.

## The general statement

`C` is abelian with enough injectives, `D` abelian with limits indexed by
`ℕᵒᵖ`, and `F : C ⥤ D` additive.

- `derivedAdicReductionSequence_shortExact_of_limitExact F T P hlim r q hfin`:
  let `P` be a property of objects of `D` such that `lim` keeps exact every
  exact sequence `X₁ ⟶ X₂ ⟶ X₃` of inverse systems in `D` whose terms
  `X₁(m)` all satisfy `P` (`hlim`). If every `R^q F(T m)` satisfies `P`
  (`hfin`), then the published `derivedAdicReductionSequence F T r q`,
  `0 ⟶ (lim_m R^q F(T m)) / ℓ ^ r ⟶ R^q F(T r) ⟶
  (lim_m R^(q+1) F(T m))[ℓ ^ r] ⟶ 0`, is short exact. Proof: the proof of the
  published `derivedAdicReductionSequence_shortExact` with `hlim` in place of
  `limit_exact_of_finite`. The three sequences of inverse systems
  `R^q F(T m) ⟶ R^q F(T (m + r)) ⟶ R^q F(T r)`,
  `R^q F(T (m + r)) ⟶ R^q F(T r) ⟶ R^(q+1) F(T m)` and
  `R^q F(T r) ⟶ R^(q+1) F(T m) ⟶ R^(q+1) F(T (m + r))` are exact levelwise.
  Their first terms are `R^q F(T m)`, `R^q F(T (m + r))` and the constant
  `R^q F(T r)`, so all satisfy `P`, and `hlim` makes their limits exact. The
  published `limMap` lemmas identify the limits with the pieces of the
  four-term sequence, and `cokernelKernelShortComplex_shortExact` concludes.

## Representations

`k` is a commutative ring and `G` a monoid; `Rep k G` is Mathlib's category
of `k`-linear representations of `G`.

- `limit_exact_of_finite_rep hML hS hfin`: for an exact sequence
  `X₁ ⟶ X₂ ⟶ X₃` of inverse systems of representations with every `X₁(m)`
  finite, given `hML : MittagLefflerShortExactLimitStatement k`,
  `lim X₁ ⟶ lim X₂ ⟶ lim X₃` is exact. Proof: the forgetful functor
  `Φ = forget₂ (Rep k G) (ModuleCat k)` preserves limits and is exact, so the
  sequence of underlying inverse systems of modules is exact and the
  published `limit_exact_of_finite` makes its limit exact. That limit is
  isomorphic to `Φ` applied to the limit sequence (`preservesLimitNatIso`),
  and `Φ` reflects exactness (`exact_map_iff_of_faithful`).
- `derivedAdicReductionSequence_shortExact_rep F T hML r q hfin` (Milne,
  Lemma 1.11, for right derived functors with values in representations): for
  `F : C ⥤ Rep k G`, if every `R^q F(T m)` is finite, given
  `MittagLefflerShortExactLimitStatement k`,
  `derivedAdicReductionSequence F T r q` is short exact. It is the general
  statement with `P` finiteness and `limit_exact_of_finite_rep`.

## Equivariant sheaves

`R : Type u` is a commutative ring, `G : Type u` a group acting on the
topological space `X : Type u` by continuous translations, and `T` an
`ℓ`-divisible system in Worker 13's abelian category
`TopologicalSheaf G X (ModuleCat R)` of equivariant module sheaves.
`H^q_c = EquivariantDerivedSections.compactDerived R G X q` and
`H^q = EquivariantDerivedSections.globalDerived R G X q` are Worker 13's right
derived functors of the compact and global section representations, with
values in `Rep R G`.

- `equivariantCompactReductionSequence R G X T r q`:
  `derivedAdicReductionSequence` for `CompactSections.functor R G X`, the
  short complex of representations
  `(lim_m H^q_c(T m)) / ℓ ^ r ⟶ H^q_c(T r) ⟶ (lim_m H^(q+1)_c(T m))[ℓ ^ r]`.
  `equivariantCompactReductionSequence_X₁`, `_X₂` and `_X₃` (by definition)
  state its terms in terms of `compactDerived`.
  `equivariantCompactReductionSequence_shortExact R G X T hML r q hfin`: if
  every `H^q_c(T m)` is finite, given
  `MittagLefflerShortExactLimitStatement R`, it is short exact.
- `equivariantGlobalReductionSequence R G X T r q`, its `_X₁`, `_X₂`, `_X₃`
  lemmas and `equivariantGlobalReductionSequence_shortExact`: the same for
  `sectionRepresentation R G X` and `H^q`.

## Smooth equivariant sheaves

Now `G : Type u` is a topological group (`IsTopologicalGroup`) acting on `X`
with `HasStableNeighbourhoods G X`, and `T : SmoothSheafDivisibleSystem R G X ℓ`
is an `ℓ`-divisible system in Worker 13's abelian category
`SmoothTopologicalSheaf R G X` of smooth equivariant module sheaves. Worker
13's `SmoothSheafCohomology.compactDerived R G X q` is the `q`-th right
derived functor of `smoothSheafCompactSections R G X`, with values in the
category `SmoothRep R G` of smooth representations.

- `SmoothSheafCohomology.compactDerivedToRepIso R G X q`: the right derived
  functors of `smoothSheafCompactSections R G X ⋙ SmoothRep.toRep`, with
  values in `Rep R G`, are isomorphic to `compactDerived R G X q ⋙
  SmoothRep.toRep`. It is the published `LeftExactHomology.derivedNatTrans`,
  an isomorphism because `SmoothRep.toRep` is exact
  (`LeftExactHomology.isIso_derivedNatTrans`, with the instances of
  `ExactInclusion`).
- `smoothCompactReductionSequence R G X T r q`:
  `derivedAdicReductionSequence` for
  `smoothSheafCompactSections R G X ⋙ SmoothRep.toRep`, the short complex in
  `Rep R G`
  `(lim_m H^q_c(T m)) / ℓ ^ r ⟶ H^q_c(T r) ⟶ (lim_m H^(q+1)_c(T m))[ℓ ^ r]`.
  The limits are taken in `Rep R G`, not in `SmoothRep R G`: the `ℓ`-adic
  limit of smooth representations need not be smooth, and Harris's
  `lim_m H^q_c(U(ẽ), ℤ/ℓ^m)` is such a limit.
- `smoothCompactLimitIso R G X T q`: `lim_m H^q_c(T m)` for these derived
  functors is isomorphic to the limit in `Rep R G` of the representations
  underlying the published `compactDerived R G X q` of `T m` (by
  `compactDerivedToRepIso`). `smoothCompactReductionSequenceX₁Iso`,
  `smoothCompactReductionSequenceX₂Iso` and
  `smoothCompactReductionSequenceX₃Iso`: the three terms of
  `smoothCompactReductionSequence` are isomorphic to
  `(lim_m compactDerived(T m)) / ℓ ^ r`, the representation underlying
  `compactDerived(T r)`, and `(lim_m compactDerived(T m))[ℓ ^ r]` in degree
  `q + 1`, all in `Rep R G`.
- `smoothCompactReductionSequence_shortExact R G X T hML r q hfin`: if the
  carrier of every smooth representation `compactDerived R G X q` of `T m` is
  finite, given `MittagLefflerShortExactLimitStatement R`, the sequence is
  short exact. Proof: `derivedAdicReductionSequence_shortExact_rep`, with the
  finiteness transported along `compactDerivedToRepIso`.
- `smoothInvariantCompactReductionSequence R G X T r q`:
  `derivedAdicReductionSequence` for Worker 13's invariant compact sections
  `SmoothSheafCohomology.invariantCompactSections R G X`, a short complex of
  `R`-modules built from `SmoothSheafCohomology.invariantCompactDerived`; its
  `_X₁`, `_X₂`, `_X₃` lemmas (by definition) and
  `smoothInvariantCompactReductionSequence_shortExact` (if every
  `invariantCompactDerived R G X q` of `T m` is finite, given
  `MittagLefflerShortExactLimitStatement R`, by the published
  `derivedAdicReductionSequence_shortExact`).

## Provenance and interpretation

Milne, *Étale Cohomology* (1980), Chapter V, §1, as quoted in the published
`DerivedReductionSequence`: printed p.165 (one-based PDF page 179), Lemma
1.11, gives for an `l`-adic sheaf `F = (F_n)` with each `F_n` flat over
`Z/(l^n)` and all `H^r(X, F_n)` finite the exact sequences
`0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0`, where
`H^r(X, F) = lim H^r(X, F_n)` (printed p.164, one-based PDF page 178).

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §2 (Worker 61 read the text layer):

- printed p.304 (one-based PDF page 6), (2.1), as quoted in the published
  `DivisibleSystem`: "By an ℓ-divisible system of S(ẽ)-modules over U(ẽ) we
  mean a collection {T_m} of étale sheaves in smooth ℤ/ℓ^mℤ[S(ẽ)]-modules over
  U(ẽ), m ≥ 1, with morphisms i = i_{m',m} : T_{m'} → T_m and
  j = j_{m,m−m'} : T_m → T_{m−m'}, for all m > m' ≥ 1 such that T_m is free
  over ℤ/ℓ^mℤ, i identifies T_{m'} with the p^{m'}-torsion in T_m, and (2.1)
  0 → T_{m'} → T_m → T_{m−m'} → 0 is exact."
- printed p.303 (one-based PDF page 5), Fact 1 bis: the groups
  `H^q_c(U(ẽ), Z/ℓ^m Z)` are finite. Printed p.305 (one-based PDF page 7): they
  are finite smooth `S(ẽ)`-modules.
- printed p.306 (one-based PDF page 8), Lemma 2.8: "For every q, there is a
  canonical isomorphism H^q(lim C_m^•(U(ẽ)_F̂)) ≅ lim H^q_c(U(ẽ)_F̂, Z/ℓ^m Z)."

Interpretation. Harris's ℓ-divisible systems of sheaves with a smooth action
of `S(ẽ)` are the published `DivisibleSystem` in a category of equivariant
sheaves; `SmoothSheafDivisibleSystem` is the smooth case. The groups
`H^q_c(U(ẽ), Z/ℓ^m)` are smooth `S(ẽ)`-modules, so their limit, the right
side of Lemma 2.8, carries an action of `S(ẽ)`. This module gives Milne's
sequences for such limits of derived equivariant sections, with the group
action kept: `smoothCompactReductionSequence` is the case closest to Harris's
compactly supported cohomology. Harris's derived functors are those of
`Γ_c` on étale sheaves on the analytic space `U(ẽ)` computed with
Berkovich's resolution; here they are Mathlib's right derived functors on
Worker 13's categories of equivariant sheaves on a topological space, and
the system `T` is arbitrary. The proof follows Milne's (see the published
`DerivedReductionSequence`); exactness of inverse limits of finite
representations is reduced to the module case. Milne's and Harris's
finiteness (Fact 1 bis) is the hypothesis `hfin`, used only in degree `q`.
`compactDerivedToRepIso`, `smoothCompactLimitIso`, the `X₁`/`X₂`/`X₃`
isomorphisms and lemmas, and the general statement with `P` are internal
framework. The statements and proofs are ours; the module is derived.

## Scope

Harris's construction of the system (Lemmas 2.2, 2.2 bis), his finiteness
facts and Lemma 2.8 are not formalized, and nothing is said about étale
sheaves on analytic spaces. The short exactness assumes Worker 3's
`MittagLefflerShortExactLimitStatement` (`hML`) and the finiteness of the
level cohomology (`hfin`). No topology or continuity on the limits,
`ℚ_ℓ`-coefficients, finite generation over `ℤ_ℓ`, or naturality in `T` is
treated. The smooth global sections case is not included.

Source registrations: Milne 1980, `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
