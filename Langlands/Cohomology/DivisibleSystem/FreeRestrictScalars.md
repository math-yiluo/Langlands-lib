# Free representations over `𝒪/ℓ^m𝒪[Γ]` as representations over `𝒪`

Author: Worker 61. Built on the published module
`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`
(`FreeOverPowQuotient`, `torsionQuotientRep`, `torsionQuotientRepIso`,
`isTorsionBySet_of_powSMul_eq_zero`, `powSMul_hom_apply`, and the instances
stating that restriction of scalars along `R → R ⧸ I` is full and faithful).
Through its imports it uses `repRestrictScalars` and the local instance
`restrictScalarsModule` (`Langlands.Cohomology.DivisibleSystem.ScalarExtension`),
`powSMul` and `comp_powSMul` (`Langlands.Cohomology.DivisibleSystem`),
`Induction.asModuleLinearEquiv` and `Induction.compactInducedInvariants_free`
(`Langlands.Representation.Induction.PermutationInvariants`) and
`Induction.compactInduced` (`Langlands.Representation.Induction.Definitions`).
From Mathlib it uses `Rep`, `Rep.of`, `Rep.mkIso`, `Rep.hom_ext`,
`Representation.equivOfIso`, `Representation.Equiv`, `RestrictScalars.addEquiv`
and `RestrictScalars.addEquiv_map_smul`, `Module.IsTorsionBySet`,
`Module.IsTorsionBySet.module` and `Module.IsTorsionBySet.mk_smul`,
`Module.Free` and `Module.Free.of_equiv`, `Functor.preimageIso`,
`Ideal.Quotient.algebraMap_eq`, `Ideal.Quotient.mk_surjective`,
`Ideal.Quotient.eq_zero_iff_mem` and `Ideal.mem_span_singleton_self`.

## Conventions

`ℓ` and `m` are natural numbers and `R` is a commutative ring. `(ℓ ^ m)`
denotes the ideal `Ideal.span {((ℓ : R) ^ m)}` of `R` and `R ⧸ (ℓ ^ m)` the
quotient ring. `powSMul ℓ m X` is the published endomorphism "multiplication
by `ℓ ^ m`" of an object `X`; "`X` is killed by `ℓ ^ m`" means
`powSMul ℓ m X = 0`. For a representation `P` of `G` over a commutative ring
`k`, `P.ρ.asModule` is its module over the group algebra
`MonoidAlgebra k G` (written `k[G]`), and "`P` is free over `k[G]`" means
`Module.Free (MonoidAlgebra k G) P.ρ.asModule`.

`repRestrictScalars R S G : Rep S G ⥤ Rep R G` is the published restriction of
scalars along an algebra `R → S`: same additive group and operators, with `R`
acting through `algebraMap R S`. For a representation `X` over `R` killed by an
ideal `I` (`hX : Module.IsTorsionBySet R X I`), the published
`torsionQuotientRep X hX` is the same representation regarded over `R ⧸ I`,
and `torsionQuotientRepIso X hX` identifies its restriction of scalars back to
`R` with `X`.

The published predicate `FreeOverPowQuotient ℓ m P`, for `P` in `Rep R G`,
states: there is a proof `h` that `P` is killed by `ℓ ^ m`, and
`torsionQuotientRep P _` is free over `(R ⧸ (ℓ ^ m))[G]`. It formalizes
Harris's "free `𝒪/ℓ^m𝒪[Γ]`-module" with `𝒪 = R`.

Representations have carriers in one universe `w` (`Rep.{w}`); `G` is a
monoid unless stated otherwise.

## Freeness and isomorphisms (namespace `Langlands.Cohomology`)

- `free_asModule_of_iso e hP`: for an isomorphism `e : P ≅ Q` in `Rep k G` and
  `hP` stating that `P` is free over `k[G]`, `Q` is free over `k[G]`. The
  isomorphism gives an equivalence of representations
  (`Representation.equivOfIso`), hence a `k[G]`-linear equivalence of the
  modules over the group algebra (`Induction.asModuleLinearEquiv`), and
  freeness transfers along it (`Module.Free.of_equiv`).

## Restriction of scalars along `R → R ⧸ I` (namespace `Langlands.Cohomology`)

`I` is an ideal of `R` and `Y` a representation of `G` over `R ⧸ I`.

- `isTorsionBySet_repRestrictScalars Y`: the restriction of scalars of `Y` to
  `R` is killed by `I`. An element `a` of `I` acts as its image in `R ⧸ I`,
  which is zero.
- `torsionQuotientRepRestrictIso Y hY` (the entry declaration): for any proof
  `hY` of the previous statement, an isomorphism in `Rep (R ⧸ I) G` from
  `torsionQuotientRep` of the restriction of scalars of `Y` to `Y`. It is the
  identity of the underlying additive group (`RestrictScalars.addEquiv`). It
  is `R ⧸ I`-linear because the class of `r` acts on the left-hand side as `r`
  (`Module.IsTorsionBySet.mk_smul`), that is, as the image of `r` in `R ⧸ I`
  acting on `Y`; the operators of `G` agree by definition.

## `FreeOverPowQuotient` (namespace `Langlands.Cohomology.DivisibleSystem`)

- `powSMul_repRestrictScalars_eq_zero Y`: for a representation `Y` over
  `R ⧸ (ℓ ^ m)`, its restriction of scalars to `R` is killed by `ℓ ^ m`.
  Multiplication by `ℓ ^ m` is scalar multiplication by the element
  `(ℓ : R) ^ m` (`powSMul_hom_apply`), which lies in the ideal `(ℓ ^ m)`.
- `freeOverPowQuotient_repRestrictScalars Y hY`: if `Y` is free over
  `(R ⧸ (ℓ ^ m))[G]` (`hY`), its restriction of scalars to `R` satisfies
  `FreeOverPowQuotient ℓ m`. The first condition is the previous lemma; the
  second follows from `hY` along `torsionQuotientRepRestrictIso` and
  `free_asModule_of_iso`.
- `freeOverPowQuotient_of_iso e hP`: for an isomorphism `e : P ≅ Q` in
  `Rep R G`, `FreeOverPowQuotient ℓ m P` implies `FreeOverPowQuotient ℓ m Q`.
  `Q` is killed by `ℓ ^ m` because multiplication by `ℓ ^ m` commutes with
  `e.inv` (`comp_powSMul`), so it equals `e.inv ≫ powSMul ℓ m P ≫ e.hom = 0`.
  The isomorphism between the representations over `R ⧸ (ℓ ^ m)` comes from
  the full and faithful restriction of scalars (`Functor.preimageIso`) applied
  to `torsionQuotientRepIso P _ ≪≫ e ≪≫ (torsionQuotientRepIso Q _).symm`, and
  freeness transfers along it.
- `freeOverPowQuotient_iff P`: `FreeOverPowQuotient ℓ m P` holds if and only
  if there is a representation `Y` over `R ⧸ (ℓ ^ m)`, free over
  `(R ⧸ (ℓ ^ m))[G]`, whose restriction of scalars to `R` is isomorphic to
  `P`. Forward: take `Y = torsionQuotientRep P _` and `torsionQuotientRepIso`.
  Backward: the two previous results.

## Invariants of compact inductions

Here `G` is a topological group, `H` and `K` are subgroups with `H` open
(`hH`), `H ≤ K` (`hHK`), `K` normal and `H` of finite index in `K`, and `I` is
a type.

- `freeOverPowQuotient_compactInducedInvariants hH hHK I`: the `K`-invariants
  of the compact induction from `H` of the trivial representation on
  `I →₀ R ⧸ (ℓ ^ m)`, as a representation of `G ⧸ K` over `R ⧸ (ℓ ^ m)`,
  restricted to `R`, satisfy `FreeOverPowQuotient ℓ m` in `Rep R (G ⧸ K)`.
  This is `freeOverPowQuotient_repRestrictScalars` applied to the published
  `Induction.compactInducedInvariants_free` over `R ⧸ (ℓ ^ m)`. With the
  published `homSystem_map_surjective_of_freeOverPowQuotient` and its
  companions, it gives the surjectivity and Mittag-Leffler statements for Hom
  systems whose sources are of this form.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312
(one-based PDF page 14; Worker 61 read the rendered scanned page): "Since
`C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective
for all `m`."

Harris's modules are modules over `𝒪/ℓ^m𝒪`, while the published Hom systems
of `ℓ`-divisible systems live in `Rep R G` with `R = 𝒪`. The published
`FreeOverPowQuotient` states Harris's freeness for an object of `Rep R G`.
This module shows that the predicate describes exactly the objects coming from
free modules over `(R ⧸ (ℓ ^ m))[G]` by restriction of scalars. Freeness
results proved over a ring `k`, such as the published
`compactInducedInvariants_free`, therefore apply with `k = R ⧸ (ℓ ^ m)`. In
our reading `𝒪_m = 𝒪/ℓ^m𝒪` is `R ⧸ (ℓ ^ m)` and `S(ẽ)/H_p` is `G` (or
`G ⧸ K` in the last section). As in the published FreeTorsionProjective and
PermutationInvariants modules, `G`, `K` and `H` in the last section would
correspond to `S(ẽ)`, `H_p` and a member of Harris's family `H(ẽ)`; this
correspondence is our interpretation.

The statements are standard facts about restriction of scalars along a
quotient ring. The formulation and all proofs are ours; the module is
derived.

## Scope

The module does not prove that Harris's modules `C^j_m(ẽ)^{H_p}` or
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are free over `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`; direct limits
are not treated. Everything concerns the categories `Rep` of representations
of abstract groups, not categories of smooth representations.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
