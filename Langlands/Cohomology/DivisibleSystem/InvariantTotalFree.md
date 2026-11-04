# Freeness of the terms of Harris's complexes `C_m^{•,H}` over `(R ⧸ (ℓ ^ m))[G ⧸ H]`

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.LevelProjective`
(`IsUnitMulUniformizerPow`, `DivisibleSystem.exists_free_generators_obj`), and through it on the
InvariantTotalProjective module and the systems `groupStandardTotalSystem` (Total module),
`quotientInvariantsTotalSystem`, `smoothGodementInvariantTotalSystem` (InvariantTotal module) and
`proPSmoothGodementInvariantTotalSystem` (ProPInvariants module); on
`Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit`
(`freeOverPowQuotient_of_equiv_permutation`) and
`Langlands.Cohomology.DivisibleSystem.FreeRestrictScalars` (`freeOverPowQuotient_iff`); through
them on the FreeTorsionProjective module (`FreeOverPowQuotient`,
`powTorsionProjective_of_freeOverPowQuotient`), the PowTorsionProjective module
(`TermwisePowTorsionProjective`), the StandardResolution module (`standardPow`, `indResBot`) and
the permutation representations `permutation` and `permutationCongr` of
`Langlands.Induction`. From Mathlib it uses `Representation.IndV`, `Representation.ind_mk`,
`Representation.IndV.hom_ext`, `TensorProduct.finsuppScalarLeft`,
`MonoidAlgebra.coeffLinearEquiv`, `Finsupp.curryLinearEquiv`,
`LinearMap.quotKerEquivOfSurjective`, `Rep.toModuleMonoidAlgebra`,
`ModuleCat.coprodIsoDirectSum`, `Module.Free.directSum`, `PreservesCoproduct.iso` and
`HomologicalComplex₂.toGradedObject.isColimitCofanMapObj`.

`FreeOverPowQuotient ℓ m P` (FreeTorsionProjective module) says that the representation `P` over
`R` is killed by `ℓ ^ m` and, as a module over the group algebra `(R ⧸ (ℓ ^ m))[G]`, is free. The
InvariantTotalProjective module proved only that the terms of `C_m^{•,H}` are projective relative
to objects killed by `ℓ ^ m`. This module proves `FreeOverPowQuotient ℓ m` for these terms when
`ℓ = u π ^ e` in `R` (`IsUnitMulUniformizerPow ℓ π e`: `u` a unit, `e ≥ 1`, `(π)` a maximal
ideal).

The declarations of the first two sections are in the namespace `Langlands.Cohomology`, except
`DivisibleSystem.freeOverPowQuotientModule_obj`; all other declarations are in
`Langlands.Cohomology.DivisibleSystem`.

## Free modules over `R ⧸ (ℓ ^ m)`

`R` is a commutative ring and `M` an `R`-module.

- `linearEquivFinsuppQuotient v I hsurj hker` (a definition): for a family `v : ι → M` whose
  linear combinations exhaust `M` (`hsurj`) and such that a linear combination
  `Finsupp.linearCombination R v c` vanishes if and only if every coefficient `c i` lies in the
  ideal `I` (`hker`), an `R`-linear equivalence `M ≃ₗ[R] (ι →₀ R ⧸ I)`. Both `M` and
  `ι →₀ R ⧸ I` are quotients of `ι →₀ R`, by the same kernel.
- `FreeOverPowQuotientModule R ℓ m M` (a definition, `Prop`-valued): there are a type `ι` in the
  universe of `M` and an `R`-linear equivalence `M ≃ₗ[R] (ι →₀ R ⧸ (ℓ ^ m))`. This is Harris's
  "free over `ℤ/ℓ^mℤ`" for `R`-modules, with `R ⧸ (ℓ ^ m)` in place of `ℤ/ℓ^mℤ`. The linear
  equivalence is over `R`; `R ⧸ (ℓ ^ m)`-linearity is not part of the statement, and no
  `Module.Free` instance over the quotient ring is constructed.
- `FreeOverPowQuotientModule.of_linearEquiv`: the predicate is invariant under `R`-linear
  equivalence.
- `DivisibleSystem.freeOverPowQuotientModule_obj`: for `IsUnitMulUniformizerPow ℓ π e` and an
  `ℓ`-divisible system `T` in `ModuleCat R`, every level `T.obj m` satisfies
  `FreeOverPowQuotientModule R ℓ m`. It applies `linearEquivFinsuppQuotient` to the generators of
  the LevelProjective module's `exists_free_generators_obj`, whose relations are exactly the
  coefficientwise multiples of `ℓ ^ m`.

## Induction from the trivial subgroup

`k` is a commutative ring, `Γ` a group and `ρ` a representation of the trivial subgroup
`⊥ : Subgroup Γ` on a `k`-module `A`.

- `coinvariantsKer_bot_eq_bot`: the coinvariant relations `τ g x - x` of a representation of `⊥`
  span the zero submodule.
- `indBotLinearEquiv ρ` (a definition): Mathlib's induced module
  `Representation.IndV (⊥ : Subgroup Γ).subtype ρ`, the quotient of `k[Γ] ⊗_k A` by these
  relations, is `k`-linearly equivalent to `Γ →₀ A`. The equivalence divides by the zero
  submodule, identifies `k[Γ] ⊗_k A` with `Γ →₀ A` (`TensorProduct.finsuppScalarLeft`), and
  reindexes by inversion on `Γ`.
- `indBotLinearEquiv_mk`: it sends the class of `γ ⊗ a` to `Finsupp.single γ⁻¹ a`.
- `indBotEquiv ρ` (a definition): the same map is an equivalence of representations between
  Mathlib's induced representation `ρ.ind (⊥ : Subgroup Γ).subtype` and the permutation
  representation `permutation k Γ Γ A` of `Γ` on `Γ →₀ A` by left multiplication. The inversion
  makes the action match: `h` sends `γ ⊗ a` to `γ h⁻¹ ⊗ a` in Mathlib's induction and
  `single γ⁻¹ a` to `single (h γ⁻¹) a` in the permutation representation.

## `Ind_1^Γ Res_1^Γ` and its iterates

`k` is a commutative ring, `Γ` a group, `V` a representation in `Rep.{max w u v} k Γ` and
`ℓ m : ℕ`. `indResBot k Γ` is the StandardResolution module's `Ind_1^Γ Res_1^Γ`, and
`standardPow P r` is the `r`-th iterate of an endofunctor `P`.

- `freeOverPowQuotient_indResBot_obj`: if the underlying module of `V` satisfies
  `FreeOverPowQuotientModule k ℓ m`, then `(indResBot k Γ).obj V` satisfies
  `FreeOverPowQuotient ℓ m`. Composing `indBotEquiv` with `permutationCongr` along
  `V ≃ₗ[k] (ι →₀ k ⧸ (ℓ ^ m))` gives an equivalence with the permutation representation on
  `Γ →₀ (ι →₀ k ⧸ (ℓ ^ m))`, and the FreeQuotientLimit module's
  `freeOverPowQuotient_of_equiv_permutation` applies.
- `freeOverPowQuotientModule_indResBot_obj`: the underlying module of `(indResBot k Γ).obj V`
  satisfies `FreeOverPowQuotientModule k ℓ m`, with index type `Γ × ι`
  (`Γ →₀ (ι →₀ k ⧸ (ℓ ^ m)) ≃ (Γ × ι →₀ k ⧸ (ℓ ^ m))` by `Finsupp.curryLinearEquiv`).
- `freeOverPowQuotientModule_standardPow_indResBot_obj`: by induction on `r`, the underlying
  module of every iterate `(standardPow (indResBot k Γ) r).obj V` satisfies
  `FreeOverPowQuotientModule k ℓ m`.
- `freeOverPowQuotient_standardPow_indResBot_obj`: every iterate
  `(standardPow (indResBot k Γ) (r + 1)).obj V = (Ind_1^Γ Res_1^Γ)^(r+1) V` satisfies
  `FreeOverPowQuotient ℓ m`.

## Finite coproducts and total complexes

`G` is a monoid.

- `toModuleMonoidAlgebra_additive` (an instance): Mathlib's functor `Rep.toModuleMonoidAlgebra`
  from `Rep S G` to modules over `S[G]` is additive.
- `free_asModule_sigma`: for a finite family `Y` of representations over a commutative ring `S`
  with a coproduct `∐ Y`, if every `Y j` is free over `S[G]`, so is `∐ Y`. The functor
  `Rep.toModuleMonoidAlgebra` carries `∐ Y` to the direct sum of the `Y j`
  (`PreservesCoproduct.iso`, `ModuleCat.coprodIsoDirectSum`), which is free
  (`Module.Free.directSum`).
- `freeOverPowQuotient_of_isColimit`: for a finite family `f` in `Rep R G` and a colimit cofan
  `c` of `f`, if every `f j` satisfies `FreeOverPowQuotient ℓ m`, so does `c.pt`. By
  `freeOverPowQuotient_iff` (FreeRestrictScalars module) each `f j` is the restriction of scalars
  of a representation `Y j` over `R ⧸ (ℓ ^ m)` free over `(R ⧸ (ℓ ^ m))[G]`; restriction of
  scalars is additive, so it carries `∐ Y`, free by `free_asModule_sigma`, to a coproduct of the
  `f j`, which is isomorphic to `c.pt`.
- `freeOverPowQuotient_total_X`: for a double complex `K : HomologicalComplex₂ (Rep R G) c₁ c₂`
  with a total complex for `c₁₂`, and a total degree `i₁₂` with finitely many pairs
  `(i₁, i₂)` mapping to it, if every term `(K.X i₁).X i₂` with `(i₁, i₂)` mapping to `i₁₂`
  satisfies `FreeOverPowQuotient ℓ m`, so does `(K.total c₁₂).X i₁₂`. The term is the point of
  the colimit cofan `HomologicalComplex₂.toGradedObject.isColimitCofanMapObj`.

## Termwise freeness

`R` is a commutative ring, `G` a monoid and `T` an `ℓ`-divisible system of `ℤ`-graded cochain
complexes in `Rep.{w} R G`.

- `TermwiseFreeOverPowQuotient T` (a definition, `Prop`-valued): for all `m` and `p`, the term
  `(T.obj m).X p` satisfies `FreeOverPowQuotient ℓ m`. This is Harris's "complexes of free
  `ℤ/ℓ^mℤ[S(e)/H]`-modules" (p.306), with `R ⧸ (ℓ ^ m)` in place of `ℤ/ℓ^mℤ` and `G` in place
  of `S(e)/H`.
- `TermwiseFreeOverPowQuotient.termwisePowTorsionProjective`: it implies the
  PowTorsionProjective module's `TermwisePowTorsionProjective T`, by
  `powTorsionProjective_of_freeOverPowQuotient`.

## The total complexes `groupStandardTotalSystem`

`k` is a commutative ring, `Γ` a finite group, `N : ℕ` and `K` an `ℓ`-divisible system of
`ℕ`-graded cochain complexes in `Rep.{max w u v} k Γ`.

- `termwiseFreeOverPowQuotient_groupStandardTotalSystem`: if, for every `m` and every `q < N`,
  the underlying module of `(K.obj m).X q` satisfies `FreeOverPowQuotientModule k ℓ m` (the
  hypothesis `hK`), then `TermwiseFreeOverPowQuotient (groupStandardTotalSystem N K)`. In total
  degree `n`, the term of level `m` is the finite coproduct of the terms
  `(standardPow (indResBot k Γ) (r + 1)).obj ((K.obj m).X q)` with `q < N`; the previous two
  sections apply.
- `termwiseFreeOverPowQuotient_groupStandardTotalSystem_of_isUnitMulUniformizerPow`: for
  `IsUnitMulUniformizerPow ℓ π e` in `k`, the same conclusion without `hK`. The underlying
  modules of the terms in degree `q` form the `ℓ`-divisible system of modules
  `(K.degree q).map (forget₂ (Rep k Γ) (ModuleCat k))` (the DivisibleSystem module's `degree`
  and `map`), and `freeOverPowQuotientModule_obj` applies to it.

## Harris's `C_m^{•,H}`

The systems are those of the InvariantTotal and ProPInvariants modules, with their hypotheses;
`H` is a normal subgroup of finite index of `G`, so that `G ⧸ H` is finite. In each case
`ℓ = u π ^ e` in `R` (`hℓ : IsUnitMulUniformizerPow ℓ π e`), and the conclusion is that every
term of every level is free over `(R ⧸ (ℓ ^ m))[G ⧸ H]`.

- `termwiseFreeOverPowQuotient_quotientInvariantsTotalSystem_of_isUnitMulUniformizerPow`: for
  an `ℓ`-divisible system `K` of `ℕ`-graded cochain complexes of smooth representations of a
  topological group `G` and the Invariants module's surjectivity hypothesis `hK`,
  `TermwiseFreeOverPowQuotient (K.quotientInvariantsTotalSystem N H hK)`.
- `termwiseFreeOverPowQuotient_smoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow`:
  for the truncated smooth Godement resolutions (`h`, `T`, `D`, `hterm`, `hres` as in
  `smoothGodementInvariantTotalSystem`, all types in one universe `u`; `h` is a proof of Worker
  3's unproved proposition `SmoothGodementZeroExactStatement R G X`),
  `TermwiseFreeOverPowQuotient (smoothGodementInvariantTotalSystem h T D H hterm hres)`.
- `termwiseFreeOverPowQuotient_proPSmoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow`:
  in the pro-`p` case (`hP : ProPInvariantsExactStatement`, an unproved proposition;
  `hH : IsProPSubgroup p H`; `hR : IsUnit (p : R)`; `hterm`, `hres` on compact sections without
  invariants), `TermwiseFreeOverPowQuotient
  (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres)`.

Each is `termwiseFreeOverPowQuotient_groupStandardTotalSystem_of_isUnitMulUniformizerPow` for the
system of `H`-invariants being resolved, since the three systems are abbreviations of
`groupStandardTotalSystem`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed pp.304 and 306 (one-based PDF pages 6 and 8). Worker
61 read both pages in the rendered scanned original for the LevelProjective and
InvariantTotalProjective modules; the quotations below are those of these modules.

1. Harris's claims. On p.304 an `ℓ`-divisible system is "a collection `{T_m}` of étale sheaves
   in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules" with maps `i`, `j` "such that `T_m` is free over `ℤ/ℓ^mℤ`"
   and (2.1) is exact. On p.306, "another snake lemma argument shows that `C_m^{•,H}` is an
   ℓ-divisible system of complexes of free `ℤ/ℓ^mℤ[S(e)/H]`-modules as `m` varies". Remark 2.9
   says that "the free `ℤ/ℓ^mℤ[S(ẽ)/H]`-complexes `C_m^{•,H}` will also be used in the
   calculations".
2. What is proved. `FreeOverPowQuotientModule` is Harris's freeness over `ℤ/ℓ^mℤ` of p.304, and
   `TermwiseFreeOverPowQuotient` his freeness over `ℤ/ℓ^mℤ[S(e)/H]` of p.306, with `R ⧸ (ℓ ^ m)`
   in place of `ℤ/ℓ^mℤ` and `G ⧸ H` in place of `S(e)/H`. The module proves the freeness of the
   terms of the Library's `C_m^{•,H}`. The `ℓ`-divisibility of `C_m^{•,H}` as `m` varies is the
   Total module's construction and is not reproved here.
3. The route. Harris gives a snake lemma argument, which is not formalized. Here the terms of
   `C_m^{•,H}` are finite coproducts of the representations `(Ind_1^Γ Res_1^Γ)^(r+1) M` with
   `Γ = G ⧸ H` and `M` an `H`-invariant term killed by `ℓ ^ m`. `Ind_1^Γ A` is the permutation
   module `Γ →₀ A` (`indBotEquiv`), free over `(R ⧸ (ℓ ^ m))[Γ]` when `A` is free over
   `R ⧸ (ℓ ^ m)`, and finite coproducts of free modules are free. The freeness of the
   underlying modules of the `H`-invariant terms over `R ⧸ (ℓ ^ m)` comes from the axioms of
   `ℓ`-divisible systems through the LevelProjective module; for this, the `H`-invariant terms
   of each degree form an `ℓ`-divisible system, which the Invariants and InvariantTotal modules
   construct under their surjectivity hypotheses. The StandardResolution module describes
   `indResBot` as `k[Γ] ⊗_k M` and calls its identification with Harris's
   `ℤ_ℓ[S(ẽ)/H] ⊗_{ℤ_ℓ} M` "not formalized"; `indBotEquiv` formalizes the identification of
   `Ind_1^Γ` with the permutation module (item 5 of that module's interpretation), not the
   comparison with Harris's notation.
4. Coefficients. The ring hypothesis `IsUnitMulUniformizerPow ℓ π e` is that of the
   LevelProjective module: it covers Harris's `ℤ/ℓ^mℤ` via `ℤ` or `ℤ_[p]` with `ℓ = p`, and a
   discrete valuation ring with an irreducible element in which `ℓ` is a nonzero nonunit; Harris's
   `𝒪` and its discrete valuation ring instance are not constructed.
5. Stand-ins. `G`, `H`, the coefficient ring `R` and the compact sections of the truncated smooth
   Godement resolutions stand for `S(ẽ)`, `H` (or `H_p`), `𝒪` (or `ℤ`) and Harris's
   `G_m^•(U(ẽ)_F̄)`, as in the InvariantTotal module. The resolution functor `Ind_1^Γ Res_1^Γ`
   over `R` stands for Harris's (2.4), as in the StandardResolution module.

The definitions `FreeOverPowQuotientModule` and `TermwiseFreeOverPowQuotient` render Harris's
freeness conditions; `linearEquivFinsuppQuotient`, `indBotLinearEquiv` and `indBotEquiv` are
standard constructions supplied here. The proofs are ours.

## Scope

The module proves freeness only under `IsUnitMulUniformizerPow ℓ π e`, or, for
`groupStandardTotalSystem`, under the explicit hypothesis `hK` on the rows `q < N`. It keeps
the hypotheses of the parent systems: finiteness of `Γ`, normality and finite index of `H`, the
surjectivity hypotheses `hK`, `hterm`, `hres` on `H`-invariants, the unproved propositions
`SmoothGodementZeroExactStatement` and `ProPInvariantsExactStatement`, and `hH`, `hR` in the
pro-`p` case. It does not treat sheaves, does not formalize Harris's snake lemma argument, and
constructs no `Module.Free` instance over `R ⧸ (ℓ ^ m)` (the freeness over `R ⧸ (ℓ ^ m)` is the
`R`-linear equivalence of `FreeOverPowQuotientModule`). It proves nothing about the cohomology of
`C_m^{•,H}`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
