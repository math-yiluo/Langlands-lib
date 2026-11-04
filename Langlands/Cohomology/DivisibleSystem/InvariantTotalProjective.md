# Relative projectivity of the terms of Harris's complexes `C_m^{•,H}`

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`
(the predicate `FreeOverPowQuotient` and
`powTorsionProjective_of_freeOverPowQuotient`), and through it on
`Langlands.Cohomology.DivisibleSystem.PowTorsionProjective`
(`TermwisePowTorsionProjective`, `powTorsionProjective_obj_of_adjunction`) and
`Langlands.Cohomology.DivisibleSystem.HomSurjective` (`PowTorsionProjective`
and the surjectivity and Mittag-Leffler lemmas for `homSystem` and
`homComplexSystem` of the HomSystem module); and on
`Langlands.Cohomology.DivisibleSystem.ProPInvariants`
(`proPSmoothGodementInvariantTotalSystem`), and through it on the InvariantTotal
module (`quotientInvariantsTotalSystem`, `smoothGodementInvariantTotalSystem`),
the Total module (`upFinTotalFunctor`, `totalSystem`, `standardTotalSystem`,
`groupStandardTotalSystem`) and the StandardResolution module (`standardPow`,
`indResBot`). From Mathlib it uses `HomologicalComplex₂.totalDesc`,
`HomologicalComplex₂.total.hom_ext`, the adjunctions `Rep.indResAdjunction` and
`Rep.resIndAdjunction`, and `Rep.trivialFunctor`. All names are in the
namespace `Langlands.Cohomology.DivisibleSystem`.

`PowTorsionProjective ℓ m P` (HomSurjective module) says that every morphism
from `P` to the target `Y` of an epimorphism `p : X ⟶ Y` with `X` killed by
`ℓ ^ m` lifts along `p`. The HomSurjective module proves the surjectivity of
the transitions of `T_m = Hom(T m, W m)` from this property of the source
alone. This module proves the property for the terms of the total complexes
`groupStandardTotalSystem` and hence for the Library's `C_m^{•,H}`, from the
same property of the underlying modules of the terms being resolved. It then
specializes the HomSurjective lemmas to these systems.

## Total complexes

- `powTorsionProjective_total_X`: in a preadditive category, let `K` be a
  double complex (`HomologicalComplex₂ C c₁ c₂`) with a total complex for
  `c₁₂`. If every term `(K.X i₁).X i₂` is projective relative to objects
  killed by `ℓ ^ m`, so is every term `(K.total c₁₂).X i₁₂`. Proof: lift each
  restriction `ιTotal ≫ g` to a summand, assemble the lifts with `totalDesc`,
  and compare summandwise with `total.hom_ext`.
- `powTorsionProjective_upFinTotalFunctor_obj_X`: for
  `K : HomologicalComplex₂ A (up ℕ) (down ℕ)` in an abelian category, the terms
  of `(upFinTotalFunctor A N).obj K` (the total complex of the rows `q < N`)
  have the property when the terms `(K.X q).X r` with `q < N` have it.
- `termwisePowTorsionProjective_totalSystem`: for an `ℓ`-divisible system `K`
  of such double complexes, `TermwisePowTorsionProjective (K.totalSystem N)`
  holds if, for all `m`, `q < N` and `r`, `((K.obj m).X q).X r` is projective
  relative to objects killed by `ℓ ^ m`.
- `termwisePowTorsionProjective_standardTotalSystem`: for an endofunctor `P`
  with `ε : P ⟶ 𝟭 A` (additive and preserving finite limits and colimits, as
  the Total module requires) and an `ℓ`-divisible system `K` of `ℕ`-graded
  cochain complexes, `TermwisePowTorsionProjective (K.standardTotalSystem N P ε)`
  holds if, for all `m`, `q < N` and `r`, `(standardPow P (r + 1)).obj ((K.obj m).X q)`
  has the property.

The hypotheses concern only the rows `q < N` that enter the total complexes.

## Induction, restriction and the trivial subgroup

`k` is a commutative ring and `Γ` a group; representations live in
`Rep.{max w u v} k Γ`.

- `powTorsionProjective_indFunctor_obj`: for a subgroup `S`, `Ind_S^Γ`
  preserves the property. It is left adjoint to restriction
  (`Rep.indResAdjunction`), and restriction is additive and preserves
  epimorphisms, so the PowTorsionProjective module's
  `powTorsionProjective_obj_of_adjunction` applies.
- `powTorsionProjective_resFunctor_obj`: for a subgroup `S` of finite index,
  `Res_S^Γ` preserves the property. It is left adjoint to induction
  (`Rep.resIndAdjunction`). Induction is additive, because it preserves binary
  products as a right adjoint, and it preserves epimorphisms as a left adjoint.
- `powTorsionProjective_iff_forget₂_of_subsingleton`: for a monoid `S` with at
  most one element, a representation `Y` has the property if and only if its
  underlying module does. `S` acts through its unit, so every linear map
  between underlying modules is equivariant. One direction uses
  `Rep.trivialFunctor` to carry epimorphisms and torsion objects of modules to
  representations.
- `powTorsionProjective_resFunctor_bot_obj_iff`: the restriction of `X` to the
  trivial subgroup `⊥` has the property if and only if the underlying module of
  `X` has it.
- `powTorsionProjective_indResBot_obj`: `Ind_1^Γ Res_1^Γ X` (the
  StandardResolution module's `indResBot`) has the property when the
  underlying module of `X` has it.
- `powTorsionProjective_forget₂_obj_of_freeOverPowQuotient`: the underlying
  module of `X` has the property when the restriction of `X` to `⊥` satisfies
  `FreeOverPowQuotient ℓ m`. That is, it is killed by `ℓ ^ m` and free over the
  group algebra `(R ⧸ (ℓ ^ m))[⊥]`. Mathematically this group algebra is
  `R ⧸ (ℓ ^ m)`, so the condition says that the underlying module is free over
  `R ⧸ (ℓ ^ m)`. That identification is not formalized.

Now `Γ` is finite.

- `powTorsionProjective_forget₂_obj`: if a representation has the property,
  so does its underlying module. Restriction to `⊥`, which has finite index,
  preserves the property.
- `powTorsionProjective_standardPow_indResBot_obj`: if the underlying module of
  `X` has the property, then every iterate
  `(standardPow (indResBot k Γ) (r + 1)).obj X = (Ind_1^Γ Res_1^Γ)^(r+1) X` has
  it. The proof is by induction on `r`, using the two previous lemmas.

## The hypothesis on the underlying modules

- `UnderlyingPowTorsionProjectiveBelow N K` (a definition, `Prop`-valued), for
  an `ℓ`-divisible system `K` of `ℕ`-graded cochain complexes in `Rep.{w} k Γ`:
  for every `m` and every `q < N`, the underlying module
  `(forget₂ (Rep k Γ) (ModuleCat k)).obj ((K.obj m).X q)` is projective
  relative to objects killed by `ℓ ^ m`.
- `underlyingPowTorsionProjectiveBelow_of_freeOverPowQuotient`: the predicate
  holds when the restrictions to `⊥` of all the terms `(K.obj m).X q` with
  `q < N` satisfy `FreeOverPowQuotient ℓ m`.

## The total complexes `groupStandardTotalSystem`

`Γ` is a finite group, `N : ℕ`, `K` an `ℓ`-divisible system of `ℕ`-graded
cochain complexes in `Rep.{max w u v} k Γ`, and
`hK : UnderlyingPowTorsionProjectiveBelow N K`.

- `termwisePowTorsionProjective_groupStandardTotalSystem`:
  `TermwisePowTorsionProjective (groupStandardTotalSystem N K)`.

For an `ℓ`-divisible system `W` of representations of `Γ`, with
`T_m(j) = Hom(C_m^j, W_m)` the HomSystem module's
`homSystem k ((groupStandardTotalSystem N K).degree j) W`:

- `groupStandardTotalSystem_degree_homSystem_map_surjective`: every
  transition `T_m(j) → T_{m'}(j)` (`m' ≤ m`) is surjective;
- `isMittagLeffler_groupStandardTotalSystem_degree_homSystem`: the inverse
  system of the `T_m(j)` satisfies the Mittag-Leffler condition;
- `groupStandardTotalSystem_degree_towerHomEval_surjective`: every morphism
  `C_n^j ⟶ W_n` is the level-`n` component of a morphism of the inverse
  systems.

For an `ℓ`-divisible system `W` of `ℤ`-graded cochain complexes of
representations of `Γ`, with `homComplexSystem k (groupStandardTotalSystem N K) W`
the inverse system of Hom complexes `Hom^•(C_m^•, W_m)`:

- `groupStandardTotalSystem_homComplexSystem_map_f_surjective`: its
  transitions are surjective in every degree;
- `isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval`: it
  satisfies the Mittag-Leffler condition in every degree;
- `groupStandardTotalSystem_homComplexLimit_π_f_surjective`: the limit
  projections are surjective in every degree.

Each lemma is the corresponding HomSurjective lemma applied to
`termwisePowTorsionProjective_groupStandardTotalSystem`.

## Harris's `C_m^{•,H}`

The systems are those of the InvariantTotal and ProPInvariants modules, with
their hypotheses. `H` is a normal subgroup of finite index of `G`, so
`G ⧸ H` is a finite group. In each case `hfree` is
`UnderlyingPowTorsionProjectiveBelow` of the `H`-invariants system being
resolved, so only the underlying modules of the `H`-invariant terms in
the rows that are totalized are constrained.

- A general system `K` of complexes of smooth representations, with the
  Invariants module's surjectivity hypothesis `hK`:
  `hfree : UnderlyingPowTorsionProjectiveBelow N (K.quotientInvariantsComplexes H hK)`.
  - `termwisePowTorsionProjective_quotientInvariantsTotalSystem`;
  - `quotientInvariantsTotalSystem_degree_homSystem_map_surjective` and
    `isMittagLeffler_quotientInvariantsTotalSystem_degree_homSystem`, for an
    `ℓ`-divisible system `W` in `Rep.{max w uR uG} R (G ⧸ H)`;
  - `isMittagLeffler_quotientInvariantsTotalSystem_homComplexSystem_eval`,
    for an `ℓ`-divisible system `W` of `ℤ`-graded cochain complexes there.
- The truncated smooth Godement resolutions (`h`, `T`, `D`, `hterm`, `hres` as
  in `smoothGodementInvariantTotalSystem`, all types in one universe `u`; `h`
  is a proof of Worker 3's unproved proposition
  `SmoothGodementZeroExactStatement R G X`):
  `hfree : UnderlyingPowTorsionProjectiveBelow (D + 2)
  (smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres)`.
  - `termwisePowTorsionProjective_smoothGodementInvariantTotalSystem`;
  - `smoothGodementInvariantTotalSystem_degree_homSystem_map_surjective`,
    `isMittagLeffler_smoothGodementInvariantTotalSystem_degree_homSystem`;
  - `isMittagLeffler_smoothGodementInvariantTotalSystem_homComplexSystem_eval`.
- The pro-`p` case (`hP : ProPInvariantsExactStatement`, an unproved
  proposition; `hH : IsProPSubgroup p H`; `hR : IsUnit (p : R)`; `hterm`,
  `hres` on compact sections without invariants), as in
  `proPSmoothGodementInvariantTotalSystem`: `hfree` on
  `proPSmoothGodementTruncatedQuotientInvariantSectionsSystem`, rows `q < D + 2`.
  - `termwisePowTorsionProjective_proPSmoothGodementInvariantTotalSystem`;
  - `proPSmoothGodementInvariantTotalSystem_degree_homSystem_map_surjective`,
    `isMittagLeffler_proPSmoothGodementInvariantTotalSystem_degree_homSystem`;
  - `isMittagLeffler_proPSmoothGodementInvariantTotalSystem_homComplexSystem_eval`.

These systems are abbreviations of `groupStandardTotalSystem`, so the
`towerHomEval` and limit-projection lemmas of the previous section also apply
to them.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed pp.304, 306 and 312 (one-based PDF
pages 6, 8 and 14). Worker 61 read all three pages in the rendered scanned
original.

1. Harris's claims. On p.304 an `ℓ`-divisible system is "a collection `{T_m}`
   of étale sheaves in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules" with maps `i`, `j`
   "such that `T_m` is free over `ℤ/ℓ^mℤ`" and (2.1) is exact. On p.306, "another snake lemma argument shows that `C_m^{•,H}`
   is an ℓ-divisible system of complexes of free `ℤ/ℓ^mℤ[S(e)/H]`-modules as
   `m` varies". Remark 2.9 says that "the free `ℤ/ℓ^mℤ[S(ẽ)/H]`-complexes
   `C_m^{•,H}` will also be used in the calculations". On p.312, in the proof
   of Proposition 4.10, he writes
   `T_m(j,ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`
   and continues: "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are
   both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3)
   are surjective for all `m`."
2. The route. Harris uses the freeness of both arguments. Here, as in the
   HomSurjective module, only the source needs a property, relative
   projectivity with respect to objects killed by `ℓ ^ m`, which free
   `(R ⧸ (ℓ ^ m))[Γ]`-modules have (FreeTorsionProjective module). The target
   `W` is any `ℓ`-divisible system: its transitions are epimorphisms and `W_m`
   is killed by `ℓ ^ m`. Harris's target `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` is not
   constructed. For the source, freeness of the terms over
   `(R ⧸ (ℓ ^ m))[G ⧸ H]` is replaced by relative projectivity of the terms.
   That property is derived from relative projectivity of the underlying
   modules of the `H`-invariant terms. Each term of the total complex is a
   finite coproduct of terms `(Ind_1^Γ Res_1^Γ)^(r+1) M`. `Ind_1^Γ` is left
   adjoint to an exact functor, and the property passes from a representation
   of a finite group to its underlying module.
3. The Hom. The Lean `homSystem` consists of morphisms in
   `Rep R (G ⧸ H)`, that is `R`-linear `G ⧸ H`-equivariant maps. Harris's
   `Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}` is taken between modules on which `H_p` acts trivially
   (he calls both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules), so it consists of the
   `𝒪/ℓ^m𝒪`-linear `S(ẽ)/H_p`-equivariant maps; for modules killed by `ℓ ^ m`,
   linearity over `R` and over `R ⧸ (ℓ ^ m)` agree. This comparison is a remark and is not formalized.
4. The Mittag-Leffler condition. Harris deduces the Mittag-Leffler condition
   for the complexes (4.10.2) from the finiteness of the right-hand side of the
   spectral sequence (4.9). Here the degreewise Mittag-Leffler condition of
   the Hom systems follows from the surjectivity of their transitions
   (HomSurjective module). Nothing is said about the cohomology of the Hom
   complexes or about (4.9).
5. The hypothesis `UnderlyingPowTorsionProjectiveBelow`. Harris's sheaves are
   free over `ℤ/ℓ^mℤ` (p.304), and he asserts the freeness of `C_m^{•,H}` over
   `ℤ/ℓ^mℤ[S(e)/H]` (p.306) without deriving it in detail. The module does not
   derive the property of the `H`-invariant terms from properties of the
   sheaves; it stays the explicit hypothesis `hK` or `hfree`. The sufficient
   condition `underlyingPowTorsionProjectiveBelow_of_freeOverPowQuotient`
   expresses freeness over `R ⧸ (ℓ ^ m)` through the group algebra of the
   trivial subgroup.
6. Stand-ins. `G`, `H`, the coefficient ring `R` and the compact sections of
   the truncated smooth Godement resolutions stand for `S(ẽ)`, `H_p`, `𝒪` (or
   `ℤ`) and Harris's `G_m^•(U(ẽ)_F̄)`, as in the InvariantTotal module. The
   resolution functor `Ind_1^Γ Res_1^Γ` over `R` stands for Harris's (2.4), as
   in the StandardResolution module.

The definition `UnderlyingPowTorsionProjectiveBelow` is internal: it names the
hypothesis of the lemmas. The lemmas formalize the step from projectivity of
the terms to the surjectivity of (4.10.3). Its mechanism is ours (adjunctions
and total complexes in place of freeness), and the hypothesis on the
underlying modules is ours.

## Scope

The module does not prove that the terms of `C_m^{•,H}` are free over
`(R ⧸ (ℓ ^ m))[G ⧸ H]`. It does not prove that the underlying modules of the
`H`-invariant terms are projective relative to objects killed by `ℓ ^ m` for
any actual system, and does not construct Harris's target
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`. It does not formalize the snake lemma argument of
p.306, the isomorphism `(R ⧸ (ℓ ^ m))[⊥] ≅ R ⧸ (ℓ ^ m)`, the identification of
Hom over `R` with Hom over `R ⧸ (ℓ ^ m)`, or the spectral sequences (4.9) and
(4.10.1).

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
