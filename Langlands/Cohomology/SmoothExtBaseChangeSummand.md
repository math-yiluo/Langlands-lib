# Extension of scalars on `Ext` groups of smooth representations: summands and compact induction

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.SmoothExtBaseChange` (`IsFreeOnFixedVectors`,
`HasFreeFixedBasis`, `HasProPFreeFixedBasis`, `smoothRepHom_mem_invariants`,
`isFreeOnFixedVectors_compactInduction`, `HasProPFreeFixedBasis.projective`,
`HasProPFreeFixedBasis.projective_smoothRepExtendScalars`,
`smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis`; Worker 61),
`Langlands.Cohomology.HyperextExtBaseChangeSummand` (`IsSummandOfFiniteSum`,
`IsSummandOfFiniteSum.of_prop`, `IsSummandOfFiniteSum.biproduct`,
`extBaseChangeMap_injective_of_hasResolutionBy_summand`,
`extBaseChangeMap_bijective_of_hasResolutionBy_summand`,
`extBaseChangeEquivOfHasResolutionBySummand`; Worker 61) and
`Langlands.Representation.Induction.PermutationModule`
(`Induction.permutation`, `Induction.smoothPermutation`,
`Induction.compactInductionTrivialIso`; Worker 61). Through these imports it
also uses `Langlands.Representation.Induction.OpenAdjunction`
(`Induction.smoothRestriction`, `Induction.smoothCompactInduction`,
`Induction.compactInductionAdjunction`, `Induction.unitFunction`,
`Induction.eval_unitFunction`; Worker 61),
`Langlands.Representation.Induction.Definitions` (`Induction.eval`;
Worker 61), `Langlands.Cohomology.HyperextExtBaseChange` (`HasResolutionBy`,
`extBaseChangeMap_zero_bijective_iff`; Worker 61),
`Langlands.Cohomology.HyperextScalarExtension` (`smoothExtBaseChangeMap`,
`smoothRepExtendScalars_isSemilinear`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension`
(`smoothRepExtendScalars`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.PermutationProjective`
(`smoothTrivialFunctor`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.ProPInvariants` (`IsProPSubgroup`;
Worker 61) and `Langlands.Cohomology.ProPInvariants.Statement`
(`ProPInvariantsExactStatement`; Worker 3).

The Library's `SmoothExtBaseChange` proves that, for a localization `S` of `R`,
the comparison map
`smoothExtBaseChangeMap R S G X Y n : S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)`
of smooth representations is injective or bijective when `X` has a resolution
by representations free of finite rank on vectors fixed by pro-`p` subgroups
(`HasProPFreeFixedBasis p`), for `p` invertible in `R` and assuming the
Library's `ProPInvariantsExactStatement`. Its only examples are the compact
inductions `c-Ind_H^G M` of free modules of finite rank with trivial action of
an open pro-`p` subgroup `H`. The Library's `HyperextExtBaseChangeSummand`
extends the general dimension-shifting theorems to resolutions by direct
summands of finite sums.

This module combines the two and enlarges the class of examples:

- compact induction `c-Ind_S^G` from an open subgroup `S` sends representations
  of `S` free on vectors fixed by `H ≤ S` to representations of `G` free on
  `H`-fixed vectors, and sends summands of finite sums of such representations
  to summands of finite sums;
- the permutation representation of `G` on `G ⧸ H →₀ M`, for `H` open and `M`
  free, is free on `H`-fixed vectors;
- hence `c-Ind_S^G` of the permutation representation of `S` on `S ⧸ H →₀ M`,
  for `H ≤ S` open and pro-`p` and `M` free of finite rank, and finite
  biproducts of such representations, are in the class (respectively, are
  summands of finite sums of objects in the class);
- the comparison theorems hold for resolutions by summands of finite sums of
  representations in `HasProPFreeFixedBasis p`.

The existence of the resolutions remains a hypothesis.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`.

## Conventions

As in `SmoothExtBaseChange`: `SmoothRep.{uR, uG, w} R G` is the Library's
category of smooth representations of `G` on `R`-modules with carriers in
universe `w`; for `A : SmoothRep R G` and a subgroup `H` of `G`,
`A^H = Representation.invariants (A.representation.comp H.subtype)` is the
`R`-submodule of `H`-fixed vectors; `SmoothRep.hom f` is the underlying
intertwining map of a morphism `f`; `Ext^n_G(X, Y)` is Mathlib's
`Abelian.Ext.{t} X Y n`; `E = smoothRepExtendScalars.{max uS w} R S G` is the
Library's extension of scalars `X ↦ S ⊗[R] X` and
`hE = smoothRepExtendScalars_isSemilinear.{max uS w} R S G`.
`IsFreeOnFixedVectors H x` (Library) says that the vectors `x i ∈ P^H` are free
on `H`-fixed vectors: morphisms `P ⟶ Y` are determined by their values at the
`x i`, and every family `y i ∈ Y^H` is the family of values of a morphism;
`HasFreeFixedBasis H P` asks for such a family indexed by `Fin n` for some `n`;
`HasProPFreeFixedBasis p P` asks for `HasFreeFixedBasis H P` for some subgroup
`H` with `IsProPSubgroup p H`. `IsSummandOfFiniteSum Q X` (Library) says that
there are a finite type `ι`, objects `P i` with `Q (P i)` and morphisms
`a i : X ⟶ P i`, `b i : P i ⟶ X` with `∑ i, a i ≫ b i = 𝟙 X`.

For a subgroup `S` of `G`, `Induction.smoothCompactInduction.{uR, uG, uV} R S :
SmoothRep.{uR, uG, max uG uV} R S ⥤ SmoothRep.{uR, uG, max uG uV} R G` is the
Library's compact induction `c-Ind_S^G`, `Induction.smoothRestriction R S` is
restriction to `S`, and for `hS : IsOpen (S : Set G)`,
`Induction.compactInductionAdjunction.{uR, uG, uV} S hS` is the Library's
adjunction `c-Ind_S^G ⊣ restriction` (Frobenius reciprocity); its unit at `V`
is the `S`-equivariant map `u_V : V → c-Ind_S^G V` sending `v` to the function
supported on `S` with value `S(s) v` at `s ∈ S`. For a subgroup `H` of `G`,
`H.subgroupOf S` is Mathlib's subgroup `{s ∈ S | (s : G) ∈ H}` of `S`.

For an open subgroup `H` and an `R`-module `M`,
`Induction.smoothPermutation R M H hH` is the Library's smooth permutation
representation of `G` on `G ⧸ H →₀ M` (finitely supported functions on the
left cosets, `(g • φ)(x) = φ(g⁻¹ • x)`), and
`Induction.compactInductionTrivialIso R M H hH` is the Library's isomorphism
from `c-Ind_H^G` of the trivial representation of `H` on `M` to it, sending a
function `f` to the function `y H ↦ f(y⁻¹)`.

## Additive functors and isomorphisms

Section `Map` takes preadditive categories `C`, `D` and `Q : C → Prop`,
`Q' : D → Prop` (implicit). Section `Iso` takes a commutative ring
`R : Type uR` and a group `G : Type uG` with a topology (implicit); the
representations are in `SmoothRep.{uR, uG, w} R G`.

| Declaration | Statement |
| --- | --- |
| `IsSummandOfFiniteSum.map F hF hX` | For an additive functor `F : C ⥤ D` (`[F.Additive]`), `hF : ∀ P, Q P → Q' (F.obj P)` and `hX : IsSummandOfFiniteSum Q X`: `IsSummandOfFiniteSum Q' (F.obj X)`. |
| `IsFreeOnFixedVectors.of_iso e hx` | For an isomorphism `e : P ≅ P'`, `x : ι → P` and `hx : IsFreeOnFixedVectors H x`: `IsFreeOnFixedVectors H (fun i => SmoothRep.hom e.hom (x i))`. |
| `HasFreeFixedBasis.of_iso e hP` | For `e : P ≅ P'` and `hP : HasFreeFixedBasis H P`: `HasFreeFixedBasis H P'`. |
| `HasProPFreeFixedBasis.of_iso e hP` | For `e : P ≅ P'` and `hP : HasProPFreeFixedBasis p P`: `HasProPFreeFixedBasis p P'`. |

Proofs.

- `IsSummandOfFiniteSum.map`: the same index type with `F.obj (P i)`,
  `F.map (a i)` and `F.map (b i)`; then
  `∑ i, F.map (a i) ≫ F.map (b i) = F.map (∑ i, a i ≫ b i) = F.map (𝟙 X) =
  𝟙 (F.obj X)` (Mathlib's `Functor.map_comp`, `Functor.map_sum`,
  `Functor.map_id`).
- `IsFreeOnFixedVectors.of_iso`: the vectors `e.hom (x i)` are `H`-fixed by
  `smoothRepHom_mem_invariants`. If `f, g : P' ⟶ Y` agree at all
  `e.hom (x i)`, then `e.hom ≫ f` and `e.hom ≫ g` agree at all `x i`, so they
  are equal by `hom_ext` of `x`, and `f = g` (Mathlib's `cancel_epi`). Given
  `y i ∈ Y^H`, take `f : P ⟶ Y` with `f (x i) = y i` (`exists_hom` of `x`);
  then `e.inv ≫ f` sends `e.hom (x i)` to `f (x i) = y i` (`Iso.hom_inv_id`).
- `HasFreeFixedBasis.of_iso` and `HasProPFreeFixedBasis.of_iso`: the previous
  lemma with the same `n`, respectively the same subgroup.

## Compact induction

Section `CompactInduction` takes `R`, `G` as above with
`[IsTopologicalGroup G]`; from `isFreeOnFixedVectors_smoothCompactInduction` on
it also takes a subgroup `S` of `G` and `hS : IsOpen (S : Set G)` (both
explicit). The representations of `S` are in
`SmoothRep.{uR, uG, max uG uV} R S`, and `u_V` is the unit of
`Induction.compactInductionAdjunction.{uR, uG, uV} S hS` at `V`.

| Declaration | Statement |
| --- | --- |
| `isOpen_subgroupOf hH S` | For subgroups `H`, `S` of `G` with `hH : IsOpen (H : Set G)`: `H.subgroupOf S` is open in `S`. Needs only the topology on `G`. |
| `smoothRestriction_additive R S` | Instance: `Induction.smoothRestriction.{uR, uG, uV} R S` is additive. |
| `smoothCompactInduction_additive S hS` | For `hS : IsOpen (S : Set G)`: `Induction.smoothCompactInduction.{uR, uG, uV} R S` is additive. |
| `isFreeOnFixedVectors_smoothCompactInduction S hS hHS hx` | For a subgroup `H` with `hHS : H ≤ S`, `x : ι → V` and `hx : IsFreeOnFixedVectors (H.subgroupOf S) x`: `IsFreeOnFixedVectors H (fun i => SmoothRep.hom u_V (x i))` in `c-Ind_S^G V`. |
| `HasFreeFixedBasis.smoothCompactInduction S hS hHS hV` | For `hHS : H ≤ S` and `hV : HasFreeFixedBasis (H.subgroupOf S) V`: `HasFreeFixedBasis H (c-Ind_S^G V)`. |
| `HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction S hS hHp hHS hV` | Moreover for `hHp : IsProPSubgroup p H`: `HasProPFreeFixedBasis p (c-Ind_S^G V)`. |
| `IsSummandOfFiniteSum.smoothCompactInduction S hS hHp hHS hV` | For `hHp : IsProPSubgroup p H`, `hHS : H ≤ S` and `hV : IsSummandOfFiniteSum (HasFreeFixedBasis (H.subgroupOf S)) V`: `IsSummandOfFiniteSum (HasProPFreeFixedBasis p) (c-Ind_S^G V)`. |

`IsProPSubgroup p H` is a condition on `H` as a subgroup of `G`. The subgroup
`S` need not be compact.

Proofs.

- `isOpen_subgroupOf`: the underlying set of `H.subgroupOf S` is the preimage
  of `H` under the inclusion `S → G` (Mathlib's `Subgroup.coe_subgroupOf`),
  which is continuous.
- `smoothRestriction_additive`: restriction does not change the underlying
  maps, so `map_add` holds by definition.
- `smoothCompactInduction_additive`: a left adjoint of an additive functor
  between preadditive categories is additive (Mathlib's
  `Adjunction.left_adjoint_additive`), applied to the Library's
  `compactInductionAdjunction`.
- `isFreeOnFixedVectors_smoothCompactInduction`: for `h ∈ H` we have `h ∈ S`,
  `u_V` is `S`-equivariant (`Representation.IntertwiningMap.isIntertwining`)
  and `x i` is fixed by `h` viewed in `H.subgroupOf S`, so
  `h • u_V (x i) = u_V (h • x i) = u_V (x i)`. Under the adjunction a morphism
  `f : c-Ind_S^G V ⟶ Y` corresponds to the morphism
  `u_V ≫ restriction.map f : V ⟶ Y|_S` (`Adjunction.homEquiv`), whose value at
  `x i` is `f (u_V (x i))`. If `f` and `g` agree at all `u_V (x i)`, the
  corresponding morphisms agree at all `x i`, so they are equal by `hom_ext`
  of `x`, and `f = g` because `homEquiv` is injective. Given `y i ∈ Y^H`, the
  `y i` are fixed by `H.subgroupOf S` in the restriction `Y|_S`, since an
  element of `H.subgroupOf S` acts through its image in `G`; take
  `f : V ⟶ Y|_S` with `f (x i) = y i` (`exists_hom` of `x`). The morphism
  `homEquiv.symm f : c-Ind_S^G V ⟶ Y` corresponds to `f`
  (`Equiv.apply_symm_apply`), so it sends `u_V (x i)` to `f (x i) = y i`.
- `HasFreeFixedBasis.smoothCompactInduction`: the previous theorem for the
  witnessing family `x : Fin n → V`.
- `HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction`: the
  previous theorem, with `H` as the pro-`p` subgroup.
- `IsSummandOfFiniteSum.smoothCompactInduction`: `IsSummandOfFiniteSum.map` for
  the additive functor `c-Ind_S^G` (`smoothCompactInduction_additive`) and the
  previous theorem.

## Permutation representations

Section `Permutation` takes `R`, `G` as above with `[IsTopologicalGroup G]`, a
subgroup `H` and `hH : IsOpen (H : Set G)` (both explicit); `M : Type (max uG
uV)` is an `R`-module. Let
`u = (Induction.compactInductionAdjunction.{uR, uG, uV} H hH).unit.app
((smoothTrivialFunctor R H).obj (ModuleCat.of R M))` be the unit of Frobenius
reciprocity for the trivial representation of `H` on `M`, and `mk 1 : G ⧸ H`
the coset `H`.

| Declaration | Statement |
| --- | --- |
| `compactInductionTrivialIso_hom_unit H hH M v` | For `v : M`: `SmoothRep.hom (Induction.compactInductionTrivialIso R M H hH).hom (SmoothRep.hom u v) = Finsupp.single (mk 1) v`. |
| `isFreeOnFixedVectors_smoothPermutation H hH M b` | For a basis `b : Module.Basis ι R M` (any index type `ι`): `IsFreeOnFixedVectors H (fun i => Finsupp.single (mk 1) (b i))` in `Induction.smoothPermutation R M H hH`. |
| `hasProPFreeFixedBasis_smoothPermutation H hH hHp M b` | For `hHp : IsProPSubgroup p H` and a basis `b : Module.Basis (Fin n) R M`: `HasProPFreeFixedBasis p (Induction.smoothPermutation R M H hH)`. |
| `hasProPFreeFixedBasis_compactInduction_permutation S hHp hH hHS M b` | For subgroups `S`, `H` (`S` explicit, `H` implicit) with `hHp : IsProPSubgroup p H`, `hH : IsOpen (H : Set G)`, `hHS : H ≤ S`, and a basis `b : Module.Basis (Fin n) R M`: `HasProPFreeFixedBasis p` holds for `(Induction.smoothCompactInduction.{uR, uG, uV} R S).obj (Induction.smoothPermutation R M (H.subgroupOf S) (isOpen_subgroupOf hH S))`, the compact induction `c-Ind_S^G` of the permutation representation of `S` on `S ⧸ H.subgroupOf S →₀ M`. |
| `isSummandOfFiniteSum_biproduct_compactInduction_permutation S hHp hH hHS M b` | For a finite type `J : Type` (`[Fintype J]`), families of subgroups `S j`, `H j` (`S` explicit, `H` implicit) with `hHp : ∀ j, IsProPSubgroup p (H j)`, `hH : ∀ j, IsOpen (H j : Set G)`, `hHS : ∀ j, H j ≤ S j`, `R`-modules `M j : Type (max uG uV)` with bases `b j : Module.Basis (Fin (n j)) R (M j)`, and a biproduct (instance argument `[HasBiproduct _]`) of the family `X j = c-Ind_{S j}^G` of the permutation representation of `S j` on `S j ⧸ (H j).subgroupOf (S j) →₀ M j`: `IsSummandOfFiniteSum (HasProPFreeFixedBasis p) (⨁ X)`. |

The biproduct hypothesis can always be met: the Library's category of smooth
representations is abelian (`Langlands.Representation.Category.Abelian`), so
Mathlib's `Abelian.hasFiniteBiproducts` gives finite biproducts. The theorem
takes the biproduct as an argument to fix the object `⨁ X`.

Proofs.

- `compactInductionTrivialIso_hom_unit`: compare values at a coset `y H`
  (`Finsupp.ext`, `QuotientGroup.induction_on`). The isomorphism sends `u v` to
  the function `y H ↦ (u v)(y⁻¹)`, by definition. By the Library's
  `eval_unitFunction`, `(u v)(y⁻¹)` is `v` if `y⁻¹ ∈ H` (the action of `H` on
  `M` is trivial) and `0` otherwise. The value of `Finsupp.single (mk 1) v` at
  `y H` is `v` if `H = y H` and `0` otherwise (`Finsupp.single_apply`). Both
  conditions are equivalent to `y ∈ H` (`QuotientGroup.eq`).
- `isFreeOnFixedVectors_smoothPermutation`: the Library's
  `isFreeOnFixedVectors_compactInduction` for the trivial representation on
  `ModuleCat.of R M`, transported along `compactInductionTrivialIso` by
  `IsFreeOnFixedVectors.of_iso`; by the previous lemma the transported family
  is `fun i => Finsupp.single (mk 1) (b i)`.
- `hasProPFreeFixedBasis_smoothPermutation`: the previous theorem, with `H`
  as the pro-`p` subgroup.
- `hasProPFreeFixedBasis_compactInduction_permutation`: `S` is open because it
  contains the open subgroup `H` (Mathlib's `Subgroup.isOpen_mono`), and
  `H.subgroupOf S` is open in `S` (`isOpen_subgroupOf`).
  `isFreeOnFixedVectors_smoothPermutation`, for the group `S` and its open
  subgroup `H.subgroupOf S`, gives `HasFreeFixedBasis (H.subgroupOf S)` for
  the permutation representation of `S`, and
  `HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction` applies.
- `isSummandOfFiniteSum_biproduct_compactInduction_permutation`: each `X j`
  satisfies `HasProPFreeFixedBasis p` by the previous theorem, hence is a
  summand of a finite sum (`IsSummandOfFiniteSum.of_prop`), and the Library's
  `IsSummandOfFiniteSum.biproduct` applies.

## Localization

Section `Localization` takes `R`, `G` as above with `[IsTopologicalGroup G]`,
a commutative `R`-algebra `S : Type uS` and a submonoid `M` of `R` with
`[IsLocalization M S]` (`S` and `M` explicit), `[Module.Flat R S]`,
`[HasExt.{t} (SmoothRep.{uR, uG, max uS w} R G)]`,
`[HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)]` and
`Y : SmoothRep.{uR, uG, max uS w} R G` (explicit); `X` is implicit, and
`hP : ProPInvariantsExactStatement.{uG, uR, max uS w}` and
`hR : IsUnit (p : R)` are explicit. As in `SmoothExtBaseChange`, flatness holds
for every localization (Mathlib's `IsLocalization.flat`); it is an argument
because the Library's `smoothExtBaseChangeMap` takes it. Write
`Q_p = IsSummandOfFiniteSum (HasProPFreeFixedBasis p)`.

| Declaration | Statement |
| --- | --- |
| `smoothExtBaseChangeMap_injective_of_hasResolutionBy_summand S M Y hP hR n hX` | For `hX : HasResolutionBy Q_p n X`: `smoothExtBaseChangeMap.{max uS w} R S G X Y n : S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(E.obj X, E.obj Y)` is injective. |
| `smoothExtBaseChangeMap_bijective_of_hasResolutionBy_summand S M Y hP hR n hX` | For `hX : HasResolutionBy Q_p (n + 1) X`: `smoothExtBaseChangeMap.{max uS w} R S G X Y n` is bijective. |
| `smoothExtBaseChangeEquivOfHasResolutionBySummand S M Y hP hR n hX` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Ext^n_G(X, Y) ≃ₗ[S] Ext^n_G(E.obj X, E.obj Y)` with underlying map `smoothExtBaseChangeMap.{max uS w} R S G X Y n`. A `def`. |
| `smoothExtBaseChangeEquivOfHasResolutionBySummand_apply S M Y hP hR n hX z` | Its value at `z` is `smoothExtBaseChangeMap.{max uS w} R S G X Y n z` (a `simp` lemma, by definition). |

`HasResolutionBy Q n X` (Library) holds when there is an exact sequence
`P_n → ⋯ → P_0 → X → 0` with all `Q P_i`.

Proofs. The Library's `extBaseChangeMap_injective_of_hasResolutionBy_summand`,
`extBaseChangeMap_bijective_of_hasResolutionBy_summand` and
`extBaseChangeEquivOfHasResolutionBySummand` for `F = E` and
`Q = HasProPFreeFixedBasis p`, with the Library's
`HasProPFreeFixedBasis.projective`,
`HasProPFreeFixedBasis.projective_smoothRepExtendScalars`, and
`extBaseChangeMap_zero_bijective_iff` combined with
`smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis`.
`smoothExtBaseChangeMap` is by definition the Library's `extBaseChangeMap E hE`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. That compact induction from an open subgroup preserves freeness on
fixed vectors is a direct consequence of Frobenius reciprocity. The
representations covered are modelled on the following passages of Harris 1999,
read in the rendered scans (the same passages as in `SmoothExtBaseChange` and
`HyperextExtBaseChangeSummand`):

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- Proof of Proposition 4.4, printed p.310 (one-based PDF page 12): "Since
  (recalling that `ẽ = (e, N, δ)`) (4.4.4)
  `Z^{i,j} = ⊕_{dim(e)=n-1-i} C^j(ẽ) = ⊕_{(e,δ)∈O_i} c-Ind_{S(ẽ)}^{GJ} C^j(ẽ)`
  is a sum of compactly induced modules, the argument goes through as before."
- Proof of Proposition 4.10, printed p.311 (one-based PDF page 13): "Recall
  that `C^j(ẽ)` has been chosen to be a direct limit of free
  `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies over a family of open
  subgroups of" `S(ẽ)`.
- Printed p.312 (one-based PDF page 14): "Since `C^j_m(ẽ)^{H_p}` and
  `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
  follows that the maps (4.10.3) are surjective for all `m`."

Interpretation (explanation only, not formalized). For a normal subgroup `H`
of `S`, a free `R[S ⧸ H]`-module of rank `n`, viewed as a representation of
`S`, is the permutation representation on `S ⧸ H →₀ R^n`; for `H` open and
pro-`p` in `GJ`, `hasProPFreeFixedBasis_compactInduction_permutation` covers
the compact induction `c-Ind_S^{GJ}` of such a module, with `R = 𝒪/ℓ^m𝒪`, and
`isSummandOfFiniteSum_biproduct_compactInduction_permutation` covers finite
direct sums of them, a finite analogue of the sums in (4.4.4). Unlike the
interpretation given in `SmoothExtBaseChange`, no transitivity of compact
induction is needed: compact induction from `S` is treated directly. Harris's
`C^j(ẽ)` are direct limits of such modules, his subgroups `H(ẽ)` need not be
pro-`p`, and his sums are indexed by orbits `O_i`; none of this is
formalized, and the module does not identify `G`, `S`, `H`, the modules or the
coefficient rings with Harris's objects.

## Scope

- `ProPInvariantsExactStatement` is an explicit hypothesis of the
  `Ext` comparison theorems; it is not proved in the Library.
- The existence of resolutions by summands of finite sums of representations
  in `HasProPFreeFixedBasis p` is a hypothesis. The representations of the
  previous sections are such summands (and have such resolutions of every
  length by the Library's `IsSummandOfFiniteSum.hasResolutionBy`); whether
  Harris's cohomology groups have such resolutions is not addressed.
- Direct limits, infinite sums and the passage to `𝒪`-coefficients (the limit
  over `m`) are not treated.
- The comparison map on `Hom` is known to be bijective only for a localization
  `S` of `R`, as in `SmoothExtBaseChange`.
- `HasExt` is a hypothesis; the results hold for each such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.310-312 (one-based PDF pages 12-14), read in the rendered scans.

Dependencies: `Langlands.Cohomology.SmoothExtBaseChange`,
`Langlands.Cohomology.HyperextExtBaseChangeSummand` and
`Langlands.Representation.Induction.PermutationModule`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
