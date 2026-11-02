# Free invariants of smooth representations and the smooth `Ext` comparison class

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.SmoothExtBaseChangeSummand` (`HasFreeFixedBasis.of_iso`,
`isOpen_subgroupOf`,
`HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction`,
`isFreeOnFixedVectors_smoothPermutation`; Worker 61) and
`Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit`
(`Induction.invariantsInflation`, `Induction.permutationQuotientEquiv`,
`Induction.IsFreeOnInvariants`, `Induction.IsFreeLimit`,
`Induction.IsFreeLimit.isFreeOnInvariants_of_isOpen`; Worker 61). Through
these imports it also uses `Langlands.Cohomology.SmoothExtBaseChange`
(`IsFreeOnFixedVectors`, `HasFreeFixedBasis`, `HasProPFreeFixedBasis`;
Worker 61), `Langlands.Cohomology.HyperextExtBaseChangeSummand`
(`IsSummandOfFiniteSum`, `IsSummandOfFiniteSum.of_prop`,
`IsSummandOfFiniteSum.biproduct`; Worker 61),
`Langlands.Representation.Induction.PermutationModule`
(`Induction.permutation`, `Induction.smoothPermutation`; Worker 61),
`Langlands.Representation.Induction.OpenAdjunction`
(`Induction.smoothCompactInduction`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.ProPInvariants` (`IsProPSubgroup`;
Worker 61), `Langlands.Representation.Category.Basic` (`SmoothRep`,
`SmoothRep.of`, `SmoothRep.ofHom`, `SmoothRep.hom`, `SmoothRep.mkIso`) and
`Langlands.Representation.Smooth.Definitions` (`Langlands.IsSmooth`).

The Library's `SmoothExtBaseChangeSummand` shows that compact inductions
`c-Ind_S^G` of permutation representations of `S` on `S ⧸ H →₀ M`, for `H ≤ S`
open and pro-`p` and `M` free of finite rank, are free of finite rank on
vectors fixed by a pro-`p` subgroup (`HasProPFreeFixedBasis p`), the class
used by its comparison theorems for extension of scalars on `Ext` groups of
smooth representations, and that finite biproducts of them are summands of
finite sums of objects in that class. The Library's `FreeQuotientLimit`
defines Harris's free `k[G ⧸ H]`-modules on invariants
(`IsFreeOnInvariants`) and direct limits of them (`IsFreeLimit`), for
representations without topology.

This module connects the two:

- for an open normal subgroup `H` of `G`, the `H`-invariants of a smooth
  representation `V` form a smooth representation of `G`
  (`smoothInvariantsInflation`), with an inclusion into `V`;
- if these invariants are a free `R[G ⧸ H]`-module (`IsFreeOnInvariants`) that
  is finitely generated over `R`, the index type can be taken finite, the
  invariants are isomorphic to the permutation representation of `G` on
  `G ⧸ H →₀ (I →₀ R)`, and they are free of finite rank on `H`-fixed vectors;
- for `H ≤ S` with `H` open and pro-`p` in `G` and normal in `S`, the compact
  induction `c-Ind_S^G` of the `H`-invariants of such a representation of `S`
  is in `HasProPFreeFixedBasis p`, also when the representation of `S` is a
  direct limit of free modules (`IsFreeLimit`) for open normal subgroups
  shrinking to the identity; finite biproducts of such compact inductions are
  summands of finite sums of objects in that class.

## Conventions

`SmoothRep.{uR, uG, w} R G` is the Library's category of smooth
representations of a topological group `G` on `R`-modules with carriers in
universe `w`; `SmoothRep.of ρ hρ` bundles a representation `ρ` with a proof
`hρ : IsSmooth ρ`, `SmoothRep.ofHom f` makes an intertwining map a morphism,
`SmoothRep.hom f` is the intertwining map of a morphism `f`, and
`SmoothRep.mkIso e` is the isomorphism given by an equivariant linear
equivalence `e`. `IsSmooth ρ` (Library) says that every vector is fixed by an
open subgroup. For a subgroup `H` of `G`,
`ρ^H = Representation.invariants (ρ.comp H.subtype)` is the `R`-submodule of
`H`-fixed vectors. For a normal subgroup `H`, Mathlib's
`ρ.quotientToInvariants H` is the representation of `G ⧸ H` on `ρ^H`, and the
Library's `invariantsInflation ρ H` is its pullback to `G`.

`Induction.permutation R X Y M` is the Library's permutation representation of
a group `X` acting on a set `Y` on `Y →₀ M`, with
`(g • φ)(y) = φ(g⁻¹ • y)`; `Induction.smoothPermutation R M H hH`, for an open
subgroup `H` (`hH : IsOpen (H : Set G)`), is the smooth permutation
representation of `G` on `G ⧸ H →₀ M`. The Library's
`IsFreeOnInvariants ρ R H`, for a normal subgroup `H`, says that there are a
type `I` and an equivariant linear equivalence of `ρ.quotientToInvariants H`
with `permutation R (G ⧸ H) (G ⧸ H) (I →₀ R)`, the free `R[G ⧸ H]`-module
`⊕_I R[G ⧸ H]`. The Library's `IsFreeLimit ρ R K`, for a family `K : ι →
Subgroup G` of normal subgroups, says that the family is directed, that every
vector is fixed by some `K i`, and that `IsFreeOnInvariants ρ R (K i)` holds
for every `i`.

As in `SmoothExtBaseChangeSummand`: `IsFreeOnFixedVectors H x` (Library) says
that the vectors `x i ∈ P^H` are free on `H`-fixed vectors: morphisms
`P ⟶ Y` are determined by their values at the `x i`, and every family
`y i ∈ Y^H` is the family of values of a morphism; `HasFreeFixedBasis H P` asks for such a family indexed by
`Fin n` for some `n`; `HasProPFreeFixedBasis p P` asks for
`HasFreeFixedBasis H P` for some subgroup `H` with `IsProPSubgroup p H`
(Library: `H` is compact and totally disconnected and its quotients by open
normal subgroups are `p`-groups, `p` prime). `IsSummandOfFiniteSum Q X`
(Library) says that there are a finite type `ι`, objects `P i` with `Q (P i)`
and morphisms `a i : X ⟶ P i`, `b i : P i ⟶ X` with
`∑ i, a i ≫ b i = 𝟙 X`. For a subgroup `S` of `G`,
`Induction.smoothCompactInduction.{uR, uG, uV} R S :
SmoothRep.{uR, uG, max uG uV} R S ⥤ SmoothRep.{uR, uG, max uG uV} R G` is the
Library's compact induction `c-Ind_S^G`, and `H.subgroupOf S` is Mathlib's
subgroup `{s ∈ S | (s : G) ∈ H}` of `S`.

## Smooth representations on invariants

Namespace `Langlands.Induction`. Section `Smooth` takes a commutative ring
`R : Type uR` and a group `G : Type uG` with a topology (implicit), a normal
subgroup `H` of `G` (`[H.Normal]`) and `hH : IsOpen (H : Set G)`; from
`smoothInvariantsInflationIso` on it also assumes `[IsTopologicalGroup G]`.

| Declaration | Statement |
| --- | --- |
| `isSmooth_invariantsInflation ρ H hH` | For a representation `ρ` of `G` on an `R`-module `V : Type uV`: `IsSmooth (invariantsInflation ρ H)`. |
| `smoothInvariantsInflation V H hH` | For `V : SmoothRep.{uR, uG, uV} R G`: the smooth representation `SmoothRep.of (invariantsInflation V.representation H) _` of `G` on `V^H`, in `SmoothRep.{uR, uG, uV} R G`. An `abbrev`. |
| `smoothInvariantsInflationι V H hH` | The morphism `smoothInvariantsInflation V H hH ⟶ V` whose intertwining map is the inclusion `V^H → V` (Mathlib's `quotientToInvariants_lift`). A `def`. |
| `smoothInvariantsInflationι_apply V H hH v` | `SmoothRep.hom (smoothInvariantsInflationι V H hH) v` is the underlying vector of `v` in `V` (a `simp` lemma, by definition). |
| instance `Mono (smoothInvariantsInflationι V H hH)` | The inclusion is a monomorphism. |
| `smoothInvariantsInflationIso V H hH e` | For `V : SmoothRep.{uR, uG, max uG uM} R G`, an `R`-module `M : Type (max uG uM)` (implicit) and an equivariant linear equivalence `e` of `V.representation.quotientToInvariants H` with `permutation R (G ⧸ H) (G ⧸ H) M`: the isomorphism `smoothInvariantsInflation V H hH ≅ smoothPermutation R M H hH` with the same underlying linear equivalence. A `def`. |

Proofs.

- `isSmooth_invariantsInflation`: a vector of `ρ^H` is fixed by every element
  of `H` by definition, and `H` is open.
- `smoothInvariantsInflationι_apply`: by definition (`rfl`).
- The `Mono` instance: if `f ≫ ι = g ≫ ι`, then for every `v` the vectors
  `f v` and `g v` have the same image in `V`; elements of `V^H` are equal when
  their underlying vectors are, so `f = g` (extensionality of morphisms).
- `smoothInvariantsInflationIso`: `SmoothRep.mkIso` of the composite of `e`,
  viewed as an equivalence of representations of `G` through `G → G ⧸ H`
  (each `g` acts through its coset), with the Library's
  `permutationQuotientEquiv R H M`, which identifies the permutation
  representation of `G ⧸ H` on `G ⧸ H →₀ M`, pulled back to `G`, with the
  permutation representation of `G` on `G ⧸ H →₀ M`.

## Finite rank

Section `FiniteRank` takes `R`, `G` as above without topology, a
representation `ρ` of `G` on `V : Type uV` and a normal subgroup `H`.

| Declaration | Statement |
| --- | --- |
| `IsFreeOnInvariants.exists_finite h` | For `h : IsFreeOnInvariants ρ R H` and `[Module.Finite R ρ^H]`: there are a type `I : Type uV` with `Finite I` and an equivariant linear equivalence of `ρ.quotientToInvariants H` with `permutation R (G ⧸ H) (G ⧸ H) (I →₀ R)`. |

Proof. If `R` is the zero ring, every `R`-module is trivial (Mathlib's
`Module.subsingleton`), and `I = PEmpty` works with
`LinearEquiv.ofSubsingleton`. Otherwise take the type `I` and equivalence `e`
given by `h`. The module `G ⧸ H →₀ I →₀ R` is finite over `R`, being
isomorphic to `ρ^H` (`Module.Finite.equiv`); evaluation at the coset `H`
(`Finsupp.lapply`) is a surjection onto `I →₀ R`, which is therefore finite
(`Module.Finite.of_surjective`); and a free module of finite rank over a
nonzero commutative ring has finite bases, so `I` is finite (Mathlib's
`Module.Finite.finite_basis` for `Finsupp.basisSingleOne`).

## Free invariants and compact induction

Namespace `Langlands.Cohomology.HyperextScalarExtension` (the namespace of the
comparison theorems); the theorems named `IsFreeOnInvariants.…` and
`IsFreeLimit.…` are declared in namespace `Langlands.Induction`, for dot
notation. Section `FreeInvariants` takes `R`, `G` as above with
`[IsTopologicalGroup G]`. The smooth representations are in
`SmoothRep.{uR, uG, max uR uG uV}`, the universe in which
`G ⧸ H →₀ (I →₀ R)` lives for `I : Type (max uR uG uV)`; compact induction is
`Induction.smoothCompactInduction.{uR, uG, max uR uV}`. `p : ℕ` is implicit.
For subgroups `H ≤ S`, `hHS : H ≤ S`, `X_S(V)` denotes
`(Induction.smoothCompactInduction R S).obj (smoothInvariantsInflation V
(H.subgroupOf S) (isOpen_subgroupOf hH S))`, the compact induction
`c-Ind_S^G` of the `H`-invariants of a smooth representation `V` of `S`.

| Declaration | Statement |
| --- | --- |
| `hasFreeFixedBasis_smoothInvariantsInflation V H hH e` | For a normal subgroup `H` with `hH : IsOpen (H : Set G)`, a finite type `I : Type (max uR uG uV)` and an equivariant linear equivalence `e` of `V.representation.quotientToInvariants H` with `permutation R (G ⧸ H) (G ⧸ H) (I →₀ R)`: `HasFreeFixedBasis H (smoothInvariantsInflation V H hH)`. |
| `IsFreeOnInvariants.hasFreeFixedBasis hH h` | For `H` normal and open, `h : IsFreeOnInvariants V.representation R H` and `[Module.Finite R V^H]`: `HasFreeFixedBasis H (smoothInvariantsInflation V H hH)`. |
| `IsFreeOnInvariants.hasProPFreeFixedBasis hHp hH h` | Moreover for `hHp : IsProPSubgroup p H`: `HasProPFreeFixedBasis p (smoothInvariantsInflation V H hH)`. |
| `IsFreeOnInvariants.hasProPFreeFixedBasis_smoothCompactInduction S hHp hH hHS h` | For subgroups `S` (explicit) and `H` (implicit) with `hHp : IsProPSubgroup p H`, `hH : IsOpen (H : Set G)`, `hHS : H ≤ S`, `[(H.subgroupOf S).Normal]`, a smooth representation `V` of `S` with `h : IsFreeOnInvariants V.representation R (H.subgroupOf S)` and `[Module.Finite R V^{H.subgroupOf S}]`: `HasProPFreeFixedBasis p X_S(V)`. |
| `isSummandOfFiniteSum_biproduct_compactInduction_invariants S hHp hH hHS V h` | For a finite type `J : Type` (`[Fintype J]`), families of subgroups `S j` (explicit), `H j` (implicit) and smooth representations `V j` of `S j` satisfying the hypotheses of the previous theorem for each `j`, and a biproduct (instance argument `[HasBiproduct _]`) of the family `X_{S j}(V j)`: `IsSummandOfFiniteSum (HasProPFreeFixedBasis p) (⨁ fun j => X_{S j}(V j))`. |
| `isCompact_subgroupOf hHc hHS` | For subgroups `H ≤ S` of `G` with `hHc : IsCompact (H : Set G)`: `H.subgroupOf S` is compact in `S`. Needs only the topology on `G`. |

Proofs.

- `hasFreeFixedBasis_smoothInvariantsInflation`: index the basis
  `Finsupp.basisSingleOne` of `I →₀ R` by `Fin (Fintype.card I)`
  (`Module.Basis.reindex`, `Fintype.equivFin`). The Library's
  `isFreeOnFixedVectors_smoothPermutation` gives `HasFreeFixedBasis H` for
  `smoothPermutation R (I →₀ R) H hH`, and `HasFreeFixedBasis.of_iso` transports
  it along the inverse of `smoothInvariantsInflationIso V H hH e`.
- `IsFreeOnInvariants.hasFreeFixedBasis`: `IsFreeOnInvariants.exists_finite`
  and the previous theorem.
- `IsFreeOnInvariants.hasProPFreeFixedBasis`: the previous theorem, with `H`
  as the pro-`p` subgroup.
- `IsFreeOnInvariants.hasProPFreeFixedBasis_smoothCompactInduction`:
  `H.subgroupOf S` is open in `S` (Library `isOpen_subgroupOf`), and `S` is
  open because it contains the open subgroup `H` (Mathlib's
  `Subgroup.isOpen_mono`). `IsFreeOnInvariants.hasFreeFixedBasis`, for the group
  `S` and its open normal subgroup `H.subgroupOf S`, gives
  `HasFreeFixedBasis (H.subgroupOf S)` for the `H`-invariants of `V`, and the
  Library's `HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction`
  applies.
- `isSummandOfFiniteSum_biproduct_compactInduction_invariants`: each
  `X_{S j}(V j)` satisfies `HasProPFreeFixedBasis p` by the previous theorem,
  hence is a summand of a finite sum (`IsSummandOfFiniteSum.of_prop`), and the
  Library's `IsSummandOfFiniteSum.biproduct` applies.
- `isCompact_subgroupOf`: the underlying set of `H.subgroupOf S` is the
  preimage of `H` under the inclusion `S → G` (Mathlib's
  `Subgroup.coe_subgroupOf`); the inclusion is an embedding whose image
  contains `H`, so the preimage of the compact set `H` is compact (Mathlib's
  `Topology.IsInducing.isCompact_preimage'`).

The biproduct hypotheses can always be met: the Library's category of smooth
representations is abelian (`Langlands.Representation.Category.Abelian`), so
Mathlib's `Abelian.hasFiniteBiproducts` gives finite biproducts. The theorems
take the biproduct as an argument to fix the object `⨁ X`.

## Direct limits of free modules

Section `FreeLimit` takes `R`, `G` as in the previous section and an index
type `ι` (implicit).

| Declaration | Statement |
| --- | --- |
| `IsFreeLimit.hasProPFreeFixedBasis_smoothCompactInduction S hV hKo hshrink hHp hH hHS` | For a subgroup `S` (explicit), a smooth representation `V` of `S`, a family `K : ι → Subgroup S` of normal subgroups with `hV : IsFreeLimit V.representation R K`, `hKo : ∀ i, IsOpen (K i : Set S)`, `hshrink : ∀ U ∈ nhds (1 : S), ∃ i, (K i : Set S) ⊆ U`, and a subgroup `H` with `hHp : IsProPSubgroup p H`, `hH : IsOpen (H : Set G)`, `hHS : H ≤ S`, `[(H.subgroupOf S).Normal]` and `[Module.Finite R V^{H.subgroupOf S}]`: `HasProPFreeFixedBasis p X_S(V)`. |
| `isSummandOfFiniteSum_biproduct_compactInduction_isFreeLimit S V hV hKo hshrink hHp hH hHS` | For a finite type `J : Type` (`[Fintype J]`), families `S j` (explicit), smooth representations `V j` of `S j` (explicit), families `K j : ι → Subgroup (S j)` and subgroups `H j` (implicit) satisfying the hypotheses of the previous theorem for each `j`, and a biproduct (instance argument `[HasBiproduct _]`) of the family `X_{S j}(V j)`: `IsSummandOfFiniteSum (HasProPFreeFixedBasis p) (⨁ fun j => X_{S j}(V j))`. |

Proofs.

- `IsFreeLimit.hasProPFreeFixedBasis_smoothCompactInduction`: `H` is compact
  (`IsProPSubgroup.compactSpace`, Mathlib's `isCompact_iff_compactSpace`), so
  `H.subgroupOf S` is compact in `S` (`isCompact_subgroupOf`) and open
  (`isOpen_subgroupOf`). The Library's `IsFreeLimit.isFreeOnInvariants_of_isOpen`
  (some `K i` lies in the open subgroup `H.subgroupOf S` and has finite index
  in the compact subgroup `H.subgroupOf S`) gives
  `IsFreeOnInvariants V.representation R (H.subgroupOf S)`, and
  `IsFreeOnInvariants.hasProPFreeFixedBasis_smoothCompactInduction` applies.
- `isSummandOfFiniteSum_biproduct_compactInduction_isFreeLimit`: as for
  `isSummandOfFiniteSum_biproduct_compactInduction_invariants`, with the
  previous theorem.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. The compact induction of invariants and the finite sums of such
inductions are modelled on the following passages of Harris 1999, read in the
rendered scans:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- Proof of Proposition 4.4, printed p.310 (one-based PDF page 12): "Since
  (recalling that `ẽ = (e, N, δ)`) (4.4.4)
  `Z^{i,j} = ⊕_{dim(e)=n-1-i} C^j(ẽ) = ⊕_{(e,δ)∈O_i} c-Ind_{S(ẽ)}^{GJ} C^j(ẽ)`
  is a sum of compactly induced modules, the argument goes through as before."
- Proof of Proposition 4.10, printed p.311 (one-based PDF page 13): the groups
  in question are
  "`⊕_{i+j=k} Hom_{𝒪/ℓ^m𝒪[GJ]}(⊕_{(e,δ)∈O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ),
  Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`, which can be rewritten (4.10.2)
  `⊕⊕ Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ), Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`"; "Up to
  conjugacy, we may assume `S(ẽ) ⊂ C_p`"; "Recall that `C^j(ẽ)` has been
  chosen to be a direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)`
  varies over a family of open subgroups of `S(ẽ)`."
- Printed p.312 (one-based PDF page 14): "We may replace `C^j_m(ẽ)` by
  `C^j_m(ẽ)^{H_p}` in (4.10.2)", and "Since `C^j_m(ẽ)^{H_p}` and
  `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
  follows that the maps (4.10.3) are surjective for all `m`."

Interpretation (our reading; explanation only, not formalized). Harris
replaces `C^j_m(ẽ)` by its `H_p`-invariants only in (4.10.2), after
Frobenius reciprocity has turned the `Hom` out of `c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ)`
into a `Hom` of `S(ẽ)`-modules; he never forms the compact induction of the
invariants. We form it, as `X_S(V)` with `S` in the role of `S(ẽ)`, `V` of
`C^j_m(ẽ)`, `H.subgroupOf S` of `S(ẽ) ∩ H_p`, `G` of `GJ` and `R` of
`𝒪/ℓ^m𝒪`, so that the Library's comparison theorems for extension of scalars
on `Ext` apply to it; and finite biproducts of such representations play the
role of the finite sums in (4.4.4). The normality of `H.subgroupOf S` in `S`
is an explicit hypothesis, since freeness over `𝒪/ℓ^m𝒪[S(ẽ)/H_p]` presupposes
the quotient group; the finite generation of the invariants over `R` is an
explicit hypothesis of ours, needed for the finite rank in
`HasFreeFixedBasis`. The module does not identify `G`, `S`, `H`, `V` or the
coefficient rings with Harris's objects.

## Scope

- Harris's modules `C^j_m(ẽ)` are not constructed, and it is not proved that
  they satisfy `IsFreeLimit` or that their invariants are finitely generated.
- Only the compact induction of the invariants is treated; the passage from
  `c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ)` to it, and Harris's computation (4.10.2), are not
  formalized.
- The `Ext` comparison theorems are not restated here; they apply through the
  Library's `SmoothExtBaseChangeSummand` with the hypotheses stated there.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.310-312 (one-based PDF pages 12-14), read in the rendered scans.

Dependencies: `Langlands.Cohomology.SmoothExtBaseChangeSummand` and
`Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit`, with Mathlib pinned
to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
