# Extension of scalars on `Ext` groups of smooth representations

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextExtBaseChange` (`HasResolutionBy`,
`HasResolutionBy.of_prop`, `HasResolutionBy.mono`,
`extBaseChangeMap_zero_bijective_iff`,
`extBaseChangeMap_injective_of_hasResolutionBy`,
`extBaseChangeMap_bijective_of_hasResolutionBy`,
`extBaseChangeEquivOfHasResolutionBy`; Worker 61),
`Langlands.Cohomology.HyperextInvariantsLocalization`
(`hasFiniteOrbits_comp_subtype_of_isSmooth`,
`invariantsBaseChangeEquivOfIsLocalization`; Worker 61) and
`Langlands.Cohomology.DivisibleSystem.PermutationProjective`
(`smoothTrivialFunctor`, `smoothInvariantsFunctor`,
`smoothInvariantsFunctor_preservesEpimorphisms`; Worker 61). Through these
imports it also uses `Langlands.Cohomology.HyperextHomLocalization`
(`homBaseChangeMap`; Worker 61), `Langlands.Cohomology.HyperextScalarExtension`
(`smoothRepExtendScalars_isSemilinear`, `smoothExtBaseChangeMap`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension`
(`smoothRepExtendScalars`, `smoothRepRestrictScalars`,
`smoothRepRestrictScalars_map_apply`, `smoothRepExtendScalarsAdjunction`;
Worker 61), `Langlands.Cohomology.DivisibleSystem.ScalarExtension`
(`baseChangeRepresentation`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.ProPInvariants` (`IsProPSubgroup`;
Worker 61), `Langlands.Representation.Induction.OpenAdjunction`
(`Induction.smoothRestriction`, `Induction.smoothCompactInduction`,
`Induction.compactInductionAdjunction` and the instance
`Induction.smoothRestriction_preservesEpimorphisms`; Worker 61),
`Langlands.Representation.Category.Abelian` (`SmoothRep.epi_iff_surjective`;
Worker 13) and `Langlands.Cohomology.ProPInvariants.Statement`
(`ProPInvariantsExactStatement`; Worker 3).

The Library's `smoothExtBaseChangeMap R S G X Y n` is the `S`-linear map
`S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)`, `s ⊗ e ↦ s • (S ⊗ e)`,
for smooth representations `X`, `Y` of a topological group `G` on `R`-modules
and a flat `R`-algebra `S`. The Library's `HyperextExtBaseChange` proves it
injective or bijective when `X` has a finite resolution by objects of a class
`Q` of projective objects `P` such that `S ⊗[R] P` is projective and
`S ⊗[R] Hom_G(P, Y) → Hom_G(S ⊗[R] P, S ⊗[R] Y)` is bijective, and constructs
such a class only for representations of abstract monoids. This module
constructs such a class of smooth representations: those that are free of
finite rank on vectors fixed by a pro-`p` subgroup `H`, for `p` invertible in
`R`, assuming the Library's `ProPInvariantsExactStatement`, and for `S` a
localization of `R`. Compact induction `c-Ind_H^G M` of the trivial
representation on a free module of finite rank, from an open pro-`p` subgroup
`H`, belongs to the class.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`.

## Conventions

`SmoothRep.{uR, uG, w} R G` is the Library's category of smooth
representations of `G` on `R`-modules with carriers in universe `w`. For
`A : SmoothRep R G` and a subgroup `H` of `G`,
`Representation.invariants (A.representation.comp H.subtype)` is the
`R`-submodule `A^H` of `H`-fixed vectors of `A`, and `SmoothRep.hom f` is the
underlying intertwining map of a morphism `f`. `Ext^n_G(X, Y)` is Mathlib's
`Abelian.Ext.{t} X Y n`. Below `E = smoothRepExtendScalars.{max uS w} R S G`
is the Library's extension of scalars
`SmoothRep.{uR, uG, max uS w} R G ⥤ SmoothRep.{uS, uG, max uS w} S G`,
`X ↦ S ⊗[R] X`, and `hE = smoothRepExtendScalars_isSemilinear.{max uS w} R S G`;
the universe `max uS w` is that of the Library's adjunction
`smoothRepExtendScalarsAdjunction.{w} R S G : E ⊣ smoothRepRestrictScalars R S G`.
`ProPInvariantsExactStatement.{uG, uR, w}` is the Library's proposition that
for every prime `p`, every compact totally disconnected topological group
`K : Type uG` whose quotients by open normal subgroups are `p`-groups, and every
commutative ring `R : Type uR` in which `p` is a unit, Mathlib's invariants
functor `Rep.invariantsFunctor R K` sends each short exact sequence in
`Rep.{w} R K` whose three terms are smooth to a short exact sequence. It is not
proved in the Library; here it is always an explicit hypothesis `hP`.

## Representations free on fixed vectors

Section `FixedVectors` takes a commutative ring `R : Type uR` and a group
`G : Type uG` with a topology (both implicit); from
`exists_mem_invariants_of_epi` on also `[IsTopologicalGroup G]`. All smooth
representations are in `SmoothRep.{uR, uG, w} R G`, and `ι : Type*` is any
index type.

| Declaration | Statement |
| --- | --- |
| `smoothRepHom_mem_invariants H f hv` | For a subgroup `H`, `f : A ⟶ B` and `hv : v ∈ A^H`: `SmoothRep.hom f v ∈ B^H`. |
| `IsFreeOnFixedVectors H x` | For `x : ι → P`, a structure (a `Prop`) with three fields: `mem_invariants : ∀ i, x i ∈ P^H`; `hom_ext`: two morphisms `f g : P ⟶ Y` with `SmoothRep.hom f (x i) = SmoothRep.hom g (x i)` for all `i` are equal; `exists_hom`: for every `Y` and `y : ι → Y` with all `y i ∈ Y^H`, there is `f : P ⟶ Y` with `SmoothRep.hom f (x i) = y i` for all `i`. |
| `IsFreeOnFixedVectors.eval_bijective hx Y` | For `hx : IsFreeOnFixedVectors H x`: the map `(P ⟶ Y) → (ι → Y^H)`, `f ↦ (i ↦ SmoothRep.hom f (x i))`, is bijective. |
| `isFreeOnFixedVectors_of_isZero H hZ` | For `hZ : IsZero Z`: `IsFreeOnFixedVectors H (Fin.elim0 : Fin 0 → Z)`. |
| `HasFreeFixedBasis H P` | There are `n : ℕ` and `x : Fin n → P` with `IsFreeOnFixedVectors H x`. A `def` (a `Prop`). |
| `HasProPFreeFixedBasis p P` | There is a subgroup `H` of `G` with the Library's `IsProPSubgroup p H` and `HasFreeFixedBasis H P`. A `def` (a `Prop`). |
| `hasFreeFixedBasis_of_isZero H hZ` | For `hZ : IsZero Z`: `HasFreeFixedBasis H Z`. |
| `HasFreeFixedBasis.hasResolutionBy hP n` | For `hP : HasFreeFixedBasis H P`: `HasResolutionBy (HasFreeFixedBasis H) n P`, for every `n : ℕ`. |
| `HasProPFreeFixedBasis.hasResolutionBy hP n` | For `hP : HasProPFreeFixedBasis p P`: `HasResolutionBy (HasProPFreeFixedBasis p) n P`, for every `n : ℕ`. |
| `exists_mem_invariants_of_epi hP hH hR e hz` | For `hP : ProPInvariantsExactStatement.{uG, uR, w}`, `hH : IsProPSubgroup p H`, `hR : IsUnit (p : R)`, an epimorphism `e : Y ⟶ Z` (instance argument `[Epi e]`) and `hz : z ∈ Z^H`: there is `y ∈ Y^H` with `SmoothRep.hom e y = z`. |
| `IsFreeOnFixedVectors.projective hP hH hR hx` | For `hP`, `hH`, `hR` as above and `hx : IsFreeOnFixedVectors H x`: `Projective P`. |
| `HasProPFreeFixedBasis.projective hP hR hPp` | For `hP`, `hR` as above and `hPp : HasProPFreeFixedBasis p P`: `Projective P`. |

`IsProPSubgroup p H` (Library) says that `p` is prime and that `H`, with the
subspace topology, is compact and totally disconnected with `p`-group quotients
by its open normal subgroups. In `IsFreeOnFixedVectors` the family `x` may be
infinite; `HasFreeFixedBasis` asks for a finite family.

Proofs.

- `smoothRepHom_mem_invariants`: for `h ∈ H`,
  `B(h) (f v) = f (A(h) v) = f v` by the intertwining property
  (`Representation.IntertwiningMap.isIntertwining`) and `v ∈ A^H`.
- `IsFreeOnFixedVectors.eval_bijective`: injectivity is `hom_ext`,
  surjectivity is `exists_hom`.
- `isFreeOnFixedVectors_of_isZero`: there are no indices; two morphisms out of
  a zero object are equal (`IsZero.eq_of_src`), and the zero morphism takes the
  empty family of values.
- `hasFreeFixedBasis_of_isZero`: the previous lemma with `n = 0`.
- `HasFreeFixedBasis.hasResolutionBy`: the Library's `HasResolutionBy.of_prop`
  with the zero object, which satisfies `HasFreeFixedBasis H` by the previous
  lemma. `HasProPFreeFixedBasis.hasResolutionBy`: the same for the subgroup `H`
  witnessing `HasProPFreeFixedBasis p P`, followed by `HasResolutionBy.mono`.
- `exists_mem_invariants_of_epi`: `H` is compact and totally disconnected
  (`IsProPSubgroup`), so the Library's
  `smoothInvariantsFunctor_preservesEpimorphisms` shows, given `hP`, that the
  `H`-invariants functor on smooth representations of `H` preserves
  epimorphisms. The restriction of `e` to `H`
  (`Induction.smoothRestriction R H`) is an epimorphism
  (`Induction.smoothRestriction_preservesEpimorphisms`), so `e` restricted to
  `H`-fixed vectors is an epimorphism of `R`-modules, that is, surjective
  (`ModuleCat.epi_iff_surjective`).
- `IsFreeOnFixedVectors.projective`: given `f : P ⟶ Z` and an epimorphism
  `e : Y ⟶ Z`, the vectors `f (x i)` lie in `Z^H`
  (`smoothRepHom_mem_invariants`); choose `y_i ∈ Y^H` with `e y_i = f (x i)`
  (`exists_mem_invariants_of_epi`), take `g : P ⟶ Y` with `g (x i) = y_i`
  (`exists_hom`), and `g ≫ e = f` by `hom_ext`.
- `HasProPFreeFixedBasis.projective`: the previous lemma for the witnessing
  subgroup and family.

## Compact induction

Section `CompactInduction` takes `R`, `G` as above with
`[IsTopologicalGroup G]`, a subgroup `H` and `hH : IsOpen (H : Set G)` (both
explicit). For an `R`-module `M : ModuleCat.{max uG uV} R`, let
`P_M = (Induction.smoothCompactInduction.{uR, uG, uV} R H).obj
((smoothTrivialFunctor R H).obj M)` be the Library's compact induction to `G`
of the trivial representation of `H` on `M`, an object of
`SmoothRep.{uR, uG, max uG uV} R G`, and let
`u = (Induction.compactInductionAdjunction.{uR, uG, uV} H hH).unit.app
((smoothTrivialFunctor R H).obj M)`. By the Library's
`compactInductionAdjunction_unit_app_apply`, `u` sends `v ∈ M` to the function
supported on `H` with value `v` on `H`.

| Declaration | Statement |
| --- | --- |
| `isFreeOnFixedVectors_compactInduction H hH M b` | For a basis `b : Module.Basis ι R M` (any index type `ι`): `IsFreeOnFixedVectors H (fun i => SmoothRep.hom u (b i))` in `P_M`. |
| `hasProPFreeFixedBasis_compactInduction H hH hHp M b` | For `hHp : IsProPSubgroup p H` and a basis `b : Module.Basis (Fin n) R M`: `HasProPFreeFixedBasis p P_M`. |

Proofs.

- `isFreeOnFixedVectors_compactInduction`: `u` is `H`-equivariant from the
  trivial representation, so its values are `H`-fixed. Under the Library's
  adjunction `compactInductionAdjunction H hH` (compact induction is left
  adjoint to restriction to the open subgroup `H`), a morphism `P_M ⟶ Y`
  corresponds to an `H`-equivariant map from the trivial representation on `M`
  to `Y`, that is, to an `R`-linear map `M → Y^H`, and the value of the
  morphism at `u (b i)` is the value of that map at `b i`. Two `R`-linear maps
  agreeing on a basis are equal (`Module.Basis.ext`), which gives `hom_ext`.
  For `exists_hom`, given `y i ∈ Y^H`, the map `Module.Basis.constr` sending
  `b i` to `y i` into `Y^H`, followed by the inclusion `Y^H → Y`, is
  `H`-equivariant; its adjoint morphism `P_M ⟶ Y` sends `u (b i)` to `y i`
  (`Adjunction.homEquiv` applied to its inverse, `Module.Basis.constr_basis`).
- `hasProPFreeFixedBasis_compactInduction`: the previous lemma, with `H`
  itself as the pro-`p` subgroup.

## Extension of scalars

Section `ExtendScalars` takes `R`, `G` as above and a commutative `R`-algebra
`S : Type uS` (explicit).

| Declaration | Statement |
| --- | --- |
| `smoothRepRestrictScalars_preservesEpimorphisms R S G` | Instance: the Library's restriction of scalars `smoothRepRestrictScalars.{w} R S G : SmoothRep.{uS, uG, w} S G ⥤ SmoothRep.{uR, uG, w} R G` preserves epimorphisms. |
| `IsFreeOnFixedVectors.smoothRepExtendScalars S hx` | For `P : SmoothRep.{uR, uG, max uS w} R G` and `hx : IsFreeOnFixedVectors H x`: `IsFreeOnFixedVectors H (fun i => 1 ⊗ₜ x i)` in `E.obj P = S ⊗[R] P`. |
| `HasProPFreeFixedBasis.projective_smoothRepExtendScalars S hP hR hPp` | For `[IsTopologicalGroup G]`, `hP : ProPInvariantsExactStatement.{uG, uR, max uS w}`, `hR : IsUnit (p : R)` and `hPp : HasProPFreeFixedBasis p P` with `P : SmoothRep.{uR, uG, max uS w} R G`: `Projective (E.obj P)`. |

Proofs.

- `smoothRepRestrictScalars_preservesEpimorphisms`: epimorphisms of smooth
  representations are the morphisms with surjective underlying map
  (`SmoothRep.epi_iff_surjective`), and restriction of scalars does not change
  the underlying map (`smoothRepRestrictScalars_map_apply`,
  `RestrictScalars.addEquiv`).
- `IsFreeOnFixedVectors.smoothRepExtendScalars`: the vectors `1 ⊗ x i` are
  `H`-fixed because `H` acts on `S ⊗[R] P` through `P`. Under
  `smoothRepExtendScalarsAdjunction`, a morphism `g : S ⊗[R] P ⟶ Y` corresponds
  to a morphism `P ⟶ smoothRepRestrictScalars Y` whose value at `x i` is
  `g (1 ⊗ x i)`; `hom_ext` of `x` gives `hom_ext`. For `exists_hom`, `H`-fixed
  `y i ∈ Y` stay `H`-fixed in the restriction of scalars of `Y`; take the
  morphism `f : P ⟶ smoothRepRestrictScalars Y` with `f (x i) = y i` given by
  `exists_hom` of `x`; its adjoint sends `1 ⊗ x i` to `1 • y i = y i`.
- `HasProPFreeFixedBasis.projective_smoothRepExtendScalars`: a left adjoint
  whose right adjoint preserves epimorphisms preserves projective objects
  (Mathlib's `Adjunction.map_projective`), applied to
  `smoothRepExtendScalarsAdjunction`, the instance above and
  `HasProPFreeFixedBasis.projective`.

## Localization

Section `Localization` takes `R`, `G` as above with `[IsTopologicalGroup G]`,
a commutative `R`-algebra `S` and a submonoid `M` of `R` with
`[IsLocalization M S]` (`S` and `M` explicit). All representations are in
`SmoothRep.{uR, uG, max uS w} R G`.

| Declaration | Statement |
| --- | --- |
| `smoothHomBaseChangeMap_bijective_of_isFreeOnFixedVectors S M hx Y` | For a subgroup `H` with `[CompactSpace H]`, `x : Fin n → P` and `hx : IsFreeOnFixedVectors H x`: the Library's `homBaseChangeMap E hE P Y : S ⊗[R] (P ⟶ Y) → (E.obj P ⟶ E.obj Y)` is bijective. |
| `smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis S M hP Y` | For `hP : HasProPFreeFixedBasis p P`: `homBaseChangeMap E hE P Y` is bijective. |

Its section `Ext` also takes `[Module.Flat R S]`,
`[HasExt.{t} (SmoothRep.{uR, uG, max uS w} R G)]`,
`[HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)]` and `Y` (explicit);
`X` is implicit, and `hP : ProPInvariantsExactStatement.{uG, uR, max uS w}` and
`hR : IsUnit (p : R)` are explicit. The flatness instance holds for every
localization (Mathlib's `IsLocalization.flat`); it is an argument because the
Library's `smoothExtBaseChangeMap` takes it.

| Declaration | Statement |
| --- | --- |
| `smoothExtBaseChangeMap_injective_of_hasResolutionBy S M Y hP hR n hX` | For `hX : HasResolutionBy (HasProPFreeFixedBasis p) n X`: `smoothExtBaseChangeMap.{max uS w} R S G X Y n : S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(E.obj X, E.obj Y)` is injective. |
| `smoothExtBaseChangeMap_bijective_of_hasResolutionBy S M Y hP hR n hX` | For `hX : HasResolutionBy (HasProPFreeFixedBasis p) (n + 1) X`: `smoothExtBaseChangeMap.{max uS w} R S G X Y n` is bijective. |
| `smoothExtBaseChangeEquivOfHasResolutionBy S M Y hP hR n hX` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Ext^n_G(X, Y) ≃ₗ[S] Ext^n_G(E.obj X, E.obj Y)`. A `def`. |
| `smoothExtBaseChangeEquivOfHasResolutionBy_apply S M Y hP hR n hX z` | Its value at `z` is `smoothExtBaseChangeMap.{max uS w} R S G X Y n z` (a `simp` lemma, by definition). |

`HasResolutionBy Q n X` (Library) holds when there is an exact sequence
`P_n → ⋯ → P_0 → X → 0` with all `Q P_i`.

Proofs.

- `smoothHomBaseChangeMap_bijective_of_isFreeOnFixedVectors`: let
  `ρ = Y.representation.comp H.subtype`. By `eval_bijective`, evaluation at `x`
  is an `R`-linear equivalence `(P ⟶ Y) ≃ (Fin n → Y^H)`; let `ψ` be its base
  change followed by Mathlib's `TensorProduct.piRight`, an `S`-linear
  equivalence `S ⊗[R] (P ⟶ Y) ≃ (Fin n → S ⊗[R] Y^H)`. Since `H` is compact and
  `Y` smooth, `ρ` has finite orbits (`hasFiniteOrbits_comp_subtype_of_isSmooth`),
  so the Library's `invariantsBaseChangeEquivOfIsLocalization` identifies
  `S ⊗[R] Y^H` with the `H`-fixed vectors of `S ⊗[R] Y`; let `Φ` be this
  identification in each coordinate (`LinearEquiv.piCongrRight`) and `θ` the
  inclusion into `Fin n → S ⊗[R] Y`, which is injective. The map
  `ev : (E.obj P ⟶ E.obj Y) → (Fin n → S ⊗[R] Y)`, `g ↦ (g (1 ⊗ x i))_i`, is
  injective by `hom_ext` of `IsFreeOnFixedVectors.smoothRepExtendScalars`. On
  `s ⊗ f`, `ev (s • E.map f) = (s • (1 ⊗ f (x i)))_i = (s ⊗ f (x i))_i =
  θ (Φ (ψ (s ⊗ f)))`, and both sides are additive, so
  `ev ∘ homBaseChangeMap E hE P Y = θ ∘ Φ ∘ ψ`. Hence `homBaseChangeMap E hE P Y`
  is injective. For surjectivity, given `g`, the values `g (1 ⊗ x i)` are
  `H`-fixed (`smoothRepHom_mem_invariants`), so
  `ev g = θ (Φ (ψ t))` for `t = ψ⁻¹ (Φ⁻¹ (ev g))`, and injectivity of `ev`
  gives `homBaseChangeMap E hE P Y t = g`.
- `smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis`: the previous
  theorem for the witnessing pro-`p` subgroup, which is compact
  (`IsProPSubgroup.compactSpace`).
- `smoothExtBaseChangeMap_injective_of_hasResolutionBy`,
  `smoothExtBaseChangeMap_bijective_of_hasResolutionBy`,
  `smoothExtBaseChangeEquivOfHasResolutionBy`: the Library's
  `extBaseChangeMap_injective_of_hasResolutionBy`,
  `extBaseChangeMap_bijective_of_hasResolutionBy` and
  `extBaseChangeEquivOfHasResolutionBy` for `F = E` and
  `Q = HasProPFreeFixedBasis p`, with `HasProPFreeFixedBasis.projective`,
  `HasProPFreeFixedBasis.projective_smoothRepExtendScalars`, and the Library's
  `extBaseChangeMap_zero_bijective_iff` combined with
  `smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis`.
  `smoothExtBaseChangeMap` is by definition the Library's `extBaseChangeMap E hE`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. The class of representations free on vectors fixed by a pro-`p`
subgroup is modelled on the following passage of Harris 1999, read in the
rendered scans:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §4, printed p.311 (one-based PDF page 13), Proposition 4.10: "There is a
  spectral sequence of `𝒪`-modules (4.10.1)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, L_ℓ(n - 1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`.
  Here `Ext^i` denotes the i-th derived functor of `Hom` in the category of
  smooth `L_ℓ[GJ]`-modules."
- Same page, proof of Proposition 4.10: the complexes are
  "`⊕_{i+j=k} Hom_{𝒪/ℓ^m𝒪[GJ]}(⊕_{(e,δ)∈O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ), Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`",
  and "Recall that `C^j(ẽ)` has been chosen to be a direct limit of free
  `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies over a family of open
  subgroups of" `S(ẽ)`.
- Printed p.312 (one-based PDF page 14): "Since `C^j_m(ẽ)^{H_p}` and
  `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
  follows that the maps (4.10.3) are surjective for all `m`." The proof ends
  with the integral statement (4.10.4)
  "`E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒ H^{i+j}(S̄_{K(N)}, 𝓛̃)`."

Interpretation (explanation only, not formalized). In Harris's setting the
coefficient ring `𝒪` is the ring of integers of `L_ℓ`, `ℓ ≠ p`, so `p` is a
unit in `𝒪`, and `L_ℓ` is the localization of `𝒪` at the powers of a
uniformizer. The `E_2` terms of (4.10.4) and (4.10.1) are `Ext` groups of
smooth representations with `𝒪`- and with `L_ℓ`-coefficients, and the
comparison map between them is `smoothExtBaseChangeMap` for `R = 𝒪`,
`S = L_ℓ`. Compact induction `c-Ind_H^{GJ}` of a free module of finite rank
with trivial action of an open pro-`p` subgroup `H` is the kind of
representation that `hasProPFreeFixedBasis_compactInduction` covers. When
`H ⊆ S(ẽ)` is an open pro-`p` subgroup, Harris's `c-Ind_{S(ẽ)}^{GJ}` of a free
`𝒪_m[S(ẽ)/H]`-module of finite rank is of that form, with coefficients
`𝒪_m = 𝒪/ℓ^m𝒪`, by transitivity of compact induction, which this module does
not prove.
Harris's freeness assertion is used in his argument for a Mittag-Leffler
condition, not for a comparison of coefficients; here only the freeness on
`H`-fixed vectors is borrowed. The module does not identify `G`, `X`, `Y`, the
subgroups or the coefficient rings with Harris's objects.

## Scope

- `ProPInvariantsExactStatement` is an explicit hypothesis; it is not proved in
  the Library.
- The existence of resolutions by representations free of finite rank on
  vectors fixed by pro-`p` subgroups is a hypothesis; it is not verified for
  any representation other than those of the class itself
  (`HasProPFreeFixedBasis.hasResolutionBy`), and whether Harris's cohomology
  groups have such resolutions is not addressed. Harris's complexes have
  coefficients `𝒪/ℓ^m𝒪` and are direct limits of free modules; the passage
  to `𝒪`-coefficients (the limit over `m`) and direct limits are not
  treated.
- The comparison map on `Hom` is proved bijective only for a localization `S`
  of `R` (used through the commutation of invariants of a compact group with
  localization), not for every flat `R`-algebra.
- Only `Ext` groups between objects are treated. Hyperext groups of complexes,
  invariants and isotypic parts, and compatibility with the differentials of
  Harris's spectral sequences are not treated.
- `HasExt` is a hypothesis; the results hold for each such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.311 and 312 (rendered scans).

Dependencies: `Langlands.Cohomology.HyperextExtBaseChange`,
`Langlands.Cohomology.HyperextInvariantsLocalization` and
`Langlands.Cohomology.DivisibleSystem.PermutationProjective`, with Mathlib
pinned to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
