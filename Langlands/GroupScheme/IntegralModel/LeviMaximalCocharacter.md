# A cocharacter with torus centralizer, and Levi maximality from openness

All rings and schemes use one arbitrary universe `u`. This module proves the
published target `LeviMaximalCocharacterStatement` from one hypothesis: openness
of the integral points of every supplied model.

## Tori and base change along field maps

`IsTorus.baseChange_specMap` states: for fields `k`, `K`, a ring map
`φ : k ⟶ K` in `CommRingCat`, and a torus `T` over `Spec k`, the base change of `T`
along `Spec.map φ` is a torus. It is the published `IsTorus.baseChange` for the
algebra structure given by `φ`.

## A cocharacter with torus special centralizer

Let `F` be a nonarchimedean local field and `M : IntegralModel 𝒪[F] F G`.
`exists_cocharacter_isTorus_specialCentralizer` assumes that `G` and the special
fibre of `M.group` over `𝓀[F]` are connected reductive. It gives a cocharacter
`χ : Gm(Spec 𝒪[F]) ⟶ M.group` such that the special fibre over `𝓀[F]` of the
Library integral centralizer scheme `Dynamic.Affine.centralizerScheme χ` is a
torus.

Proof.

1. `𝒪[F]` is a Henselian local ring (the published
   `henselianLocalRing_integer`), and `M.group` is smooth
   (`isSmooth_of_reductive_localField`).
2. Let `κ` be the scheme residue field at the closed point of `Spec 𝒪[F]` and `G₀`
   the base change of `M.group` to `Spec κ`. `G₀` is connected reductive by the
   published `residueReductive_of_fieldReductive`, applied to the special fibre over
   `𝓀[F]`. The field `κ` is finite, being isomorphic to `𝓀[F]`.
3. A connected reductive group over a finite field is quasi-split
   (`finiteFieldQuasiSplit`). The published
   `IsQuasiSplit.exists_maximalSplitTorus_with_torusCentralizer`, with
   `dynamicCentralizerReductive` and `parabolicDynamic`, gives a maximal split torus
   `a : A ⟶ G₀` and a closed subgroup `c : C ⟶ G₀` representing its centralizer
   `torusCentralizer a`, with `C` a torus. The published `centralizingCocharacter`
   gives a cocharacter `ν` of `A` whose dynamic centralizer is `torusCentralizer a`.
4. `exists_cocharacter_baseChange_eq_comp_iso` (module
   `Torus.HenselianCocharacterLifting`) lifts `ν ≫ a`: it gives `χ` and an
   automorphism `B` of `G₀` with base change of `χ` to `κ` equal to `ν ≫ a ≫ B.hom`.
5. By `Dynamic.centralizer_eq_comap_of_iso`, the dynamic centralizer of that base
   change is the pullback of `torusCentralizer a` along `B.inv`. It is therefore
   represented by `c ≫ B.hom`, so the Library centralizer scheme of the base-changed
   cocharacter is isomorphic to the torus `C`. By the published
   `Dynamic.affineCentralizerBaseChangeIso`, this is the fibre of the integral
   centralizer scheme of `χ` over `κ`.
6. The isomorphism `closedPointResidueSpecIso` from `Spec 𝓀[F]` to `Spec κ`,
   followed by the residue point, is `Spec.algebraMap 𝒪[F] 𝓀[F]`
   (`closedPointResidueSpecIso_hom_fromSpecResidueField`). So the special fibre over
   `𝓀[F]` is the base change of the fibre over `κ` along a ring map of fields, and
   it is a torus by `IsTorus.baseChange_specMap`.

## Levi maximality

`leviMaximalCocharacterStatement_of_isOpen` takes the hypothesis `hopen`: for every
nonarchimedean local field `F`, every group scheme `G` over `Spec F` with affine
underlying scheme, and every `M : IntegralModel 𝒪[F] F G`, the set
`M.integralPoints` is open in `G(F)` for `rationalPointTopology F G.X`. From it, the
theorem proves `LeviMaximalCocharacterStatement.{u}`. Given the data of the
statement, it takes `χ` from the previous section and applies
`leviMaximal_of_isTorus_specialCentralizer` (module `DynamicCentralizer`). The
statement's hypothesis that `C` contains the integral points of the centralizer is
not used.

## Provenance

This assembles internal constructions for the published target
`LeviMaximalCocharacterStatement` along Maculan (2017), proof of Lemma 5.1, Claim
(printed p. 14 / PDF p. 15). There the maximal `𝒪`-torus of a Borel subgroup is the
centralizer of a maximal split torus, and maximal boundedness of its integral
points (Proposition 4.6) gives the Levi step. The `𝒪`-torus is obtained here as the
integral centralizer of a cocharacter lifted from a maximal split torus of the
quasi-split special fibre. Openness of integral points is a hypothesis of this
module and is not proved here.
