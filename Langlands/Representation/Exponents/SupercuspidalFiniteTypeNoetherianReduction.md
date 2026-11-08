# Finitely generated supercuspidal representations are Noetherian (Renard VI.7.5, first step)

Module `Langlands.Representation.Exponents.SupercuspidalFiniteTypeNoetherianReduction`.

## Purpose and scope

Worker 1582's reduction `smoothRepNoetherianCategory_of_inputs` (module
`Exponents/SmoothRepNoetherianReduction`) derives the VI.7.5 Proposition
(`SmoothRepNoetherianCategoryStatement`) from four inputs. One of them is
`SupercuspidalFiniteTypeNoetherianStatement`: for every connected reductive `G` over a
nonarchimedean local field, a supercuspidal smooth representation of `G(F)` that is
finitely generated over `ℂ[G(F)]` is a Noetherian `ℂ[G(F)]`-module. Here
"supercuspidal" (`IsSupercuspidal`) means that the normalized Jacquet module along every
proper actual rational parabolic vanishes.

This module proves that statement in carrier universe `max u v` from the published
statements of Renard's VI.3 and VI.4 and two structural statements. Every input is an
explicit premise, so the result is a conditional reduction and discharges neither VI.7.5
target. The module also shows that carrier universe `max u v` is enough for the
Proposition in every carrier universe.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The proof of
the VI.7.5 Proposition (printed p.186 / PDF p.192) starts as follows. Each supercuspidal
component `M(G)_[ρ]` is equivalent, by the Corollary of VI.4.4, to the category of unital
right modules over a Noetherian algebra, hence is a Noetherian category. An object of
finite type has only finitely many nonzero components, because a finite generating
system does. This module formalizes that step, restricted to supercuspidal
representations, in the form needed by `smoothRepNoetherianCategory_of_inputs`.

## Main results

Namespace `Langlands.Aubert.General.RepresentedParabolic`:

- `supercuspidalFiniteTypeNoetherian_of_inputs`. Hypotheses:
  - `hStandard : StandardCocharacterStatement.{u}`;
  - `hRoot : RelativeRootSystemStatement.{u}`;
  - `hSplit : CuspidalSupport.RationalCuspidalInertiaDecompositionStatement.{u, max u v}`:
    VI.3.3.1, the splitting of the smooth category along the inertia class of an
    irreducible cuspidal representation (printed pp.144–145 / PDF pp.150–151);
  - `hFinite : CuspidalSupport.RationalCuspidalInertiaFinitenessStatement.{u, max u v}`:
    the concluding remark of VI.3.4. For each compact open subgroup `K`, only finitely many
    inertia classes have an irreducible cuspidal representative with nonzero `K`-fixed
    vectors (printed p.146 / PDF p.152);
  - `hRes : CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, max u v}`:
    VI.3.2(ii), finite semisimple restriction of an irreducible representation to the
    norm kernel `⁰G` (printed pp.143–144 / PDF pp.149–150);
  - `hHom : CuspidalSupport.RationalSummandHomEquivalenceStatement.{u, max u v}`: the
    Theorem of VI.4.1. For an irreducible summand `ρ` of the restriction of an irreducible
    cuspidal `π` to `⁰G`, the functor `Hom(Π, •)` with `Π = ind_{⁰G}^G ρ` is an
    equivalence from the inertia block to modules over `(End Π)ᵐᵒᵖ` (printed pp.150–151 /
    PDF pp.156–157);
  - `hEnd : CuspidalSupport.RationalSummandEndNoetherianStatement.{u, max u v}`: the
    Corollary of VI.4.4, `End Π` is left and right Noetherian (printed p.159 /
    PDF p.165).

  Conclusion: `SupercuspidalFiniteTypeNoetherianStatement.{u, max u v}`.
- `smoothRepNoetherianCategory_of_universeLift`:
  `SmoothRepNoetherianCategoryStatement.{u, max u v} →
  SmoothRepNoetherianCategoryStatement.{u, v}`.
- `smoothRepNoetherianCategory_of_blockInputs`: the Proposition in every carrier universe
  `v`. It takes the seven hypotheses above and the remaining inputs of
  `smoothRepNoetherianCategory_of_inputs` in carrier universe `max u v`:
  `LeviJacquetFiniteTypeStatement`, `RepresentedCuspidalRemainderSplittingStatement` and
  `FiniteProperParabolicSupercuspidalTestStatement`. Proof:
  `smoothRepNoetherianCategory_of_inputs` at `max u v`, with the supercuspidal input
  supplied by `supercuspidalFiniteTypeNoetherian_of_inputs`, followed by
  `smoothRepNoetherianCategory_of_universeLift`.

### Why carrier universe `max u v`

In the VI.4.1 statements the inertia block and the progenerator `Π` live in carrier
universe `max uF uV`, where `uF` is the field universe and `uV` the carrier universe of
`π`. Their block is that of `rationalInertiaBaseLift G π`, the carrier lift of `π`.
With `uV = max u v`, the block universe `max u (max u v)` is `max u v`, so the
representation being studied already lives in the block's category, and
`rationalInertiaBaseLiftIso` identifies `π` with its lift. In a smaller carrier universe
the block objects would be lifts, and comparing irreducible subquotients of a lift with
those of the original is not available. For the Proposition the universe costs nothing:
finite generation and Noetherianity of the group-algebra module are unchanged by the
carrier lift (`moduleFinite_universeLift_iff`, and a surjection from the lift), which
gives `smoothRepNoetherianCategory_of_universeLift`. The Theorem-side reduction
`leviInductionFiniteType_of_inputs` (module `Exponents/LeviInductionFiniteTypeReduction`)
already uses the Proposition in carrier universe `max u v`.

## Proof

Let `A` be supercuspidal and finitely generated, with carrier universe `max u v`.

1. **Standard family.** The published `exists_maximalSplitTorus_genericCocharacter` gives
   a maximal split torus `i` and a generic cocharacter `ν`. `hRoot` gives the relative
   root system and `isClosed_unipotent_of_isNonarchimedeanLocalField` the closedness of
   the standard unipotent radicals. `rationalPoint_t2Space` gives the Hausdorff property.
   Every subquotient `D` of `A` is supercuspidal (`IsSupercuspidal.of_isSubquotient`,
   module `RepresentedCuspidalProjection`), hence cuspidal for the proper standard
   parabolics (`isCuspidal_of_all_represented_parabolics_of_standardCocharacter`, using
   `hStandard`). The rest of the proof works in the CuspidalSupport conventions, with the
   topology `rationalPointTopology`, to which the represented topology `pointTopology`
   unfolds.
2. **Level.** A finite generating set of `A` is fixed by one compact open subgroup `K`
   (`exists_compactOpen_fixing_finite`). Hence `A` is generated by its `K`-fixed vectors,
   in the form `SmoothRep.FixedVectorsGenerate K A`: every intertwiner out of `A` that
   kills the `K`-fixed vectors is zero (`fixedVectorsGenerate_of_span`). This property
   passes to quotients (`FixedVectorsGenerate.of_surjective`). A nonzero quotient of a
   representation with this property has nonzero `K`-fixed vectors
   (`FixedVectorsGenerate.nontrivial_fixedVectors`).
3. **Finitely many classes.** By `hFinite`, the set `C` of inertia classes with an
   irreducible cuspidal representative having nonzero `K`-fixed vectors is finite. For
   each `c ∈ C` a representative `π c` is chosen.
4. **Splitting induction** (`CuspidalSupport.isNoetherian_of_inertiaSplittings`, by
   induction on a finite set `s` of indices). Claim: let `X` be finitely generated and
   generated by `K`-fixed vectors, and suppose every irreducible subquotient of `X` with
   nonzero `K`-fixed vectors is inertia-related to some `π a`, `a ∈ s`. Then `X` is
   Noetherian.
   - `s = ∅`. A nonzero `X` would have an irreducible quotient
     (`SmoothRep.exists_irreducible_quotient_of_finite`, from a maximal submodule) with
     nonzero `K`-fixed vectors, and that quotient is related to no `π a`. So `X = 0`.
   - `s = insert a s'`. `hSplit` for `π a` writes `X` as a coproduct of `Y true` in the
     block of `π a` and `Y false` with no irreducible subquotient related to `π a`. The
     retractions `boolCofanRetraction` (module-level identity `boolCofan_id_eq`) make both
     summands quotients of `X`. So both are finitely generated and generated by `K`-fixed
     vectors, and the irreducible subquotients of `Y false` are subquotients of `X`
     (`smoothSubquotientTransitivity`). Those with nonzero `K`-fixed vectors are related
     to some `π b` with `b ∈ s'`, since `b = a` is excluded. By induction `Y false` is
     Noetherian. `Y true` is Noetherian by step 5. A `Bool`-indexed coproduct of
     Noetherian representations is Noetherian (`SmoothRep.isNoetherian_of_boolCofan`,
     from the jointly injective retractions and `NoetherianRepresentation.of_jointlyInjective`).

   The claim applies to `A` with `s` the whole of `C`. An irreducible subquotient `D` of
   `A` with nonzero `K`-fixed vectors is cuspidal by step 1, so its class lies in `C`. It
   is then related to the representative of its class (`rationalIrreducibleInertiaClass_eq_iff`).
5. **Blocks** (`CuspidalSupport.isNoetherian_of_rationalInertiaBlockProperty`). Let `Y`
   be finitely generated in the block of an irreducible cuspidal `π`. `hRes` and
   `rationalNormKernelConstituent_of_finiteRestriction` give an irreducible
   subrepresentation `ρ` of the restriction of `π` to `⁰G`. `hHom` gives that `Π` lies in
   the block of the lifted `π` and that `E = Hom(Π, •)` is an equivalence to
   `ModuleCat (End Π)ᵐᵒᵖ`, and `hEnd` that `(End Π)ᵐᵒᵖ` is Noetherian
   (`fullSubcategoryEndRingEquiv` identifies the endomorphism ring in the block with the
   ambient one). `Y` lies in the block of the lifted `π`, because `π` and its lift are
   isomorphic and the block depends only on the inertia class
   (`rationalInertiaBlockProperty_iff_of_related`). The module
   `CategoryTheory/Renard/SubobjectOrderIsoTransfer` gives order isomorphisms of
   subobject lattices, from `Y` in the smooth category to `Y` in the block (the block is
   closed under subobjects) and from there to `E Y`. Along them Renard finite type passes
   from `Y` to `E Y`. So `E Y` is a finitely generated module over a Noetherian ring
   (`ModuleFiniteType.finiteType_iff_finite`), hence Noetherian
   (`ModuleNoetherian.object_iff`), and Noetherianity passes back to `Y`
   (`SmoothRep.renardFiniteType_iff`, `SmoothRep.renardNoetherian_iff`).

The proof of `smoothRepNoetherianCategory_of_universeLift` is the transfer already
described. Unions come from `SmoothRep.hasAllSubobjectUnions`. A finite-type `X` has a
finitely generated carrier lift, the lift is Noetherian by the hypothesis, and `X` is
the image of the lift under `universeLiftEquiv`.

## Provenance

The route follows Renard's first paragraph of the VI.7.5 proof, restricted to
supercuspidal representations, which is all that `smoothRepNoetherianCategory_of_inputs`
needs. Renard uses the product decomposition of VI.3.5 over all inertia classes. The
formal proof instead uses finitely many individual VI.3.3.1 splittings, selected by the
VI.3.4 finiteness remark at the level `K` of a generating set. This replaces Renard's
remark that an object of finite type has only finitely many nonzero components, and avoids
the large product. The universe transfer and the general lemmas (fixed-vector generation,
`Bool`-indexed coproducts, irreducible quotients of finitely generated representations)
are elementary and not stated by Renard. The irreducible quotient lemma repeats the
argument of the published
`Aubert.General.JacquetCommonConstituent.exists_irreducible_quotient_of_moduleFinite`, so
that the heavier module need not be imported.

Inputs remaining open for an unconditional proof: the seven premises of
`supercuspidalFiniteTypeNoetherian_of_inputs`, plus the inputs of
`smoothRepNoetherianCategory_of_inputs` for the Proposition.
