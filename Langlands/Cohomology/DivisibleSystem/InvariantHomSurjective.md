# Surjectivity of the Hom transitions out of invariants

Author: Worker 61. Built on the published modules
`Langlands.Representation.Induction.QuotientAdjunction`
(`coinvariantsInflationAdjunction`, `invariantsToCoinvariantsNatTrans`,
`isIso_invariantsToCoinvariantsNatTrans_app`),
`Langlands.Cohomology.DivisibleSystem.HomSurjective` (`PowTorsionProjective`,
`homSystem_map_surjective`, `isMittagLeffler_homSystem`,
`towerHomEval_surjective`),
`Langlands.Cohomology.DivisibleSystem.PowTorsionProjective`
(`powTorsionProjective_obj_of_adjunction`, `powTorsionProjective_of_iso`) and
`Langlands.Cohomology.DivisibleSystem.InvariantHomSystem`, which is imported
for the notation `T^S` and the companion isomorphism
`invariantsHomSystemIso`. Through these imports it uses
`DivisibleSystem`, `DivisibleSystem.epi_projection`, `DivisibleSystem.degree`,
`DivisibleSystem.mapLeftExact` (`LeftExact`), `DivisibleSystem.mapComplexes`
(`Sections`), `homSystem` and `towerHomEval` (`HomSystem`),
`invariantsToCoinvariants` (`InvariantRestriction`), and from
`Langlands.Cohomology.DivisibleSystem.Invariants` the instances making
`Rep.quotientToInvariantsFunctor k S` additive and limit-preserving (needed by
`mapLeftExact`), `smoothQuotientInvariants`, `epi_toRep_map_projection_f` and
`quotientInvariantsComplexes`. From Mathlib it uses
`Rep.quotientToInvariantsFunctor`, `Rep.quotientToCoinvariantsFunctor`,
`Functor.preservesEpimorphisms_of_adjunction`, `Functor.map_epi`, `asIso`,
`IsIso.hom_inv_id` and `Functor.IsMittagLeffler`.

All new names are in the namespace `Langlands.Cohomology.DivisibleSystem`.
Unless stated otherwise, `k : Type u` is a commutative ring, `G : Type v` a
group and `S` a normal subgroup of `G`, and all representations have carriers
in one universe `w` (`Rep.{w}`).

## Conventions

For a representation `A` of `G`, `invariantsToCoinvariants A.ρ S` is the
published map from the `S`-invariants to the `S`-coinvariants of `A` (an
`S`-invariant vector is sent to its class). It is the component at `A` of
`invariantsToCoinvariantsNatTrans k S`, a natural transformation from
`Rep.quotientToInvariantsFunctor k S` to `Rep.quotientToCoinvariantsFunctor k S`,
both functors to `Rep k (G ⧸ S)`. "Bijectivity at `A`" below means
`Function.Bijective (invariantsToCoinvariants A.ρ S)`.

`PowTorsionProjective ℓ m P` is the published hypothesis that every morphism
from `P` to the target of an epimorphism whose source is killed by `ℓ ^ m`
lifts along that epimorphism.

For an `ℓ`-divisible system `T` in `Rep k G` and a proof `hT` that for all
`m' ≤ m` the map induced on `S`-invariants by the projection `T m ⟶ T m'` is an
epimorphism, `T^S` denotes `T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT`,
as in the published `InvariantHomSystem`. `W` is an `ℓ`-divisible system in
`Rep k (G ⧸ S)`, and `homSystem k T^S W` is the inverse system of `k`-modules
`m ↦ Hom((T m)^S, W m)` of `HomSystem`.

## Epimorphisms and relative projectivity on invariants

- `epi_quotientToInvariantsFunctor_map S f hA hB`: for an epimorphism
  `f : A ⟶ B` in `Rep k G` with bijectivity at `A` (`hA`) and at `B` (`hB`),
  the induced map of `S`-invariants is an epimorphism. Proof: the components of
  `invariantsToCoinvariantsNatTrans k S` at `A` and `B` are isomorphisms
  (`isIso_invariantsToCoinvariantsNatTrans_app`), so by naturality the map on
  invariants is the map on coinvariants composed with isomorphisms; the
  coinvariants functor preserves epimorphisms because it is a left adjoint
  (`coinvariantsInflationAdjunction`,
  `Functor.preservesEpimorphisms_of_adjunction`).
- `powTorsionProjective_quotientToCoinvariants S hP`: if
  `PowTorsionProjective ℓ m P`, then the `S`-coinvariants of `P` satisfy
  `PowTorsionProjective ℓ m`. This is the published
  `powTorsionProjective_obj_of_adjunction` for
  `coinvariantsInflationAdjunction`, whose right adjoint (inflation) is
  additive and preserves epimorphisms.
- `powTorsionProjective_quotientToInvariants S hP hbij`: if moreover
  bijectivity holds at `P`, the `S`-invariants of `P` satisfy
  `PowTorsionProjective ℓ m`, by `powTorsionProjective_of_iso` along the
  inverse of the isomorphism `(invariantsToCoinvariantsNatTrans k S).app P`.

## The system of invariants

Let `T` be an `ℓ`-divisible system in `Rep k G` and `hbij` the hypothesis
that bijectivity holds at `T m` for every `m`.

- `epi_quotientToInvariantsFunctor_map_projection k S T hbij h`: for `m' ≤ m`
  (`h`), the map induced on `S`-invariants by the projection `T m ⟶ T m'`
  is an epimorphism. It is `epi_quotientToInvariantsFunctor_map` for the
  projection, which is an epimorphism (`epi_projection`). This is the
  hypothesis `hT` of `mapLeftExact` for the `S`-invariants functor.
- `invariantsSystem k S T hbij : DivisibleSystem (Rep k (G ⧸ S)) ℓ`
  (definition): `T.mapLeftExact (Rep.quotientToInvariantsFunctor k S)` with
  the hypothesis supplied by the previous lemma, that is the system
  `m ↦ (T m)^S` of `S`-invariants as representations of `G ⧸ S`.
  `invariantsSystem_eq_mapLeftExact` states that it equals `T^S` for every
  proof `hT` (by `rfl`, since proofs of a proposition are definitionally
  equal), so the lemmas below, stated for `T^S` with an arbitrary `hT`, apply
  to it. `invariantsSystem_obj` states that its level `m` is the
  `S`-invariants of `T m`.

## Hom systems out of the invariants

Assume in addition `hP : ∀ m, PowTorsionProjective ℓ m (T.obj m)`. The lemmas
below take `hbij`, an arbitrary `hT` and `hP`.

- `powTorsionProjective_mapLeftExact_quotientToInvariants k S T hbij hT hP m`:
  level `m` of `T^S` satisfies `PowTorsionProjective ℓ m`
  (`powTorsionProjective_quotientToInvariants` at `T m`).
- `invariants_homSystem_map_surjective k S T hbij hT hP W φ`: every
  transition `(homSystem k T^S W).map φ`, that is every map
  `Hom((T m)^S, W m) → Hom((T m')^S, W m')` for `m' ≤ m`, is surjective.
- `isMittagLeffler_invariants_homSystem k S T hbij hT hP W`: the inverse
  system `homSystem k T^S W`, composed with the forgetful functor to types,
  satisfies the Mittag-Leffler condition.
- `invariants_towerHomEval_surjective k S T hbij hT hP W n`: every morphism
  `(T n)^S ⟶ W n` is the level-`n` component of a morphism of inverse systems
  `T^S.tower ⟶ W.tower` (surjectivity of the published `towerHomEval`).

These are the published `homSystem_map_surjective`, `isMittagLeffler_homSystem`
and `towerHomEval_surjective` for the system `T^S`, whose hypothesis is the
first lemma of this section. Under `hbij`, the published
`invariantsHomSystemIso` identifies `homSystem k T^S W` with the Hom system out
of `T` into the inflation of `W`; the results are not restated for that
system.

## Systems of complexes

`K` is an `ℓ`-divisible system in `CochainComplex (Rep k G) ℕ` and `hbij` the
hypothesis that bijectivity holds at the degree `q` term of `K m` for all `m`
and `q`.

- `epi_quotientToInvariantsFunctor_map_projection_f k S K hbij h q`: the map
  induced on `S`-invariants by the degree `q` component of the projection
  `K m ⟶ K m'` is an epimorphism. This is the hypothesis `hK` of
  `mapComplexes` for the `S`-invariants functor.
- `invariantsComplexSystem k S K hbij` (definition): the system
  `K.mapComplexes (Rep.quotientToInvariantsFunctor k S)` of complexes of
  degreewise `S`-invariants, with the hypothesis supplied by the previous
  lemma. `invariantsComplexSystem_eq_mapComplexes` states that it equals
  `K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK` for every proof
  `hK` (by `rfl`), and `invariantsComplexSystem_obj_X` that its degree `q`
  term at level `m` is the `S`-invariants of the degree `q` term of `K m`.
- For a degree `j`, an arbitrary `hK`, and
  `hP : ∀ m, PowTorsionProjective ℓ m ((K.obj m).X j)`:
  `degree_invariants_homSystem_map_surjective`,
  `isMittagLeffler_degree_invariants_homSystem` and
  `degree_invariants_towerHomEval_surjective` are the three statements of the
  previous section for the degree `j` system of
  `K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK` and `W`. That
  degree `j` system is by definition the system of `S`-invariants of
  `K.degree j`, so they are the previous lemmas for `T = K.degree j`; they
  take the bijectivity hypothesis `hbij` for all degrees, of which only
  degree `j` is used.

## Smooth complexes

Here `R : Type uR` is a commutative ring, `G : Type uG` a topological group,
`H` a normal subgroup of `G`, and `K` an `ℓ`-divisible system of cochain
complexes of smooth representations (`SmoothRep.{uR, uG, uV} R G`).

- `epi_smoothQuotientInvariants_map_projection_f_of_bijective K H hbij h q`: if
  `invariantsToCoinvariants` is bijective on the underlying representation
  (`SmoothRep.toRep`) of every term of every `K m` (`hbij`), the map induced
  on `H`-invariants by the degree `q` component of the projection
  `K m ⟶ K m'` is an epimorphism. This is the hypothesis of the published
  `quotientInvariantsComplexes K H`. Proof: the underlying map of the
  projection is an epimorphism (`epi_toRep_map_projection_f`), then
  `epi_quotientToInvariantsFunctor_map`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312
(one-based PDF page 14; Worker 61 read the rendered scanned page), after the
definition of `T_m(j, ẽ)` and the maps (4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)`:
"But we have seen in §2 that the maps `C^j_{m+1}(ẽ)^{H_p} → C^j_m(ẽ)^{H_p}`
are surjective. Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are
both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are
surjective for all `m`."

The surjectivity from §2 refers to printed p.305 (one-based PDF page 7, read
in the rendered scanned page), where `H ⊂ S(ẽ)` is an open normal pro-`p`
subgroup: "Since `p` is prime to `ℓ`, the functor `H^0(H, •)` is exact on
`ℓ`-primary torsion modules".

In our reading, `T` plays the role of the system of degree `j` terms
`C^j_m(ẽ)`, `G` and `S` the roles of `S(ẽ)` and `H_p ∩ S(ẽ)` (as in the
published `InvariantHomSystem`), `W` the role of the coefficients
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`, and the published hypothesis
`PowTorsionProjective` the role of freeness of the source. The bijectivity
of `invariantsToCoinvariants` replaces the hypothesis that `p` is prime to
`ℓ`: for the compact induction of a trivial representation from an open
subgroup `H ≤ S` of finite index in `S` it holds when that index is a unit
of `k` (published `bijective_invariantsToCoinvariants_compactInduced`), and
for Harris the index is a power of `p`. Harris obtains the surjectivity on
invariants from the exactness of `H^0(H, •)`; here it is derived from the
bijectivity hypothesis, through coinvariants, instead. Harris also uses the
freeness of the target `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`; the published
`homSystem_map_surjective` needs only the hypothesis on the source, the
target being an `ℓ`-divisible system. This correspondence, the route and all
definitions and proofs are ours; the module is derived.

## Scope

The module does not construct Harris's modules `C^j_m(ẽ)` or `T_m(j, ẽ)` or
the maps (4.10.3), does not prove that his modules are free or satisfy
`PowTorsionProjective`, and does not prove the exactness of pro-`p`
invariants on `ℓ`-primary torsion. The bijectivity hypotheses `hbij` and
the relative projectivity hypotheses `hP` are explicit. Morphisms are
`k`-linear over a fixed ring `k`, as in `HomSystem`; Harris's morphisms over
`𝒪/ℓ^m𝒪[S(ẽ)]` are compared only informally (the systems are killed by
`ℓ ^ m`). The Mittag-Leffler statements concern the Hom systems of single
degrees; the Hom complexes (4.10.2), the finiteness of the right-hand side of
(4.9) and the spectral sequence are not treated.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
