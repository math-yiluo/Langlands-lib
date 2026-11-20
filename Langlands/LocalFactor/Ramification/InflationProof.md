# Inflation from a finite Galois quotient preserves the Artin and Swan sums

Module `Langlands.LocalFactor.Ramification.InflationProof`.

## Result

`Langlands.Ramification.Padic.finiteGaloisConductorInflation` proves the Library
proposition `Langlands.Ramification.Padic.FiniteGaloisConductorInflationStatement TE TL K (V := V)`
(module `Langlands.LocalFactor.Ramification.InflationStatement`). Its type is

```
∀ {p : ℕ} [Fact p.Prime] {E : PadicField.{uE} p} {L : PadicField.{uL} p}
  (TE : E.TopologicalData) (TL : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K E.Carrier] [Algebra K L.Carrier] [Algebra E.Carrier L.Carrier]
  [IsScalarTower (Padic p) K E.Carrier] [IsScalarTower (Padic p) K L.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier] [IsScalarTower K E.Carrier L.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
  FiniteGaloisConductorInflationStatement TE TL K (V := V)
```

The universe levels `uK`, `uE`, `uL` and `uV` are independent. No hypothesis is added.
For `[IsGalois K E.Carrier] [IsGalois K L.Carrier]`, a representation
`ρ : Representation ℂ (E.Carrier ≃ₐ[K] E.Carrier) V` and the restriction
`π = AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E.Carrier`, the theorem
proves `artinConductor TL K (ρ.comp π) = artinConductor TE K ρ` and
`swanConductor TL K (ρ.comp π) = swanConductor TE K ρ`. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Idea

The Artin and Swan sums of a representation of `Gal(F/K)` only involve the lower groups
`G_i` with `i ≥ 0`. All of them lie in inertia. So they equal the sums of the
restriction of the representation to inertia, which the Library calls
`inertiaArtinConductor` and `inertiaSwanConductor`. The Library result
`inertiaConductors_eq_of_upperFixedDimension` (module
`Langlands.LocalFactor.Ramification.InertiaConductorProfile`) compares two such inertia
sums: they agree when the two fixed spaces of the upper groups `G^v` have the same
dimension at every `v ≥ 0`. Herbrand's theorem says that restriction maps the upper group
`Gal(L/K)^v` onto `Gal(E/K)^v`. Hence for `v ≥ 0` a vector is fixed by `Gal(L/K)^v`
acting through `ρ ∘ π` exactly when it is fixed by `Gal(E/K)^v` acting through `ρ`. The
two fixed spaces are equal, so their dimensions agree.

This is not Serre's proof. Serre (*Local Fields*, VI §2, Proposition 3) proves
`a_{G/N} = (a_G)^♮` from the lower-numbering quotient formula (IV §1, Proposition 3).
The proof here never compares lower groups of `L/K` and `E/K`.

## Fixed vectors (namespace `Langlands.Ramification.Padic.GaloisConductorInflation`)

These two lemmas hold for any group and any complex representation, with
`fixedVectors` from `Langlands.Representation.Smooth.Definitions`.

* `fixedVectors_comp_subtype_subgroupOf ρ hHN`: for subgroups `H ≤ N` of `G`,
  `fixedVectors (ρ.comp N.subtype) (H.subgroupOf N) = fixedVectors ρ H`. Both sides are
  the vectors fixed by every element of `H`. The proof unfolds the membership conditions
  and passes between `H.subgroupOf N` and `H` with `Subgroup.mem_subgroupOf`.
* `fixedVectors_comp_map ρ f H`: for a group homomorphism `f : G' →* G` and
  `H ≤ G'`, `fixedVectors (ρ.comp f) H = fixedVectors ρ (H.map f)`. An element of
  `H.map f` has the form `f h` with `h ∈ H` (`Subgroup.mem_map`), and conversely
  `f h ∈ H.map f` (`Subgroup.mem_map_of_mem`).

## Restriction to inertia (same namespace)

The variables are those of `Langlands.LocalFactor.Ramification.Galois`: a p-adic field
`F`, `T : F.TopologicalData`, a field `K` with
`[Algebra (Padic p) K] [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]`,
and a finite-dimensional complex vector space `V`.

* Four private lemmas, `integerAction_faithful`, `inertiaAction_faithful`,
  `integers_isNoetherianRing` and `automorphisms_finite`, prove that
  `F.Carrier ≃ₐ[K] F.Carrier` and `inertia T K` act faithfully on `T.Integers` through
  `integerAction T K` and `inertiaIntegerAction T K`, that `T.Integers` is Noetherian, and
  that `F.Carrier ≃ₐ[K] F.Carrier` is finite. The module `Galois` uses private lemmas
  with these statements (`integerAction_faithful`, `inertiaIntegerAction_faithful`,
  `integerRing_noetherian`, `automorphismGroup_finite`) to install the instances in the
  definitions of `artinConductor`, `swanConductor`, `inertiaArtinConductor` and
  `inertiaSwanConductor`. Because those lemmas are private, this module repeats them. The
  proofs of the first, third and fourth are copied from `Galois`. The second is proved
  directly: two elements of inertia that act in the same way on `T.Integers` agree on
  `F.Carrier`, because `F.Carrier` is the fraction field of `T.Integers`
  (`IsFractionRing.ringHom_ext`). All four are propositions, so the instances they give are
  definitionally the ones used in those definitions.
* `lowerRamificationGroup_le_inertia`: `lowerRamificationGroup T K i ≤ inertia T K` for
  every `i : ℕ`. This is `lowerRamificationGroup_zero` (`G_0` is inertia) with
  `lowerRamificationGroup_antitone`.
* `artinConductor_eq_finsum` and `swanConductor_eq_finsum` write the Galois-group sums as
  `artinConductor T K ρ = ∑ᶠ i, (g_i / g_0) · fixedCodimension … ρ (G_i)` and
  `swanConductor T K ρ = ∑ᶠ i, (g_(i+1) / g_0) · fixedCodimension … ρ (G_(i+1))`, where
  `g_i = lowerGroupOrder T K i` and `G_i = lowerRamificationGroup T K i`. With the
  instances above installed, `artinConductor T K ρ` is by definition
  `Ramification.artinConductor T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ρ`. The Library
  lemma `Ramification.artinConductor_eq_finsum` (module
  `Langlands.LocalFactor.Ramification.Conductor`) writes it as `∑ᶠ i, conductorTerm … i`,
  and each `conductorTerm` is the displayed term by definition (`rfl`). The Swan case
  uses `Ramification.swanConductor_eq_finsum` in the same way.
* `inertiaArtinConductor_eq_finsum` and `inertiaSwanConductor_eq_finsum` do the same for
  `inertiaArtinConductor T K ρ` and `inertiaSwanConductor T K ρ` with
  `ρ : Representation ℂ (inertia T K) V`. The terms are
  `(Nat.card (inertiaLowerGroup T K i) / Nat.card (inertiaLowerGroup T K 0)) · fixedCodimension (inertia T K) ρ (inertiaLowerGroup T K i)`
  and the same at `i + 1`.
* `fixedCodimension_inertiaLowerGroup ρ i`: for `ρ` a representation of the Galois group,
  `fixedCodimension (inertia T K) (ρ.comp (inertia T K).subtype) (inertiaLowerGroup T K i)`
  equals `fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (lowerRamificationGroup T K i)`.
  `inertiaLowerGroup T K i` is by definition
  `(lowerRamificationGroup T K i).subgroupOf (inertia T K)`, so
  `fixedVectors_comp_subtype_subgroupOf` with `lowerRamificationGroup_le_inertia` makes the
  two fixed spaces equal.
* `artinConductor_eq_inertiaArtinConductor ρ`:
  `artinConductor T K ρ = inertiaArtinConductor T K (ρ.comp (inertia T K).subtype)`, and
  `swanConductor_eq_inertiaSwanConductor ρ` is the Swan analogue. Both sides are written
  as `finsum`s by the four lemmas above, and they are compared term by term
  (`finsum_congr`). The Library lemma `card_inertiaLowerGroup` (module
  `InertiaConductorProfile`) gives `Nat.card (inertiaLowerGroup T K i) = lowerGroupOrder T K i`,
  at `i` and at `0`. `fixedCodimension_inertiaLowerGroup` gives the codimensions.
* `upperRamificationGroup_le_inertia`: for `0 ≤ v`,
  `upperRamificationGroup T K v ≤ inertia T K`, from `upperRamificationGroup_zero`
  (`G^0` is inertia) and `upperRamificationGroup_antitone` (module
  `Langlands.LocalFactor.Ramification.Herbrand.Finite`).
* `inertiaUpperFixedVectors_comp_subtype ρ hv`: for `0 ≤ v`,
  `inertiaUpperFixedVectors T K (ρ.comp (inertia T K).subtype) v = fixedVectors ρ (upperRamificationGroup T K v)`.
  By definition (module `Langlands.LocalFactor.Ramification.Breaks`) the left side is
  `fixedVectors (ρ.comp (inertia T K).subtype) ((upperRamificationGroup T K v).subgroupOf (inertia T K))`,
  so this is `fixedVectors_comp_subtype_subgroupOf` with `upperRamificationGroup_le_inertia`.
  It does not use the finite dimensionality of `V`, which is omitted from its hypotheses.

## Herbrand's theorem for the base field `K` (same namespace)

* `map_upperRamificationGroup TE TL K v hv`: in the tower of the target, without the
  hypothesis `IsScalarTower (Padic p) E.Carrier L.Carrier`, and for
  `[IsGalois K E.Carrier] [IsGalois K L.Carrier]` and `-1 ≤ v`,
  ```
  (upperRamificationGroup TL K v).map
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E.Carrier) =
    upperRamificationGroup TE K v
  ```
  The Library proves Herbrand's theorem as
  `HerbrandBridge.upperRestrictionCompatibility K' L E TL TE`
  (module `Langlands.LocalFactor.Ramification.Herbrand.TowerProof`), which states the
  Library proposition `UpperRestrictionCompatibility` (module
  `Langlands.LocalFactor.Ramification.Herbrand.ArithmeticStatement`), that is, exactly
  this equality for every `v ≥ -1`. There the base field `K'` is a `PadicField`. The
  proof therefore packages `K` as `K' := PadicField.ofField K` (module
  `Langlands.LocalField.Definitions`), whose carrier is `K` itself. This needs
  `FiniteDimensional (Padic p) K`, which holds because the injective linear map
  `IsScalarTower.toAlgHom (Padic p) K E.Carrier` embeds `K` into the finite-dimensional
  `E.Carrier` (`FiniteDimensional.of_injective`). The algebra, scalar-tower and Galois
  instances over `K'.Carrier` are the given instances over `K`, introduced with `let` and
  `have`. The extra hypothesis `IsGalois E.Carrier L.Carrier` of
  `upperRestrictionCompatibility` comes from Mathlib's `IsGalois.tower_top_of_isGalois`.
  Since `K'.Carrier` is `K` by definition, the conclusion is the displayed equality.

## Main theorem (namespace `Langlands.Ramification.Padic`)

`finiteGaloisConductorInflation`: let `ρ` and `π` be as in the statement.

1. For every `v ≥ 0`,
   `inertiaUpperFixedVectors TL K ((ρ.comp π).comp (inertia TL K).subtype) v` equals
   `inertiaUpperFixedVectors TE K (ρ.comp (inertia TE K).subtype) v`. By
   `inertiaUpperFixedVectors_comp_subtype` the two sides are
   `fixedVectors (ρ.comp π) (upperRamificationGroup TL K v)` and
   `fixedVectors ρ (upperRamificationGroup TE K v)`. `fixedVectors_comp_map` rewrites
   the first as `fixedVectors ρ ((upperRamificationGroup TL K v).map π)`, and
   `map_upperRamificationGroup` (with `-1 ≤ v`) turns it into the second.
2. Equal subspaces have equal `finrank`. So
   `inertiaConductors_eq_of_upperFixedDimension TE TL K` applies to the inertia
   representations `ρ.comp (inertia TE K).subtype` and
   `(ρ.comp π).comp (inertia TL K).subtype`. It gives equal inertia Artin sums and equal
   inertia Swan sums.
3. `artinConductor_eq_inertiaArtinConductor` and `swanConductor_eq_inertiaSwanConductor`,
   applied to `TL` with `ρ.comp π` and to `TE` with `ρ`, turn these into the two equalities
   of the statement.

## Imported Library results

Module `Langlands.LocalFactor.Ramification.InflationStatement`:
`FiniteGaloisConductorInflationStatement` (the target).
Module `Langlands.LocalFactor.Ramification.Galois`: `integerAction`, `inertiaIntegerAction`,
`inertia`, `lowerRamificationGroup`, `lowerRamificationGroup_zero`,
`lowerRamificationGroup_antitone`, `inertiaLowerGroup`, `artinConductor`, `swanConductor`,
`inertiaArtinConductor`, `inertiaSwanConductor`.
Module `Langlands.LocalFactor.Ramification.Conductor`: `fixedCodimension`, `conductorTerm`,
`Ramification.artinConductor_eq_finsum`, `Ramification.swanConductor_eq_finsum`.
Module `Langlands.LocalFactor.Ramification.Herbrand.Finite`: `lowerGroupOrder`,
`upperRamificationGroup`, `upperRamificationGroup_zero`, `upperRamificationGroup_antitone`.
Module `Langlands.LocalFactor.Ramification.Breaks`: `inertiaUpperFixedVectors`.
Module `Langlands.LocalFactor.Ramification.InertiaConductorProfile`: `card_inertiaLowerGroup`,
`inertiaConductors_eq_of_upperFixedDimension`.
Module `Langlands.LocalFactor.Ramification.Herbrand.TowerProof`:
`HerbrandBridge.upperRestrictionCompatibility`.
Module `Langlands.LocalField.Definitions`: `PadicField`, `PadicField.ofField`.
Module `Langlands.Representation.Smooth.Definitions`: `fixedVectors`.
Mathlib: `AlgEquiv.restrictNormalHom`, `IsGalois.tower_top_of_isGalois`,
`FiniteDimensional.of_injective`, `IsScalarTower.toAlgHom`,
`Module.Finite.of_restrictScalars_finite`, `IsFractionRing.ringHom_ext`,
`Subgroup.mem_subgroupOf`, `Subgroup.mem_map`, `Subgroup.mem_map_of_mem`, `finsum_congr`.

## Literature

J.-P. Serre, *Local Fields* (1979), registered as `serre-1979-local-fields`
(`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`).

* VI §2, printed p. 101 (PDF p. 108): Corollary 1′ to Proposition 2 gives
  `f(χ) = Σ_i (g_i/g_0) codim V^(G_i)`, the Library's Artin sum. Proposition 3
  (`a_{G/N} = (a_G)^♮`) and its Corollary (`f(φ) = f(φ′)` for a class function `φ` on
  `G/N` and its inflation `φ′`) are the classical form of the statement proved here, for
  `G = Gal(L/K)` and `N = Gal(L/E)`.
* IV §3, printed p. 74 (PDF p. 81): the upper numbering `G^v = G_(ψ(v))` and
  Proposition 14, `(G/H)^v = G^v H/H`. This is Herbrand's theorem in the form used here.
  Its proof on printed p. 75 (PDF p. 82) uses Lemma 5 and Proposition 15. In the Library
  it is `HerbrandBridge.upperRestrictionCompatibility`, which this module imports and does
  not reprove.

Serre derives Proposition 3 from IV §1, Proposition 3 (the lower-numbering formula for a
quotient). The proof in this module instead compares the upper-numbering fixed-space
profiles through Proposition 14, and it uses the Library's integral formula for the
inertia sums in `inertiaConductors_eq_of_upperFixedDimension`.
