# Uniqueness of ordinary polarized full-level data over a discrete valuation ring

`Langlands.AbelianScheme.PolarizedFiniteLevel.DiscreteValuationDatumUniquenessStatement`
is a proposition definition in universe `u`. It is a statement only. The module
proves nothing.

## The statement

The proposition quantifies over the following data:

- `P : Prerequisites.{u}` and natural numbers `g d n`;
- a discrete valuation ring `R : Type u` (`CommRing`, `IsDomain`,
  `IsDiscreteValuationRing`);
- a field `K : Type u` with `[Algebra R K] [IsFractionRing R K]`, so `K` is a
  fraction field of `R`;
- a proof that the image of `n` in `R` is a unit, `IsUnit (n : R)`;
- two data `a b : Datum P (Spec (CommRingCat.of R)) g d n`. A `Datum` is the
  Library's ordinary polarized full-level datum (module
  `Langlands.AbelianScheme.PolarizedFiniteLevel.Data`): an abelian scheme of
  relative dimension `g`, a polarization of degree square `d`, and an ordered
  full level-`n` tuple of torsion sections.

Write `ι = Spec.map (CommRingCat.ofHom (algebraMap R K))`, the inclusion
`Spec K ⟶ Spec R` of the generic point. The statement says: if the pullbacks
`a.pullback ι` and `b.pullback ι` (Library `Datum.pullback`, module `Pullback`) are
`Isomorphic`, then `a` and `b` are `Isomorphic`. `Isomorphic` is the Library's
relation (module `Data`): there is a `PolarizedIso`, an isomorphism of the
abelian schemes that carries the polarization to the polarization (through the
dual map) and each ordered level section to the corresponding one.

### On the hypothesis `IsUnit (n : R)`

The statement only assumes this hypothesis; it never derives it. Assuming it
makes the statement weaker. The derivation below does not use it. It is assumed
because the only application (below) supplies it: there `Spec R` is a level base
over `Spec ℤ[1/n]`.

## Provenance

The statement is derived from the Néron mapping property of abelian schemes.

Bosch–Lütkebohmert–Raynaud, *Néron Models*, registered source
`bosch-lutkebohmert-raynaud-1990-neron-models` (content SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`). Section 1.2
works over a Dedekind scheme `S` with ring of rational functions `K`; the
spectrum of a discrete valuation ring is such a scheme.

- §1.2, Definition 1 (printed p.12, PDF p.19), the Néron mapping property: "For
  each smooth S-scheme Y and each K-morphism u_K : Y_K → X_K there is a unique
  S-morphism u : Y → X extending u_K."
- §1.2, Proposition 8 (printed p.15, PDF p.22): "Let X be an abelian scheme over
  S. Then X is a Néron model of its generic fibre X_K."

The derivation of the statement from these two results is as follows.

1. Let `e_K` be a polarized isomorphism of the generic fibres. Both abelian
   schemes are smooth over `Spec R`. By Proposition 8 and the mapping property,
   `e_K` and its inverse extend to morphisms `φ : A_a → A_b` and
   `ψ : A_b → A_a` over `Spec R`.
2. `ψ ∘ φ` and the identity both extend `e_K⁻¹ ∘ e_K = id`. By the uniqueness in
   Definition 1 they are equal. The same holds for `φ ∘ ψ`. So `φ` is an
   isomorphism.
3. The polarization condition and the level conditions are equalities of
   morphisms from a flat `R`-scheme (the abelian scheme `A_a`, or `Spec R`
   itself for a section) to a separated `R`-scheme. These equalities hold after
   base change to `K`, because `e_K` satisfies them there. A morphism from a flat
   `R`-scheme to a separated one is determined by its generic fibre, because
   the generic fibre is schematically dense. So these equalities hold over `R`.

## Role

This statement is the moduli input of the proved definition
`largeLevelSeparated_of_datumUniqueness` (module
`LargeLevelSeparatedDiscreteValuationReduction`). That definition uses it in
universe `0` together with `LargeLevelFiniteTypeStatement` to prove
`LargeLevelSeparatedStatement`, through the noetherian valuative criterion for
separatedness. There, two lifts in a valuative square with a discrete valuation
ring `R` give two data over `Spec R`. Their pullbacks to `Spec K` are isomorphic,
because both lifts restrict to the same `K`-point.

## Intended Lean proof (not established)

The Library module `Langlands.AbelianScheme.RelativeHomNeronExtension` has the
tools for steps 1–3 above:

- `baseChange_map_surjective` (over a discrete valuation ring `V` with fraction
  field `K`) shows that every homomorphism of generic fibres of group schemes
  `G → H` extends, when `G` is smooth and `H` satisfies FLT's abelian scheme
  property bundle. `abelianSchemePropertyBundle_baseChange` in the same module
  supplies that bundle for base changes of abelian schemes.
- `genericFibre_map_injective` shows that base change to the generic fibre is
  injective on morphisms from a flat scheme to a separated scheme over `V`.

The polarization equality would also use the naturality of the dual base-change
comparison, `DualWitness.baseChangeIso_naturality` (module `PullbackCoherence`).
The level equality would use the description of pulled-back sections,
`Datum.pullback_level` (module `Pullback`). This plan is not part of this
candidate. Moving between the Library's `AbelianScheme` over `Spec R` and the
group schemes of `baseChange_map_surjective` may need further adapters.
