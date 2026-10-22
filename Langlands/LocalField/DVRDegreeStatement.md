# DVR ramification-inertia lower degree bound

`Langlands.LocalField.DVRDegreeLowerBound` is the proposition that a local
extension of discrete valuation rings satisfies

`e(S/R) * f(S/R) ≤ [Frac(S) : Frac(R)]`

when the compatible extension of fraction fields has finite degree.
The declaration is a `Prop`-valued definition; this module states the
inequality and supplies no proof of it.

The four carriers `R : Type uR`, `S : Type uS`, `K : Type uK`, and
`L : Type uL` have independent universe parameters. All carriers, structures,
and hypotheses are quantified inside the proposition:

- `R` and `S` are commutative integral domains with
  `IsDiscreteValuationRing` instances. Mathlib's DVR class supplies the local
  ring and principal ideal ring structures and excludes fields.
- `Algebra R S` specifies the ring map. The assumption
  `IsLocalHom (algebraMap R S)` says it is local, so the maximal ideal of
  `S` contracts to the maximal ideal of `R`.
- `K` and `L` are fields. The structures `Algebra R K` and
  `IsFractionRing R K` identify `K` as a fraction field of `R`; likewise,
  `Algebra S L` and `IsFractionRing S L` identify `L` as a fraction field
  of `S`.
- `Algebra K L` specifies the extension whose degree occurs on the right.
  The additional `Algebra R L` and the two hypotheses
  `IsScalarTower R K L` and `IsScalarTower R S L` require the paths
  `R → K → L` and `R → S → L` to equal that same map `R → L`.
- `Module.Finite K L` asserts that this field extension is finite
  dimensional.

The left side uses the actual maximal ideal `IsLocalRing.maximalIdeal S`
and the current Mathlib invariants `Ideal.ramificationIdx` and
`Ideal.inertiaDeg`. For a prime ideal `q` of an `R`-algebra `S`, the former
is the natural-number value of the length of the localized quotient by
the extension of `q.under R`; the latter is the `Module.finrank` of the
corresponding residue-field extension. Here the local-map hypothesis
identifies `q.under R` with the maximal ideal of `R`. The right side is
`Module.finrank K L` for the specified compatible algebra structure.

There is no assumption that `S` is finite as an `R`-module, that either
ring or field is complete, or that the field extension is separable.
No equality of degrees or instance of the desired inequality is a
hypothesis.

This is internal derived project content, specified by Worker 107 and
formalized by Worker 109 as a prerequisite for
`Langlands.Global.AdelicFunctoriality.CompletedLocalDegreeLowerBound`.
It isolates the general DVR inequality needed for the completed local
degree argument, where finite dimensionality of the fraction-field
extension is available but finiteness of the integer-ring extension has
not been established. It is not a transcription of a separately cited
literature result. The definitions of the invariants are imported from
Mathlib's `RingTheory.RamificationInertia.Ramification` and
`RingTheory.RamificationInertia.Inertia` modules in the pinned environment.
A separate proof must establish this proposition. Comparisons between
completed and global ramification and inertia invariants belong to the
parent completed-local-degree task and are outside this statement.
