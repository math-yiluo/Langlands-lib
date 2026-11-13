# Reduction of the unramified valuation descent to the Galois-fixed locus

Author: Worker 4707 (with Worker 4356, whose modules it uses); restructured by Worker 5553.

Lean module: `Langlands.Geometry.Building.UnramifiedValuationDescentReduction`.

This module proves that four statements about the Galois-fixed points of the special
apartment over `K = inertiaFixedField F` imply the published
`UnramifiedValuationDescentStatement` (Kaletha–Prasad, Construction 9.6.1, Lemma 9.6.3 and
Theorem 9.6.5). The four statements are:

- the published `UnramifiedGaloisFixedApartmentStatement` (module
  `UnramifiedSpecialApartmentStatement`, KP §9.2.1): a Galois-stable class has a Galois-fixed
  point;
- `UnramifiedFixedLeviTransportStatement` (module of the same name): `N(F)`-transport of
  Galois-fixed points through the Levi subgroup;
- `UnramifiedFixedCentralizerCompatibilityStatement` (module
  `UnramifiedFixedLocusStatement`): V 6 on `Z(F)` at the Galois-fixed points;
- `UnramifiedFixedOppositeStatement` (same module): V 5 at the Galois-fixed points.

None of them is proved here. Task 5513 proves the first one; its proof module is not imported
here, so this module depends only on published statements. Notation is as in the Markdown of
`UnramifiedValuationDescentStatement`: `fixed x` is invariance of `x : D.Apartment` under
`RootFunctionFamily.galoisAction F K T G σ` for every `σ : K ≃ₐ[F] K`, and `φ x` is
`torusFieldRestrictedRootFunctionFamily … (D.isRootDatumValuation_of_mem x.mem) f_K`.

## Helper lemmas

They are stated for an arbitrary field extension `K/k`, split `S`, `t : S ⟶ T` and
`jT : T.toGrp ⟶ G`.

- `galoisCocharacterAction_descentCocharacterMap`: `descentCocharacterMap k K t hS v` (the
  push-forward to `V(T_K)` of a real cocharacter `v` of `S`) is fixed by
  `galoisCocharacterAction k K T σ`. The proof is by induction on tensors, using
  `cocharacterLattice.baseChange_comp` and `cocharacterLattice.galoisRepresentation_baseChange`.
- `torusFieldRestrictedRootFunctionFamily_descent_vadd`: if `ψ = descentCocharacterMap k K t hS v +ᵥ φ`,
  then the torus-then-field restriction of `ψ` is `v +ᵥ` the restriction of `φ`. The proof
  combines `torusRestrictedRootFunctionFamily_congr`, `torusRestrictedRootFunctionFamily_vadd`
  and `RootFunctionFamily.fieldRestrict_vadd`.

## `unramifiedValuationDescent_core`

This theorem takes the data of the target as explicit binders: `F`, `G`, `hG`, the affine and
smooth instances, `S`, `iS`, `hiS`, `T`, `iT`, `f`, `hf`, `hiT`, the monomorphism instances,
`hE` and `D`. It also takes four hypotheses for this data, with `fixed` and `φ` written out:

- `hfix`: some `x0 : D.Apartment` is fixed;
- `hB`: for every `n : normalizerPoints iS` and fixed `x` there is a fixed `y` with
  `D.apartmentMap y = n_K • D.apartmentMap x` and `φ y = n • φ x`;
- `hC`: for every `CS : CentralizerDatum iS` and fixed `x`,
  `IsCentralizerCompatible iS CS.j CS.s CS.bijective (φ x)`;
- `hD`: V 5 for `φ x` at every fixed `x`.

Its conclusion is the conclusion of the target for this data. The proof:

1. `hfix` gives a fixed point `x0`.
2. Shifts. For `n ∈ N(F)`, `hB` gives a fixed `y` with `φ y = n • φ x0`. Worker 4356's
   `unramified_exists_descent_vadd_of_galoisFixed` writes `y = descentCocharacterMap v + x0`
   for some `v ∈ V(S)`, so `n • φ x0 = v +ᵥ φ x0` by the helper lemma.
3. Valuation. The published constructor `torusFieldRestrictedValuationOfOriginalPointShifts`
   turns `φ x0` into a valuation of the root datum of `(G, S)`. It is applied with
   `ω = MaximalUnramified.realOrderCharacter F` (nontrivial on `F` by
   `realOrderCharacter_nontrivial_on_base`), the shifts of step 2
   (`torusFieldOriginalPointShifts_iff`), opposite factor pairs for `iS` (published
   `rootRankOneFactorization`) and V 5 from `hD`.
4. Compatibility with `S(F)`. The published
   `torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible`, with
   `realOrderCharacter_base`, shows that `φ x0` is compatible with `localFieldOrder F`.
5. `DS` is the published `KPApartmentData.ofNormalizerShifts` of `φ x0`, whose carrier is the
   `V(S)`-orbit of `φ x0`. `CS` is `CentralizerDatum.ofValuationComparison` with the published
   `Cartan.centralizerValuationComparison`.
6. Clause 2. A member `v +ᵥ φ x0` of the orbit is `φ` of the fixed point
   `descentCocharacterMap v + x0`. It lies in `D` by `D.vadd_mem` and is fixed by
   `RootFunctionFamily.galoisAction_vadd` and the first helper lemma. Conversely, every
   fixed `x` is such a translate by the torsor lemma.
7. Clause 1 is `hC` at `x0`, propagated to the class by
   `KPApartmentData.isCentralizerCompatible_iff_of_mem`. Clause 3 is Worker 4356's
   `unramified_eq_of_torusFieldRestricted_eq`. Clause 4 is `hB`.

## Bridges and the final reduction

`UnramifiedValuationDescentFixedLocusReductionStatement` is an internal closed `Prop`
definition of the four-premise implication below. It packages the supporting reduction
for a native statement contribution. The theorem retains its explicit four-premise type,
which is definitionally this proposition. This packaging adds no premise and does not
prove any of the three new fixed-locus statements.

- `unramifiedGaloisFixedApartment_apply` restates `UnramifiedGaloisFixedApartmentStatement`
  for fixed explicit data. Its stability hypothesis is supplied by Worker 4356's
  `unramifiedGaloisStable_of_isOmegaCompatible` (module `UnramifiedApartmentGaloisStability`):
  a class with full V 6 is stable under `Aut(K/F)`.
- `unramifiedFixedCentralizerCompatibility_apply` and `unramifiedFixedOpposite_apply` restate
  the two statements of `UnramifiedFixedLocusStatement` for fixed explicit data.
- `unramifiedValuationDescent_of_fixedLocus`: `UnramifiedGaloisFixedApartmentStatement →
  UnramifiedFixedLeviTransportStatement → UnramifiedFixedCentralizerCompatibilityStatement →
  UnramifiedFixedOppositeStatement → UnramifiedValuationDescentStatement`. It introduces the
  target's data and applies the core. `hfix` comes from the first bridge, `hB` from Worker
  4356's `unramifiedFixedNormalizerTransport_of_leviTransport`, and `hC`, `hD` from the other
  two bridges.

## Elaboration cost

The bridges and the final reduction use `set_option maxHeartbeats 8000000`, and the core uses
1600000. The reason is the following. A `Prop` definition such as the target stores the
nested instance proofs inside the type `↥(inertiaFixedField F)` as auxiliary constants
(`…._proof_n`). The same type elaborated inside a theorem contains the raw proofs. Matching
the two forms needs proof irrelevance at about a thousand positions. The proof therefore
works in one form inside the core and converts each statement once, in its bridge.

## Axioms

Only `propext`, `Classical.choice` and `Quot.sound`.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
Construction 9.6.1, Lemma 9.6.3,
Theorem 9.6.5 and its proof (printed pp. 365–367 / PDF pp. 396–398), and §9.6.6 for clause 3.
The route of the proof (shifts from transport and the torsor, then the published valuation
constructor) is the Library's, not KP's.
