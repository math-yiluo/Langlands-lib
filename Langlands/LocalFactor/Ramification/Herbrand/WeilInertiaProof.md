# Inertia restrictions, finite presentations and Weil break thresholds

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.InertiaProof`,
`Langlands.LocalFactor.Ramification.InertiaPresentationStatement`,
`Langlands.LocalFactor.Ramification.WeilBreakStatement` and `Langlands.Weil.Local.ContinuityProof`.

## What the module proves

Fix a prime `p` and `F : PadicField.{u} p`. Write `G^v` for
`absoluteUpperRamificationGroup F v`, and `r_L` for `absoluteFiniteRestriction F L` for a
finite Galois subfield `L` of `AlgebraicClosure F.Carrier`. Write `I` for the local Weil
inertia `localInertia F`. `A` is a finite-dimensional complex representation of
`localWeilGroup F`. `upperGroup`, `IsTrivialAt`, `trivialityThresholds`, `lastBreak` and
`upperFixedSpace` are the Library notions of `LocalWeil.Ramification`.

### Clauses of `InertiaPresentationStatement`

- `absoluteInertiaRestriction_surjective F : AbsoluteInertiaRestrictionSurjectivityStatement F`.
  Absolute inertia maps onto the inertia group of every finite Galois `L`.
- `weilInertiaRestriction_surjective F : WeilInertiaRestrictionSurjectivityStatement F`. So does
  Weil inertia.
- `finiteInertiaRestriction_surjective F : FiniteInertiaRestrictionSurjectivityStatement F`. So
  does inertia along every inclusion `L ≤ M`.
- `continuousWeilFiniteInertiaPresentation F A : ContinuousWeilFiniteInertiaPresentationStatement F A`.
  A continuous `A` has a `FiniteInertiaPresentation`: for some finite Galois `L`, the kernel of
  `weilInertiaRestriction F L` lies in the kernel of `A` on `I`.
- `continuousWeilFiniteInertiaImage F A : ContinuousWeilFiniteInertiaImageStatement F A`. A
  continuous `A` has finite image on `I`.
- `chosenInertiaPresentation F A hA` is the one named definition: a presentation chosen from
  the previous theorem.

### Clauses of `WeilBreakStatement`

- `weilTrivialityThresholdsNonempty F : WeilTrivialityThresholdsNonempty F`. For continuous
  `A`, some `r ≥ 0` has `G^r`, through `upperGroup F r`, acting trivially.
- `weilLastBreakZero F : WeilLastBreakZero F`. For continuous `A`, `lastBreak F A = 0` if and
  only if `A` is trivial at every `r > 0`.
- `weilIrreduciblePositiveThresholds F : WeilIrreduciblePositiveThresholds F`. Let `A` be
  continuous and irreducible.
  - For `a > 0`: `a ≤ lastBreak F A` if and only if `upperFixedSpace F A a = ⊥`.
  - For `b > 0`: `lastBreak F A < b` if and only if `upperFixedSpace F A b = ⊤`.

### Supporting results

These hold for continuous `A`.

- `exists_lt_isTrivialAt`: if `A` is trivial at `b > 0`, it is trivial at some `b'` with
  `0 < b' < b`.
- `lastBreak_lt_iff_isTrivialAt`: for `b > 0`, `lastBreak F A < b` if and only if
  `IsTrivialAt F A b`.
- `upperFixedSpace_eq_top_iff`: the fixed space is `⊤` exactly when the action is trivial.
- `upperFixedSpace_eq_bot_or_eq_top`: for irreducible `A`, the fixed space of `upperGroup F r`
  is a subrepresentation, hence `⊥` or `⊤`.

## Sources

- Deligne–Henniart (1981), §0.4–0.6 (registered as `deligne-henniart-1981-variation`, printed
  p. 92, PDF p. 4).
  - The upper filtration of an infinite Galois group is the inverse limit. The Weil groups
    `W(t) = G(t)` for `t ≥ 0`, with inertia `I = W(0)`.
  - In a representation of `W`, inertia acts through a finite group.
  - `α(V)` is the last jump: `V^{W(α)} = 0` and `V^{W(α+ε)} = V` for every `ε > 0`.

  The Library `lastBreak`, the infimum of the nonnegative trivial indices, is this last jump.
  The theorems here show that the infimum is over a nonempty set and that `G^b` acts trivially
  for every `b` strictly above it.
- Jean-Pierre Serre, *Local Fields*, GTM 67 (registered as `serre-1979-local-fields`,
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`), Chapter IV, §3,
  Proposition 14 and Remark 1 (printed pp. 74–75, PDF pp. 81–82): the absolute filtration and
  its left continuity.

The Library statement modules `InertiaPresentationStatement` and `WeilBreakStatement` record
these assertions; the remaining clauses of `WeilBreakStatement` are not proved here. The
presentation and left-openness lemmas are internal steps.

## Proof (as implemented)

1. **Surjectivity.** `upperRamificationGroup_zero` identifies the inertia of `L` with
   `canonicalUpperRamificationGroup _ F.Carrier 0`. `absoluteUpperFiniteImage F L 0`
   (`AbsoluteProof`) writes it as `(G^0).map r_L`. `absoluteUpperCanonicalInertia F`
   (`InertiaProof`) identifies `G^0` with absolute inertia. The Weil version precomposes the
   Library homeomorphism `localInertiaEquiv F`. The finite version uses
   `finiteInertiaRestriction_absolute`.
2. **Presentation.** By the Library theorem `localWeilContinuity`, continuity of `A` makes the
   kernel `N` of `A` on `I` open.
   - Transport `N` along `localInertiaEquiv` to an open neighbourhood of `1` in absolute
     inertia. In the subspace topology (`nhds_subtype`) it contains `V ∩ inertia` for a Krull
     neighbourhood `V` of `1`.
   - `krullTopology_mem_nhds_one_iff_of_normal` gives a finite normal `E` with fixing subgroup
     inside `V`. `E` is Galois because the closure is separable (characteristic zero); take
     `L = E`.
   - If `weilInertiaRestriction F L w = 1`, then `r_L (localProjection w) = 1`, so the projection
     fixes `E` (`FiniteGaloisIntermediateField.mem_fixingSubgroup_iff`), and `w ∈ N`.

   Finite inertia image is the fifth clause of `localWeilContinuity`.
3. **Nonempty thresholds.** Choose a presentation on `L` and `b` with all upper groups of `L` of
   index at least `b` trivial (`exists_upperRamificationGroup_eq_bot`). Put `r = max b 0`. For
   `w ∈ upperGroup F r`:
   - the projection lies in `G^0`, absolute inertia, so `w ∈ I` (`localInertia_eq_comap`);
   - its restriction to `L` lies in the trivial group of `L` of index `r`;
   - so `w` is in the kernel of `weilInertiaRestriction`, hence acts trivially
     (`kernel_le`).
4. **Left openness** (`exists_lt_isTrivialAt`). On the presenting field, the finite upper
   group is constant slightly to the left of `b` (`exists_lt_upperRamificationGroup_eq`). Take
   `b' = max c (b/2)` in `(0, b)` with `G_L^{b'} = G_L^b`. For `w ∈ upperGroup F b'`:
   - the restriction of its projection lies in `G_L^b`, which is `(G^b).map r_L`
     (`absoluteUpperFiniteImage`), say the image of `σ ∈ G^b`;
   - `σ` is inertial; let `w'` be its preimage under `localInertiaEquiv`. Then `A w' = 1` by
     triviality at `b`;
   - `w'⁻¹ w` lies in the kernel of `weilInertiaRestriction`, so it acts trivially. Hence
     `A w = A w' · A(w'⁻¹ w) = 1`.
5. **Last break.** If `lastBreak < b`, some threshold `s < b` exists (`exists_lt_of_csInf_lt`,
   using step 3), and triviality is monotone. Conversely, triviality at `b > 0` gives a
   threshold `b' < b` by step 4, so `lastBreak ≤ b' < b`. For `WeilLastBreakZero`: if the label
   is `0`, every `r > 0` exceeds it. If `A` is trivial at every `r > 0`, then
   `lastBreak < ε` for every `ε > 0`, so the label is `0`.
6. **Irreducible thresholds.** `upperGroup F r` is normal, as a preimage of the normal
   `absoluteUpperRamificationGroup`. So its fixed space is stable under `A`, and
   `IsSimpleOrder` of subrepresentations (irreducibility) makes it `⊥` or `⊤`.
   - If `a ≤ lastBreak` and the fixed space were `⊤`, step 5 would give `lastBreak < a`.
   - If the fixed space is `⊥` but `lastBreak < a`, it would also be `⊤`. This forces
     `⊥ = ⊤` among subrepresentations, contradicting irreducibility.
   - The `b` clause is step 5 with `upperFixedSpace_eq_top_iff`.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
