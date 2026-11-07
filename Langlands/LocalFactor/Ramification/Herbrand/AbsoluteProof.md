# Absolute upper ramification: endpoint, left continuity and finite images

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.AbsoluteProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.AbsoluteStatement`,
`Langlands.LocalFactor.Ramification.Herbrand.TowerProof` and
`Langlands.LocalFactor.Ramification.InertiaPresentation`.

## What the module proves

Fix a prime `p` with `[Fact p.Prime]` and `F : PadicField.{u} p`. Write `G` for
`Field.absoluteGaloisGroup F.Carrier`, `G^v` for `absoluteUpperRamificationGroup F v`
and `r_L` for `absoluteFiniteRestriction F L`. `L` and `M` range over all
`FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)`. Write `G_L^v` for
`canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v`. The module proves
four of the seven clauses of the Library module `AbsoluteStatement`, with no further
hypotheses:

- `absoluteUpperEndpoint F : Padic.AbsoluteUpperEndpoint F`, that is `G^(-1) = ⊤`.
- `absoluteUpperLeftContinuity F : Padic.AbsoluteUpperLeftContinuity F`. For real `v > -1`,
  `G^v = ⨅ (w : ℝ) (_ : -1 ≤ w ∧ w < v), G^w`.
- `absoluteUpperFiniteImage F : Padic.AbsoluteUpperFiniteImage F`. For every `L` and real
  `v ≥ -1`, `(G^v).map r_L = G_L^v`.
- `absoluteUpperClosedRightImage F : Padic.AbsoluteUpperClosedRightImage F`. For every `L`
  and real `v ≥ -1`, the image under `r_L` of the Krull closure of
  `⨆ (w : ℝ) (_ : v < w), G^w` is `⨆ (w : ℝ) (_ : v < w), G_L^w`.

The clauses `AbsoluteUpperInertia`, `AbsoluteUpperCanonicalInertia` and
`AbsoluteUpperWildInertia` are not proved here.

Supporting results:

- `exists_lt_upperRamificationGroup_eq T K hv`. Let `T : F.TopologicalData` be any
  realization of a finite p-adic field `F` with a field `K` below it, and `v > -1`. Then there
  is a `w` with `-1 < w < v` and `Padic.upperRamificationGroup T K w = Padic.upperRamificationGroup T K v`.
  No Galois hypothesis is needed.
- `absoluteFiniteRestriction_surjective F L`: `r_L` is surjective.
- `finiteGaloisRestriction_absoluteFiniteRestriction h σ`. For `h : L ≤ M`, the Library
  restriction `finiteGaloisRestriction F h` (from `InertiaPresentation`) applied to `r_M σ`
  gives `r_L σ`.
- `map_finiteGaloisRestriction_upper h hv`. For `h : L ≤ M` and `v ≥ -1`, the image of
  `G_M^v` under `finiteGaloisRestriction F h` is `G_L^v`. This is Herbrand's theorem
  (Serre, Local Fields IV.3 Proposition 14) for the actual inclusion `L ≤ M`.
- `map_topologicalClosure_absoluteFiniteRestriction F L H`. For every subgroup `H` of `G`, the
  image of its Krull closure under `r_L` is the image of `H`.

The one named definition is `upperLiftSet F L τ v M`. For `τ : Gal(L/F.Carrier)` it is the set of
`σ ∈ G` with `r_L σ = τ` and `r_M σ ∈ G_M^v`. It is an internal helper for the compactness
argument below.

## Sources

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Chapter IV, §3:
Proposition 14 (printed p. 74, proof on p. 75) and Remark 1 on printed p. 75 (PDF p. 82). The
remark defines the upper filtration of an infinite Galois group as the inverse limit of the
finite filtrations and states its left continuity. The Library statement module
`AbsoluteStatement` cites the same places. It notes that `AbsoluteUpperClosedRightImage` is a
derived assertion, not a verbatim one from the source.

The finite Herbrand theorem used is the Library proposition
`Padic.UpperRestrictionCompatibility`. It is proved for independently presented fields by
`upperRestrictionCompatibility` in `TowerProof` (accepted candidate
`47582c7f-eb49-409e-b6d9-b6dc048c6ccd`). That proof in turn rests on `QuotientProof` and the
ported Anthropic FLT Herbrand theorems, which are already in the Library. The supporting
results above are internal steps.

## Proof (as implemented)

1. **Endpoint.** This is the Library lemma `absoluteUpperRamificationGroup_neg_one`.
2. **Finite left constancy** (`exists_lt_upperRamificationGroup_eq`). By definition
   (`upperRamificationGroup_eq_lower`), `Padic.upperRamificationGroup T K v` is the integer
   lower group of index `⌈ψ(v)⌉`, where `ψ = Padic.herbrandPsi T K`. Let `n = ⌈ψ(v)⌉`. Then
   `n - 1 < ψ(v)`. Because `ψ` is continuous, `n - 1 < ψ(w)` for all `w` close to `v`. Choose
   such a `w` with `-1 < w < v`. Then `ψ(w) < ψ(v) ≤ n` since `ψ` is strictly increasing, so
   `⌈ψ(w)⌉ = n`.
3. **Left continuity.** The absolute filtration is antitone, so `G^v` lies in the
   intersection. Conversely, let `σ` lie in every `G^w` with `-1 ≤ w < v`, and let `L` be given.
   Step 2 for the canonical realization of `L` gives `w` in `(-1, v)` with `G_L^w = G_L^v`.
   Since `σ ∈ G^w`, `r_L σ ∈ G_L^w = G_L^v`. By `mem_absoluteUpperRamificationGroup_iff`, `σ ∈ G^v`.
4. **Surjectivity and compatibility of restrictions.** `r_L` is
   `AlgEquiv.restrictNormalHom` and is surjective because the algebraic closure is Galois
   over `F.Carrier` (characteristic zero). The factorization
   `finiteGaloisRestriction F h ∘ r_M = r_L` follows from `AlgEquiv.restrictNormal_commutes`,
   used twice.
5. **Herbrand for `L ≤ M`** (`map_finiteGaloisRestriction_upper`). Give `M` the
   `L`-algebra structure of the inclusion. Then `M/L` is Galois
   (`IsGalois.tower_top_of_isGalois`), and `upperRestrictionCompatibility` applies to the fields
   `absoluteFiniteExtension F M`, `absoluteFiniteExtension F L` with their canonical
   realizations.
6. **Finite image** (`absoluteUpperFiniteImage`). The Library gives `(G^v).map r_L ≤ G_L^v`.
   For the converse let `τ ∈ G_L^v` and set `t M = upperLiftSet F L τ v M`.
   - Each `t M` is closed, being the preimage of sets in discrete finite groups under the
     continuous `r_L` and `r_M`.
   - For `M ≤ N`, `t N ⊆ t M` by steps 4 and 5. So the family is directed under `⊇`, using
     `M ⊔ N`.
   - Each `t M` is nonempty. By step 5 for `L ≤ M ⊔ L`, `τ` is the image of some
     `τ' ∈ G_{M⊔L}^v`. By step 4, `τ' = r_{M⊔L} σ` for some `σ`. Then `σ ∈ t (M ⊔ L) ⊆ t M`.
   - `G` is compact (`Gal(AlgebraicClosure F.Carrier / F.Carrier)` is profinite). By
     `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`, some `σ` lies in every
     `t M`. Then `r_M σ ∈ G_M^v` for all `M`, so `σ ∈ G^v`, and `r_L σ = τ`.
7. **Closure in a discrete image** (`map_topologicalClosure_absoluteFiniteRestriction`).
   `H ≤ closure H` gives one inclusion. For the other, `comap r_L (map r_L H)` is closed,
   being the preimage of a subset of a discrete group, and it contains `H`. So it contains the
   closure of `H` (`Subgroup.topologicalClosure_minimal`).
8. **Closed right image** (`absoluteUpperClosedRightImage`). By step 7 the closure can be
   dropped. `Subgroup.map_iSup`, applied to both nested suprema, moves the image inside. For
   `w > v ≥ -1` step 6 gives `(G^w).map r_L = G_L^w`.
