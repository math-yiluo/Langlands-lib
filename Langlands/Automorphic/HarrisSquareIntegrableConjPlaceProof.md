# Square-integrability at the conjugate place of a conjugate self-dual cuspidal realization

Module `Langlands.Automorphic.HarrisSquareIntegrableConjPlaceProof`.

`Langlands.Global.Harris.harrisSquareIntegrableConjPlace` proves the Library
statement `Langlands.Global.Harris.HarrisSquareIntegrableConjPlaceStatement`
([HarrisSquareIntegrableConjPlaceStatement](HarrisSquareIntegrableConjPlaceStatement.md))
at the independent universes `u` (the CM field) and `uV` (the carrier spaces of
the local factors). The statement is unchanged and no premise is added: no
supercuspidality, no split-place condition and no condition `v ≠ conjPlace E v`.
Take a CM number field `E` with compact adele quotient, a cuspidal realization
`S` of `GL_{r+1}` over `E` whose class is conjugate self-dual, a spectral
presentation `P` of `S` with irreducible admissible local components at every
finite place, and a finite place `v` at which the component of `P` is
square-integrable. The theorem shows that the component of the same
presentation `P` at `conjPlace E v` is square-integrable.

Of the all-place hypothesis the proof uses only the irreducibility of the
component at `conjPlace E v`. The admissibility of the component at `v`, which
the duality argument needs, follows from its square-integrability.

Notation: `c` denotes the CM involution `CMConjugation.fieldConj E`, the
abbreviation `(IsCMField.complexConj E).toRingEquiv`. For a finite place `w`,
`finitePlaceEquiv (fieldConj E) w` is by definition `conjPlace E w`, written
`c(w)`. The map
`α = AdelicGLTransport.localEquiv (r + 1) (fieldConj E) w : GL_{r+1}(E_{c(w)}) ≃ GL_{r+1}(E_w)`
applies the completion isomorphism
`finiteCompletionEquiv (fieldConj E) w : E_{c(w)} ≃ E_w` entrywise. `T_w`
denotes the canonical topological data `(CompletionPadic.padicField w).canonicalTopologicalData`
of the completion `E_w` as a finite extension of `ℚ_p`; the predicate
`LocalRealization.IsSquareIntegrable` is irreducibility together with
`T_w.IsSquareIntegrable` of the local action, square-integrability modulo the
center for every Haar measure on `GL_{r+1}(E_w)/Z`.

The proof reuses two results of
`Langlands.Global.Arithmetic.HarrisConjugateSelfDualSupercuspidalConjPlaceProof`:
`conjPlace_conjPlace` (`c(c(v)) = v`) and
`exists_conjPlace_localInvariantPairing`, whose proof uses
`finiteConj_localInclusion_conjPlace` of the same module.

## Implemented proof

1. **Transport along an isomorphism of topological fields**
   (`Langlands.PadicField.TopologicalData.isSquareIntegrable_comp_fieldEquiv`
   and `isSquareIntegrable_comp_fieldEquiv_iff`). Let `F` and `F'` be p-adic
   fields (possibly over different primes) with topological data `T` and `T'`,
   and `σ : F' ≃+* F` a ring isomorphism continuous in both directions for
   these topologies. Then for a representation `ρ` of `GL_n(F)`,
   `T'.IsSquareIntegrable (ρ ∘ GeneralLinear.fieldEquiv n σ)` holds exactly
   when `T.IsSquareIntegrable ρ` does. For the forward direction, given a Haar
   measure `μ` on the central quotient of `GL_n(F')`,
   `isSquareIntegrableModCenter_comp_continuousMulEquiv` changes variables
   along the entrywise isomorphism `GeneralLinear.fieldEquiv n σ`, and applies
   the hypothesis to the pushed-forward Haar measure. The reverse direction
   applies the forward one to `σ.symm` and uses that the two entrywise maps
   are mutually inverse.

2. **The local argument** (`isSquareIntegrable_of_conjPlace_pairing`). Let `W`
   be an irreducible local realization at `w`, `W'` a square-integrable local
   realization at `c(w)`, and `b` a nonzero bilinear form on `W × W'` with
   `b (W(α g) y) (W'(g) x) = b y x` for all `g ∈ GL_{r+1}(E_{c(w)})`. Put
   `σ = W.representation ∘ α`, a representation of `GL_{r+1}(E_{c(w)})` on the
   space of `W`.
   - `σ` is irreducible (`isIrreducible_comp_continuousMulEquiv_iff`) and
     smooth (`isSmooth_comp`). `invariantPairing_left_nondegenerate` and
     `invariantPairing_right_nondegenerate` show that `b` has zero left and
     right kernels, by the irreducibility of `σ` and of `W'`.
   - `FiniteAdelicGL.localGL_topology_eq` identifies the completion topology
     of `GL_{r+1}(E_{c(w)})` with its canonical p-adic topology, so `σ` is
     smooth for the latter. `W'.representation` is admissible for it because
     it is square-integrable (`PadicField.TopologicalData.IsSquareIntegrable.isAdmissible`).
   - `smoothInvariantPairingDuality`, with the cofinality of compact open
     subgroups (`GeneralLinear.compactOpen_cofinal`), gives an equivalence
     `Φ` of `σ` with the smooth contragredient of `W'.representation`.
   - `PadicField.TopologicalData.isSquareIntegrable_smoothContragredient`
     makes the smooth contragredient of `W'.representation` square-integrable
     for `T_{c(w)}`, and `PadicField.TopologicalData.isSquareIntegrable_iff_of_equiv`
     along `Φ` gives `T_{c(w)}.IsSquareIntegrable σ`.
   - `CompletionPadic.completion_topology_eq`, with
     `AdelicFunctoriality.continuous_finiteCompletionEquiv` and
     `continuous_finiteCompletionEquiv_symm`, shows that the completion
     isomorphism `E_{c(w)} ≃ E_w` is continuous in both directions for the
     canonical topologies. Since `α` and
     `GeneralLinear.fieldEquiv (r + 1) (finiteCompletionEquiv (fieldConj E) w)`
     have the same underlying map, step 1 turns
     `T_{c(w)}.IsSquareIntegrable σ` into `T_w.IsSquareIntegrable` of
     `W.representation`. Together with the irreducibility of `W`, this is
     `W.IsSquareIntegrable`.

3. **The global pairing** (`isSquareIntegrable_localComponent_of_conjPlace`).
   Let `P` be a spectral presentation of a cuspidal realization `S` whose
   class is conjugate self-dual. If the component of `P` at `w` is irreducible
   and the component of `P` at `c(w)` is square-integrable, the component at
   `w` is square-integrable.
   `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff` gives a
   conjugate contragredient pairing `B` of `S.realization`; the proof uses only
   its invariance under the finite adelic group and the injectivity of
   `x ↦ B (·) x`. Both local components lie in the finite image of `S` (the
   field `le_image` of `CuspidalOperatorRealization.FiniteSlice` and
   `FiniteTensorPresentation.localComponent_le`) and are nonzero
   (`CuspidalSpectralPresentation.localComponent_ne_bot`).
   `exists_conjPlace_localInvariantPairing` then gives a nonzero form `b` on
   the two components with the invariance of step 2: it restricts `B`, twisted
   by an operator commuting with the local group at `w`, and uses that
   `finiteConj` carries the local matrix of `g` at `c(w)` to the local matrix
   of `α g` at `w`. Step 2 concludes.

4. **The theorem.** Apply step 3 to `P` at `w = conjPlace E v`, with the
   irreducibility of the component at `conjPlace E v` from the all-place
   hypothesis. Its remaining hypothesis concerns the component of `P` at
   `conjPlace E (conjPlace E v)`, which is the component at `v` by
   `conjPlace_conjPlace`.

## Relation to the sources

The statement page gives the provenance: Harris, *The local Langlands
conjecture for GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998),
Theorem 1.2(i)–(ii), printed p. 185, which assumes a square-integrable local
constituent at one place and `π ≅ π̌ ∘ c`; and Clozel, *Représentations
galoisiennes associées aux représentations automorphes autoduales de GL(n)*,
Publ. Math. IHÉS 73 (1991), §5.3, Théorème 5.7, printed p. 142, whose
discrete-series condition concerns the components at the places above a split
place of the real subfield. For `π ≅ π̌ ∘ c` the component at `c(v)` is the
contragredient of the component at `v`, transported along the completion
isomorphism `E_v ≅ E_{c(v)}`, and the contragredient of a square-integrable
representation is square-integrable. The Lean proof carries out this argument
with the places exchanged: it shows that the component at `w`, pulled back
along `E_{c(w)} ≅ E_w`, is the smooth dual of the component at `c(w)`, and
obtains this local duality directly from the finite invariance of the global
conjugate contragredient pairing restricted to the two components of the same
presentation.
