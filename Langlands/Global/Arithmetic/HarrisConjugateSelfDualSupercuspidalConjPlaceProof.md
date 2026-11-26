# Supercuspidality at the conjugate place of a conjugate self-dual cuspidal class

Module `Langlands.Global.Arithmetic.HarrisConjugateSelfDualSupercuspidalConjPlaceProof`,
namespace `Langlands.Global.Harris`.

`Langlands.Global.Harris.conjugateSelfDualSupercuspidalConjPlace` proves the
Library statement
`Langlands.Global.Harris.ConjugateSelfDualSupercuspidalConjPlaceStatement`
(Statement 2 of
[HarrisAuxiliaryConjugatePairStatement](HarrisAuxiliaryConjugatePairStatement.md#2-conjugateselfdualsupercuspidalconjplacestatement))
at the independent universes `u` (the CM field) and `uV` (the carrier spaces of
the local factors). The statement is not changed and has no extra premise: no
condition on the residue characteristic, the level or ramification, and no
local-global comparison hypothesis. Take a CM number field `E` with compact
adele quotient, a conjugate self-dual cuspidal class `c` of `GL_{r+1}` over `E`
and a finite place `v`. If some actual spectral presentation, with local
factors in `Type uV`, of a representative of `c` has a supercuspidal local
component at `v`, the theorem gives an actual spectral presentation, again with
local factors in `Type uV`, of a representative of `c` whose local component at
`conjPlace E v` is supercuspidal. This is the witness required by
`CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent`.

From the conjugate contragredient pairing the proof uses only its invariance
under the finite adelic group and the injectivity of `x ↦ B (·) x`. It does not
use the invariance under the standard compact subgroup or the real Lie algebra,
nor the surjectivity onto contragredient functionals. It constructs no
conjugate or contragredient global realization.

Notation: `c` also denotes the CM involution `CMConjugation.fieldConj E`, which
is the abbreviation `(IsCMField.complexConj E).toRingEquiv`. For a finite place
`w`, the place `finitePlaceEquiv (fieldConj E) w` is by definition
`conjPlace E w`; the Lean statements of the auxiliary lemmas use the first
form. `α = AdelicGLTransport.localEquiv (r + 1) (fieldConj E) w` is the
entrywise isomorphism `GL_{r+1}(E_{c(w)}) ≅ GL_{r+1}(E_w)` induced by the
completion isomorphism `finiteCompletionEquiv (fieldConj E) w`.

## Implemented proof

1. **The conjugate place is an involution** (`conjPlace_conjPlace`):
   `conjPlace E (conjPlace E v) = v`. The composite `c ∘ c` is the identity
   ring automorphism (`IsCMField.complexConj_apply_apply`), and
   `AdelicFunctoriality.finitePlaceEquiv_trans` and
   `AdelicFunctoriality.finitePlaceEquiv_refl` turn this into the identity on
   places.

2. **Conjugation of local matrices** (`finiteConj_localInclusion_conjPlace`).
   For `g ∈ GL_n(E_{c(w)})`,
   `finiteConj E n (localInclusion E n (c(w)) g) = localInclusion E n w (α g)`.
   The proof rewrites `finiteConj` as the arithmetic transport
   `AdelicGLTransport.finiteEquiv n (fieldConj E)`
   (`AdelicGLTransport.finiteEquiv_complexConj`) and applies
   `AdelicGLTransport.finiteEquiv_localInclusion`.

3. **A nonzero local pairing** (`exists_conjPlace_localInvariantPairing`). Let
   `S` be an irreducible cuspidal realization and `B` a pairing on its space
   with `B (π(finiteConj d) y) (π(d) x) = B y x` for all finite adelic `d`, and
   with `x ↦ B (·) x` injective. Let `W` be a nonzero local subspace at `w` and
   `W'` a nonzero local subspace at `c(w)`, both contained in the finite image
   of `S`. Then there is a bilinear form `b` on `W × W'` with `b ≠ 0` and
   `b (W(α g) y) (W'(g) x) = b y x` for all `g ∈ GL_{r+1}(E_{c(w)})`.
   The construction follows `exists_localInvariantPairing` of
   `Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof`, with
   the conjugate twist in the first variable:
   - choose `x' ≠ 0` in `W'`
     (`LocalRealization.exists_ne_zero_of_ne_bot`). By injectivity the
     functional `B (·) x'`, with `x'` lifted to `S`
     (`OperatorRealization.localLift`), is nonzero;
   - `OperatorRealization.exists_twist_ne_zero`, which uses the full-operator
     irreducibility of `S`, gives an operator `a` of the local centralizer at
     `w` and `x ∈ W` with `B (π(a) x) x' ≠ 0`;
   - put `b y x = B (π(a) y) x`, with `y` and `x` lifted to `S`. The lift
     intertwines the local actions with the local inclusions
     (`OperatorRealization.localLift_representation`), `π(a)` commutes with the
     local group at `w` (`OperatorRealization.representation_commute`), and by
     step 2 the local inclusion of `α g` at `w` is `finiteConj` of the local
     inclusion of `g` at `c(w)`. Finite invariance of `B` then gives the
     invariance of `b`, and `b x x' ≠ 0`.

4. **The local argument** (`isSupercuspidal_of_conjPlace_pairing`). Let `W` be
   an irreducible local realization at `w`, `W'` a supercuspidal local
   realization at `c(w)` and `b` a nonzero pairing as in step 3. Put
   `σ = W.representation.comp α`, a representation of `GL_{r+1}(E_{c(w)})` on
   the space of `W`.
   - `σ` is irreducible (`isIrreducible_comp_continuousMulEquiv_iff`) and
     smooth (`isSmooth_comp`, since `α` is continuous).
     `invariantPairing_left_nondegenerate` and
     `invariantPairing_right_nondegenerate` show that `b` has zero left and
     right kernels, using the irreducibility of `σ` and of `W'`.
   - The canonical `p`-adic topology on `GL_{r+1}(E_{c(w)})` equals the
     completion topology (`FiniteAdelicGL.localGL_topology_eq`), so `σ` is
     smooth and `W'` admissible for it. `smoothInvariantPairingDuality`, with
     the cofinality of compact open subgroups
     (`GeneralLinear.compactOpen_cofinal`), gives an equivalence of `σ` with the
     smooth contragredient of `W'.representation`.
   - `LocalRealization.isSupercuspidal_iff_representation` turns the
     supercuspidality of `W'` into `GeneralLinear.IsSupercuspidal` of
     `W'.representation`. `CompletionPadic.completion_topology_eq` moves it to
     the canonical topology of the field.
     `GeneralLinear.isSupercuspidal_smoothContragredient` makes the smooth
     contragredient supercuspidal, and `GeneralLinear.isSupercuspidal_of_equiv`
     transfers this to `σ`. `completion_topology_eq` moves it back to the
     completion topology.
   - `α` is entrywise application of the completion isomorphism, so `σ` is the
     pullback of `W.representation` along
     `GeneralLinear.fieldEquiv (r + 1) (finiteCompletionEquiv (fieldConj E) w)`,
     whose two directions are continuous
     (`AdelicFunctoriality.continuous_finiteCompletionEquiv` and
     `continuous_finiteCompletionEquiv_symm`).
     `GeneralLinear.isSupercuspidal_comp_fieldEquiv_iff` gives
     `GeneralLinear.IsSupercuspidal` of `W.representation`. With the
     irreducibility of `W`, `LocalRealization.isSupercuspidal_iff_representation`
     gives `W.IsSupercuspidal`.

5. **Global assembly** (`hasSupercuspidalComponent_of_conjPlace`). If a
   conjugate self-dual class `c` has a supercuspidal component at `c(w)`, it has
   one at `w`. Take the representative `S` and the presentation `P` whose
   component at `c(w)` is supercuspidal.
   `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff` gives the
   conjugate contragredient pairing `B` of `S.realization`.
   `cuspidalAllLocalIrreduciblePresentationExistence`, applied to `P`, gives a
   presentation of `S` with local factors in the universe of `E` and
   irreducible admissible local components at every finite place;
   `CuspidalSpectralPresentation.exists_small` realizes such a presentation `Q`
   with local factors in `Type uV`. The embedded local components lie in the
   finite image of `S` (the field `le_image` of
   `CuspidalOperatorRealization.FiniteSlice` and
   `FiniteTensorPresentation.localComponent_le`) and are nonzero
   (`CuspidalSpectralPresentation.localComponent_ne_bot`). Step 3 with
   `W = Q.localComponent w` and `W' = P.localComponent (c(w))`, then step 4,
   show that `Q.localComponent w` is supercuspidal. So `S` and `Q` witness the
   supercuspidal component at `w`, in the universe `uV`.

6. **The theorem.** Apply step 5 with `w = conjPlace E v`. Its hypothesis is a
   supercuspidal component at `conjPlace E (conjPlace E v)`, which is `v` by
   step 1.

## Relation to the sources

The statement note gives the mathematical argument and its provenance: Harris
(1998), *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134, Theorem 1.2(ii) (printed p.185) for conjugate
self-duality `π ≅ π̌ ∘ c`, and the auxiliary conjugate pair of places with
Proposition 4.8 (printed pp.200–203). There, `π ≅ π̌ ∘ c` gives
`π_{c(v)} ≅ (π_v)^∨` transported along the completion `E_v ≅ E_{c(v)}`, and
the contragredient of a supercuspidal representation is supercuspidal. The
Lean proof carries out this argument with the places exchanged. It shows that
the component at `w`, pulled back along `E_{c(w)} ≅ E_w`, is the smooth dual
of the supercuspidal component at `c(w)`. It obtains this local duality
directly from the finite invariance of the global pairing.
