# Inertia surjectivity, finite presentations and conductor independence: proof

Lean module: `Langlands.LocalFactor.Ramification.InertiaPresentationProof`
(namespace `Langlands.Ramification.Padic`). Worker 5163 wrote it for Task 5676. It imports
`Langlands.LocalFactor.Ramification.InertiaPresentationStatement` (the target),
`Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof` and
`Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof`. No Library file is changed.

## Main result

`Langlands.Ramification.Padic.inertiaSurjectivityPresentationAndConductorIndependence`
proves the Library proposition
`Langlands.Ramification.Padic.InertiaSurjectivityPresentationAndConductorIndependenceStatement.{uF, uV, uW}`.
Its type is exactly that proposition. The universe levels are independent: `uF` for the
p-adic field and `uV`, `uW` for the carriers of the two representations `A` and `B`.

The statement quantifies over every prime `p`, every `F : PadicField.{uF} p`, every
`A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)` and every
`B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)`. It is the conjunction of nine
clauses, listed in the target Markdown (`InertiaPresentationStatement.md`). The proof adds no
hypothesis. Continuity appears only as the premise that clauses 4 and 5 already contain.
Clauses 6–9 hold for every presentation and every pair of surjectivity proofs.
`lean_check` reports that the theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Notation

`P`, `Q` are finite inertia presentations (`FiniteInertiaPresentation F A`). Such a
presentation has a finite Galois subfield `P.extension` of `AlgebraicClosure F.Carrier`. It
also has a proof `P.kernel_le` that the kernel of `weilInertiaRestriction F P.extension`
lies in the kernel of `localInertiaRepresentation F A`, which is `A` restricted to the local
Weil inertia group `localInertia F`. `hP`, `hQ` are surjectivity proofs for the Weil inertia
restrictions. `P.representation hP` is the descended representation of the finite inertia
group `inertia T F.Carrier`, where `T` is the canonical topological data of
`absoluteFiniteExtension F P.extension`. `P.artinConductor hP` and `P.swanConductor hP` are
the Library's weighted sums (Serre, *Local Fields*, VI §2, Corollary 1′ to Proposition 2).
They are defined as `artinConductorOfQuotient` and `swanConductorOfQuotient`, so they are by
definition `inertiaArtinConductor T F.Carrier (P.representation hP)` and
`inertiaSwanConductor T F.Carrier (P.representation hP)`.

## Declarations and their proofs

### `finiteInertiaConductorIndependence` (clause 8)

`finiteInertiaConductorIndependence F A : FiniteInertiaConductorIndependenceStatement F A`.
The Library theorem `presentation_conductors_eq F A P Q hP hQ` (module
`InertiaConductorRefinementProof`) has the same conclusion for arbitrary `P`, `Q`, `hP`, `hQ`.
Its module states its form but not this proposition. The proof only restates it as a
proof of this proposition.

Route of the imported theorem: it writes each Swan sum as the integral, over the upper index
`v ∈ [0, B]`, of the codimension of the upper fixed space. It writes each Artin sum as that
integral plus the codimension at `v = 0`. Then
`HerbrandBridge.presentationUpperFixedComparison` (module `Herbrand.WeilBreakProof`)
identifies both upper fixed spaces at every `v ≥ 0` with the presentation-free space
`upperFixedSpace F A v`.

### `finiteInertiaConductorCompositum` (clause 7)

`finiteInertiaConductorCompositum F A : FiniteInertiaConductorCompositumStatement F A`.
Let `R = FiniteInertiaCommonRefinement.compositum F A P Q`. Its field is
`M = P.extension ⊔ Q.extension`, and its inclusions are `le_sup_left` and `le_sup_right`.

1. `HerbrandBridge.weilInertiaRestriction_surjective F M` (clause 2, module
   `Herbrand.WeilInertiaProof`) gives a surjectivity proof `hR` at `M`. The statement does
   not provide one; the proof obtains it here.
2. `R.leftRepresentation hP` is by definition `P.pullback hP M le_sup_left`. The Library
   lemma `FiniteInertiaPresentation.representation_refine` (module `InertiaPresentation`)
   gives `(P.refine M le_sup_left).representation hR = P.pullback hP M le_sup_left`. So
   `R.leftRepresentation hP = (P.refine M le_sup_left).representation hR`. The same lemma
   for `Q` gives `R.rightRepresentation hQ = (Q.refine M le_sup_right).representation hR`.
3. Apply `inertiaArtinConductor T_M F.Carrier` and `inertiaSwanConductor T_M F.Carrier`
   (`congrArg`) to these equalities. Here `T_M` is the canonical data at `M`. The right-hand
   sides are by definition `(P.refine M le_sup_left).artinConductor hR` and so on.
4. The Library theorem `finiteInertiaConductorRefinement F A` (clause 6, module
   `InertiaConductorRefinementProof`) gives
   `(P.refine M le_sup_left).artinConductor hR = P.artinConductor hP` and the Swan analogue.
   Likewise for `Q` with `le_sup_right`. Chaining with step 3 gives the four equalities.

### `localInertiaRepresentationEquiv`

An auxiliary definition introduced for this proof; it is not a literature definition.
For `e : FiniteRepresentation.Equiv A B`, it is the equivalence
`(localInertiaRepresentation F A).Equiv (localInertiaRepresentation F B)` with the same linear
equivalence `e.toLinearEquiv`. Mathlib's `Representation.Equiv.mk` builds it. The
intertwining identity at `g : localInertia F` is `e.isIntertwining' g`, the intertwining
identity of `e` at the Weil group element `g`. The carriers stay in their own universes
`uV` and `uW`.

### `finiteInertiaConductorEquivalence` (clause 9)

`finiteInertiaConductorEquivalence F A B : FiniteInertiaConductorEquivalenceStatement F A B`.
Let `e : FiniteRepresentation.Equiv A B`, let `P` present `A` and `Q` present `B`, and fix
`hP`, `hQ`. Write `π = (weilInertiaRestriction F P.extension).toMonoidHom` and
`e' = localInertiaRepresentationEquiv F e`.

1. Transport `P` to `B`. The Library lemma `kernel_le_of_equiv T F.Carrier π P.kernel_le e'`
   (module `Descent`) shows that `ker π ≤ ker (localInertiaRepresentation F B)`. So
   `P' := ⟨P.extension, _⟩` is a `FiniteInertiaPresentation F B` on the same field. Its
   surjectivity proof is `hP` itself.
2. The Library lemmas `artinConductorOfQuotient_equiv` and `swanConductorOfQuotient_equiv`
   (module `Descent`) apply to `T`, `F.Carrier`, `π`, `hP`, the two kernel conditions and
   `e'`. They give `P.artinConductor hP = P'.artinConductor hP` and
   `P.swanConductor hP = P'.swanConductor hP`. These lemmas descend `e'` to an equivalence of
   the two descended representations (`descendInertiaEquiv`). They then use invariance of
   the inertia Artin and Swan sums under representation equivalence
   (`inertiaArtinConductor_equiv` and `inertiaSwanConductor_equiv`, module `Galois`), which
   allows independent carrier universes.
3. `P'` and `Q` are two presentations of the same `B`. So
   `presentation_conductors_eq F B P' Q hP hQ` gives
   `P'.artinConductor hP = Q.artinConductor hQ` and the Swan analogue. Chaining with step 2
   gives clause 9.

### `inertiaSurjectivityPresentationAndConductorIndependence` (assembly)

After `intro p _ F`, an anonymous-constructor term supplies the nine clauses:

1. `HerbrandBridge.absoluteInertiaRestriction_surjective F`,
2. `HerbrandBridge.weilInertiaRestriction_surjective F`,
3. `HerbrandBridge.finiteInertiaRestriction_surjective F`,
4. `HerbrandBridge.continuousWeilFiniteInertiaImage F A`,
5. `HerbrandBridge.continuousWeilFiniteInertiaPresentation F A`

(all five from module `Herbrand.WeilInertiaProof`), then

6. `finiteInertiaConductorRefinement F A` (module `InertiaConductorRefinementProof`),
7. `finiteInertiaConductorCompositum F A`,
8. `finiteInertiaConductorIndependence F A`,
9. `finiteInertiaConductorEquivalence F A B`.

Clauses 4–8 are under `∀ A` and clause 9 under `∀ A B`, as in the statement.

## Imported Library results

- Module `Langlands.LocalFactor.Ramification.InertiaPresentation`:
  `FiniteInertiaPresentation`, `.representation`, `.artinConductor`, `.swanConductor`,
  `.refine`, `.pullback`, `.representation_refine`, `FiniteInertiaCommonRefinement.compositum`,
  `.leftRepresentation`, `.rightRepresentation`, `weilInertiaRestriction`,
  `localInertiaRepresentation`.
- Module `Langlands.LocalFactor.Ramification.Descent`: `kernel_le_of_equiv`,
  `artinConductorOfQuotient_equiv`, `swanConductorOfQuotient_equiv`.
- Module `Langlands.LocalFactor.Ramification.Galois`: `inertiaArtinConductor`,
  `inertiaSwanConductor`, `artinConductorOfQuotient`, `swanConductorOfQuotient` (definitions
  unfolded by the elaborator).
- Module `Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof`:
  `presentation_conductors_eq`, `finiteInertiaConductorRefinement`.
- Module `Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof` (namespace
  `Langlands.Ramification.HerbrandBridge`): `absoluteInertiaRestriction_surjective`,
  `weilInertiaRestriction_surjective`, `finiteInertiaRestriction_surjective`,
  `continuousWeilFiniteInertiaImage`, `continuousWeilFiniteInertiaPresentation`.
- Module `Langlands.Weil.Representation.Basic`: `FiniteRepresentation.Equiv`, which is
  Mathlib's `Representation.Equiv` of the two actions.
- Mathlib: `Representation.Equiv.mk`, `Representation.IntertwiningMap.isIntertwining'`,
  `le_sup_left`, `le_sup_right`.

## Literature

J.-P. Serre, *Local Fields* (1979), registered as `serre-1979-local-fields`
(`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256 `109b461d…`).

- VI §2, Corollary 1′ to Proposition 2, printed p. 101 (PDF p. 108):
  `f(χ) = Σ_i (g_i/g_0) codim V^(G_i)`. This weighted sum is the Library definition of the
  inertia Artin sum. The Swan sum omits `i = 0`.
- VI §2, Proposition 3 and its Corollary, printed p. 101 (PDF p. 108). For a normal
  subgroup `N` of `G`, with projection `q : G → G/N`, Proposition 3 states
  `a_{G/N} = (a_G)^♮`. By VI §1(b), printed p. 98 (PDF p. 105), this pushforward averages
  over the fibres of `q`: `(a_G)^♮(x) = (1/Card N) Σ_{q(t) = x} a_G(t)`. So the Artin
  character is pushed forward by averaging and is not itself invariant under inflation. The
  Corollary gives invariance of the conductor under inflation: `f_{G/N}(φ) = f_G(φ ∘ q)`
  for every class function `φ` on `G/N`. Clauses 6–8 are inertia-level analogues of this
  Corollary for the Library's presentations, stated for both the Artin and the Swan sums.
  They say that these sums do not depend on the finite quotient through which the
  representation of the Weil inertia group is computed. The Lean route differs: it compares
  upper-numbering fixed-space profiles through the absolute upper ramification groups of
  the Weil group (in the imported `presentation_conductors_eq`). It never compares the two
  finite inertia groups through Serre's quotient argument.
- Clause 9 combines clause 8 with the evident invariance of the weighted sum under an
  isomorphism of representations, which preserves every fixed-space dimension. The Library
  proves that invariance as `inertiaArtinConductor_equiv`; this module does not reprove it.
