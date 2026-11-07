# Actual quasi-split apartments with root coordinates for every centralizer datum

Author: Worker 1045.

`QuasiSplitCoordinateApartmentStatement` is an unproved existence proposition.
It isolates what remains of `QuasiSplitIntegerApartmentExistenceStatement` once
an actual centralizer datum is available. It has the same hypotheses as that
target: a field `k : Type u`, a valuation
`v : Valuation k (WithZero (Multiplicative ℤ))` that is surjective and whose
valuation subring is a henselian local ring (the proof of this is named `hH`), an
actual affine quasi-split group `G` (`IsAffineHom G.X.hom` and
`IsQuasiSplit G`), and a prescribed maximal split torus `i : S → G`
(`IsMaximalSplitTorus i`). The `Mono` instance on `i` comes from
`mono_of_isMaximalSplitTorus`, exactly as in the target.

For **every** `C : CentralizerDatum i`, the proposition asserts that there are
a `D : KPApartmentData i (IntegerValuation.order v)` and a root function
family `φ` with `φ ∈ D.carrier`, such that every relative root
`a ∈ relativeRoots i` satisfies one of three alternatives. They are formed with
`C.j` and `C.s` and are exactly the hypothesis of the Library theorem
`IntegerValuation.isOmegaCompatible_of_rootCoordinateTypes`:

1. `Nonempty (IntegerValuation.RootCoordinateFamilyEquivariance v i C.j C.s φ a)`.
   This is a finite extension `E` with a norm-calibrated valuation `w`, a
   nonempty finite family of coordinates `c_l : G(k) → E`, and a positive
   integer `m`. On `U_a(k)`, `m • φ_a = min_l w ∘ c_l`. There are characters
   `β_l` of `Z_E` restricting to `m • a`, and the whole centralizer acts on the
   coordinates through them.
2. A `RootUnitaryCoordinates i C.j C.s a` (quadratic unitary coordinates
   `e : SU3Root.rationalParameters E L ≃* U_a(k)`) with
   `φ_a (e p) = SU3Root.towerDepth k E L v hH p` for all parameters `p`.
3. A root `b` with `2 • b = a` and a `RootUnitaryCoordinates i C.j C.s b`
   whose zero-first-coordinate parameters `q` satisfy
   `φ_a (e q) = SU3Root.towerCentralDepth k E L v hH q`.

The statement quantifies over every centralizer datum and does not let the
datum be chosen. This separates root coordinates from the structural
construction of a centralizer datum. Any datum produced elsewhere, such as
`CentralizerDatum.ofStructure`, can be used. The apartment class `D`, the
family `φ` and the coordinates are all outputs; no valuation of the root datum
or coordinates are premises.

## Provenance

This is an internal interface. Its shape comes from published Library
definitions and from the hypothesis of
`isOmegaCompatible_of_rootCoordinateTypes`. Its intended mathematical content
is the quasi-split apartment of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023) (source `kaletha-prasad-2023-bruhat-tits-new-approach`):

- Construction 6.1.17 (printed pp.205–206, PDF236–237) defines the Chevalley
  valuation. For a type R1 root, `φ_a` is the valuation of `k_ã` composed with
  the inverse of the coordinate isomorphism (2.9.2). For a type R2 root,
  `φ_a(u, v) = ω(v)/2` and `φ_{2a}(0, v) = ω(v)` on the quadratic unitary
  coordinates (2.9.3).
- Proposition 6.1.19 (printed pp.206–207, PDF237–238) states that this is an
  `ω`-compatible valuation of the relative root datum.
- Lemma 6.1.28 (printed p.210, PDF241) shows that `N_ad(k)` preserves the
  affine space `A(S)` of these valuations. `N(k)` acts through `N_ad(k)`, so
  the equipollence class is normalizer-stable.

The three alternatives give these root functions in the form used by the
published V6 bridges. For type R1, alternative 1 allows several Galois-conjugate
coordinates, so the action of the whole centralizer can be recorded through
characters of `Z_E`. For type R2 and its double, the tower depths are the
Library's henselian extensions of the valuation to the quadratic tower. The
statement claims no more than this existence. Kaletha–Prasad work under their
standing hypotheses on `k`. This proposition is stated at the generality of the
target (every henselian field with a surjective `ℤ`-valued valuation). No
source theorem at exactly that generality is cited here.

## Scope

This proposition is not proved. It is a sufficient hypothesis for the target,
together with `CentralSplitTorusCharacterStatement`; see
`QuasiSplitCoordinateApartmentReduction`. It does not construct
Chevalley–Steinberg systems, root coordinates or root functions, and it does
not verify V0–V5.
