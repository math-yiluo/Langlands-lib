# Inertia surjectivity, presentations and conductors over local fields

The Prop-valued definitions use Mathlib's `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]` and a specified separable
closure `Ω` with `[Field Ω] [Algebra K Ω] [IsSepClosure K Ω]`. The field and
closure have independent universes. The statements apply in both
characteristics. The Weil group is `Weil.Local.SepClosed.localWeilGroup K Ω`,
using separable closedness from `IsSepClosure K Ω`. Each representation is a
`FiniteRepresentation ℂ` of that group in an independent carrier universe.
The equivalence clause allows a second, independently sized carrier.

Finite levels are actual `FiniteGaloisIntermediateField K Ω` objects.
The statements use the `Langlands.Ramification.Local.SepClosed` restriction
maps, presentations and finite topological data. A presentation at `L`
contains the inclusion of the kernel of `weilInertiaRestriction K Ω L`
in the kernel of the restricted Weil action. The Artin and Swan expressions
are the existing rational sums of fixed-space codimensions of the descended
inertia action. With `I_i` the lower groups inside the finite inertia group
`I_0`, their weights are \(|I_i|/|I_0|\). The Artin sum includes index zero
and the Swan sum starts at index one. [Inertia presentation definitions](InertiaPresentation.md)

## Statements and sources

The table gives the declarations in `Langlands.Ramification.Local` and their
counterparts in `Langlands.Ramification.Padic`.
[Published p-adic statements](InertiaPresentationStatement.md)

| General declaration | P-adic counterpart | Assertion and source |
| --- | --- | --- |
| `AbsoluteInertiaRestrictionSurjectivityStatement` | `AbsoluteInertiaRestrictionSurjectivityStatement` | The actual restriction from absolute inertia onto the inertia of every finite Galois subextension is surjective. This is the index-zero case of the inverse-limit formulation in Serre IV §3, Proposition 14 and Remark 1, with inertia identified by IV §1, Proposition 1. |
| `WeilInertiaRestrictionSurjectivityStatement` | `WeilInertiaRestrictionSurjectivityStatement` | The specified Weil inertia restriction onto inertia at every finite Galois subextension is surjective. This follows from the absolute inertia case through the Weil inertia projection, using the identification in Deligne–Henniart §0.4. |
| `FiniteInertiaRestrictionSurjectivityStatement` | `FiniteInertiaRestrictionSurjectivityStatement` | Restriction from the inertia of `M/K` onto that of `L/K` is surjective for every inclusion `L ≤ M`. See Serre I §7, Proposition 22(b), and IV §3, Proposition 14 at upper index zero. |
| `ContinuousWeilFiniteInertiaImageStatement` | `ContinuousWeilFiniteInertiaImageStatement` | Continuity of the complex Weil action implies finiteness of its image on Weil inertia. See Deligne–Henniart §0.5. |
| `ContinuousWeilFiniteInertiaPresentationStatement` | `ContinuousWeilFiniteInertiaPresentationStatement` | Continuity of the Weil action implies `Nonempty` of its finite inertia presentation type. This is derived from Deligne–Henniart §0.5 and the finite restriction neighborhoods for inertia. |
| `FiniteInertiaConductorRefinementStatement` | `FiniteInertiaConductorRefinementStatement` | For each presentation `P` and inclusion `P.extension ≤ M`, the refined presentation and `P` have equal Artin expressions and equal Swan expressions, given surjectivity of both Weil inertia restrictions. This is the inertia-presentation form of the conductor comparison from Serre VI §2, Proposition 2 with Corollary 1′ and Proposition 3 with its corollary. |
| `FiniteInertiaConductorCompositumStatement` | `FiniteInertiaConductorCompositumStatement` | For presentations `P` and `Q` of one action, each of the two specified pullbacks to the inertia of `P.extension ⊔ Q.extension` preserves the two conductors of its own presentation. The left and right pullback expressions take the surjectivity proofs at `P` and `Q` respectively. This is the refinement comparison applied to the two inclusions. |
| `FiniteInertiaConductorIndependenceStatement` | `FiniteInertiaConductorIndependenceStatement` | For any two presentations of one Weil action, their Artin expressions agree and their Swan expressions agree, given surjectivity at each presentation. This is derived by comparing their descents on the compositum. |
| `FiniteInertiaConductorEquivalenceStatement` | `FiniteInertiaConductorEquivalenceStatement` | An invertible linear intertwiner of two Weil actions preserves both conductors across arbitrary presentations of the respective actions, given surjectivity at those presentations. This uses the same common-field comparison and invariance of fixed-space dimensions under the intertwiner. |
| `InertiaSurjectivityPresentationAndConductorIndependenceStatement` | `InertiaSurjectivityPresentationAndConductorIndependenceStatement` | The conjunction of the nine assertions, quantified over `K`, `Ω`, their field and closure instances and all the specified representation objects. The two carrier universes are independent. This aggregate groups the assertions above for later proofs. |

In the presentation-existence clause, continuity and finite inertia image
give an open action kernel in Weil inertia. Finite Galois restriction kernels
form a neighborhood basis there via the identification with absolute inertia.
Choosing a restriction kernel contained in the action kernel gives exactly
the condition of a presentation. This describes how the finite-image
assertion translates to the Library's presentation type.

For conductor refinement the descended action on the larger inertia group is
the pullback of the action on the smaller one. Serre's upper quotient
compatibility identifies the images of the upper groups, and the
fixed-space formula gives the conductor comparison under inflation. For an
inertia action, the lower groups of the corresponding totally ramified
extension are the same groups inside inertia, as in Serre IV §1,
Proposition 2. Swan invariance also follows from Artin invariance and
preservation of the index-zero codimension. For independence, both descents
pull back to the action on the compositum, where surjectivity of the Weil
inertia restriction determines the descended action. These are the
derivations behind the presentation-specific statements.

- Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
  Greenberg, Springer GTM 67 (1979), registered as `serre-1979-local-fields`.
  I §7, Proposition 22(b), pp. 22–23 (PDF pp. 30–31) gives the exact inertia
  sequence. IV §1, Propositions 1–2, p. 62 (PDF p. 69) identify the zeroth
  group and the subgroup lower filtration. IV §3, Proposition 14 and
  Remark 1, pp. 74–75 (PDF pp. 81–82) give the finite quotient image and
  the infinite inverse limit. VI §2, Proposition 2 and Corollary 1′,
  pp. 100–101 (PDF pp. 107–108) give the Artin fixed-space formula.
  Proposition 3 and its corollary, p. 101 (PDF p. 108), give invariance
  under quotient inflation.
- Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des
  constantes locales d'équations fonctionnelles de fonctions L*,
  Inventiones Mathematicae 64 (1981), 89–118, registered as
  `deligne-henniart-1981-variation`. §§0.4–0.5, pp. 91–92 (PDF pp. 3–4)
  identify Weil inertia with absolute inertia, state finite inertia image
  for continuous complex representations and relate Artin and Swan
  conductors by the inertia-fixed codimension.

## P-adic specialization

For `F : PadicField p`, take `K = F.Carrier` and
`Ω = AlgebraicClosure F.Carrier`. The canonical local field instances on
`F.Carrier` are those of `F.canonicalTopologicalData`. Characteristic zero
supplies the separable closure instance at the algebraic closure. The
following comparison unfolds the Weil group, its topology and its inertia
subgroup, all used in the finite-image statement.

```lean
import Langlands.LocalFactor.Ramification.LocalInertiaPresentationStatement
import Langlands.LocalFactor.Ramification.InertiaPresentationStatement

noncomputable section

namespace Langlands.Ramification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier

variable (A : FiniteRepresentation.{0, uF, uV} ℂ (Weil.Local.localWeilGroup F))

example :
    Local.ContinuousWeilFiniteInertiaImageStatement
        F.Carrier (AlgebraicClosure F.Carrier) A ↔
      Padic.ContinuousWeilFiniteInertiaImageStatement F A :=
  Iff.rfl

end Langlands.Ramification
```

The three restriction statements use inertia at finite levels. On an actual
finite subfield `L`, the general `SepClosed.finiteTopologicalData` builds
the integers using the spectral norm over `F.Carrier`. The p-adic
`(Padic.absoluteFiniteExtension F L).canonicalTopologicalData` uses the
spectral norm over `Padic p`. The integer subrings of `L` agree because both
are the integral closure of the integers of `F.Carrier` in `L`. Identifying
them gives the same residue kernels inside `Gal(L/F.Carrier)` and the same
actual automorphism restrictions. The three statement comparisons
therefore use the integral-closure identification.
[Finite-level data comparison](Herbrand/LocalAbsoluteStatement.md)

The presentation-existence clause uses the kernel of the resulting Weil
inertia restriction. After identifying its finite target as above, the
presentation condition uses the same kernel and the same Weil inertia
action. The four conductor clauses then use the same refinements, pull
back along the same inclusions, and evaluate the same lower-group
fixed-space sums. Their statement comparisons also depend on the finite
integer rings. The aggregate generalizes the outer quantification over
p-adic fields to quantification over all local fields and specified
separable closures, and each specialized conjunct corresponds to the
clause in the table by the indicated comparison.
