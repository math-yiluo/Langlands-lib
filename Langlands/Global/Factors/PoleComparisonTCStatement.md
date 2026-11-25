# Totally complex forms of the relative pole comparisons, isometry factors and composite map

**Scope.** The module `Langlands.Global.Factors.PoleComparisonTCStatement` defines
three propositions in the namespace `Langlands.Global.PoleComparison` and proves
nothing. Each is a published proposition with one more instance argument,
`[NumberField.IsTotallyComplex F]`, inserted directly after `[NumberField F]` for the
base field `F`. The universe parameters are the same, and the rest of the body is
copied verbatim.

| New proposition | Universes | Published original | Original module |
|---|---|---|---|
| `RelativeCertifiedPoleComparisonsTCStatement` | `uF uW uP` | `RelativeCertifiedPoleComparisonsStatement` | `Langlands.Global.Factors.RelativeCertifiedPoleComparisonsStatement` |
| `RelativeIsometryFactorTCStatement` | `uF uW uP uE` | `RelativeIsometryFactorStatement` | `Langlands.Global.Factors.RelativeIsometryFactorStatement` |
| `HenniartCompositeMapTCStatement` | `uF uK uW uP uE` | `HenniartCompositeMapStatement` | `Langlands.Global.Factors.HenniartCompositeMapStatement` |

The principal declaration of the module is
`Langlands.Global.PoleComparison.HenniartCompositeMapTCStatement`.

## 1. The statements

All vocabulary is that of the originals, and nothing is redefined:
`RelativeCertifiedPoleComparisons`, the generated spans `weilImage` and
`automorphicImage`, `RelativeGeneratedPositiveIsometry`, `RelativeIsometryFactors`,
`henniartCompositeMap` and `LatticeMap.HenniartProperties`. Their meaning is
explained in `RelativeCertifiedPoleComparisonsStatement.md` §§1–2,
`RelativeIsometryFactorStatement.md` ("Setting", "The predicates") and
`HenniartCompositeMapStatement.md` ("Setting", "The targets"). For number fields `F`,
`E : Type uF` with `E/F` Galois and `F` **totally complex**, the instance
`[CompactSpace (AdeleQuotient F)]`, a fundamental class family `c` with
`RelativeWeilGroup.IsArithmeticClassFamily c`, a finite place `v` of `F` and a
nontrivial additive character `ψ` of `F_v`:

- `RelativeCertifiedPoleComparisonsTCStatement`: the certified local pole comparisons
  `RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ` hold (Henniart 2000,
  Corollaire 2.4 and Lemme 2.8, in the witnessed relative setting).
- `RelativeIsometryFactorTCStatement`: if the pole comparisons hold, then every
  `ℤ`-linear equivalence `T : weilImage F E c v ≃ automorphicImage F E c v` with
  `RelativeGeneratedPositiveIsometry F E c v T` satisfies
  `RelativeIsometryFactors F E c v T` (the relative analogue of the determinant clause
  of Henniart's Proposition 2.6 (a) and the factor clauses of 2.6 (b)).
- `HenniartCompositeMapTCStatement`: if the pole comparisons hold and `T` is as above,
  then for every prime `p` with `residuePrime v = p`, every p-adic field
  `K : PadicField.{uK} p` and every isomorphism `f : K ≅ F_v` over `ℚ_p`, the composite
  map `henniartCompositeMap F E c v h K f T` has every property of Henniart's 3.8
  (`LatticeMap.HenniartProperties K`).

## 2. Effect of the restriction

The three statements have no archimedean clause: the restriction changes only the
class of base fields over which they are asserted. The extension `E`, a finite
extension of `F`, is then totally complex too (Mathlib
`NumberField.isTotallyComplex_of_algebra`). The proof obligations recorded for the
pole comparisons apply Henniart's Théorème 2.4 and Corollaire 2.4 at the same pair
`(F, E)` (`RelativeCertifiedPoleComparisonsStatement.md` §5), and the composite-map
statement is assembled from the isometry statements at the same `(F, E)`
(`HenniartCompositeMapStatement.md`, "The targets"). So the totally complex forms
need these inputs only over totally complex base fields, for instance in the form
`AssociatedSupercuspidalInductionTCStatement` and `AssociatedCuspidalFactorTCStatement`
(`Langlands.Automorphic.AssociatedFactorTCStatement`).

## 3. Relation to the originals

Each original implies its totally complex form at the same universe levels: apply the
original to the same `F` and `E` and forget the new instance. A development
check compiled the three implications, each as
`fun h F E _ _ _ _ _ _ _ _ => h F E`. The converse is not claimed. The statements make
no claim about base fields with a real place.

## 4. Why the totally complex forms are stated

In the Library's route to the local correspondence (route note
`notes/henniart/llc-proof-route.md`), the candidate-existence reduction applies the
pole comparisons and the composite-map statement only at the CM base field produced
by the globalization of Henniart (2000) §3 and Harris (1998) §4, and at its Galois
extension. These fields are totally complex (Mathlib
`NumberField.IsCMField.isTotallyComplex`). The totally complex form of that reduction
is `Langlands.Henniart.CandidateExistenceTCReductionStatement`, whose fourth and fifth
hypotheses are the first and third propositions of this module. The unrestricted
statements remain in the Library as infrastructure.

## 5. Sources and provenance

Provenance: *derived*. The three propositions are the special cases, for totally
complex base fields, of the published statements, which are themselves derived
finite-relative, witnessed analogues of Henniart's results. The differences from the
source are listed in the originals' Markdown ("Source correspondence" and
"Differences from the source", "Conventions and adaptations", "Relation to
Henniart's absolute-global objects").

G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique*, Invent. Math. 139 (2000), 439–455 (`henniart-2000-simple-proof`; PDF page
= printed page − 438):

- Théorème 2.4 and its Corollaire, printed p.445 (PDF 7);
- §2.5 and Théorème 2.5, printed pp.445–446 (PDF 7–8);
- Proposition 2.6 (a)–(b), printed pp.446–447 (PDF 8–9);
- Lemme 2.8 and its proof, printed pp.447–448 (PDF 9–10);
- §§3.7–3.8, the composite map and its properties, printed p.451 (PDF 13).
