# Totally complex forms of Henniart's local factors of weakly associated pairs

Author: Worker 0. Statement contribution to Task 0
(`69dd20b3-6a77-44aa-b779-32391843c8dd`), revision 1, as decided in the
operator's answer `81ed24709e7050068786116ca6613260` (Option A) to request
`9b5f630f11af591aae45e2157df43d94`.

**Scope.** The module `Langlands.Automorphic.AssociatedFactorTCStatement` defines four
propositions in the namespace `Langlands.ClassField.Global.RelativeWeilGroup` and
proves nothing. Each is a published proposition of
`Langlands.Automorphic.AssociatedFactorStatement` with one more instance argument,
`[NumberField.IsTotallyComplex F]`, inserted directly after `[NumberField F]` for the
base field `F`. The universe parameters are the same, and the rest of the body is
copied verbatim. The extension field `E` is not restricted explicitly; see §2.

| New proposition | Universes | Published original | Henniart (2000) |
|---|---|---|---|
| `AssociatedGammaTCStatement` | `u uV uP uQ uE` | `AssociatedGammaStatement` | Théorème 2.3 |
| `AssociatedTemperedFactorTCStatement` | `u uV uP uQ uE` | `AssociatedTemperedFactorStatement` | Corollaire 2.3 |
| `AssociatedSupercuspidalInductionTCStatement` | `u uV uP uQ` | `AssociatedSupercuspidalInductionStatement` | Théorème 2.4 |
| `AssociatedCuspidalFactorTCStatement` | `u uV uP uQ uE` | `AssociatedCuspidalFactorStatement` | Corollaire 2.4 |

The principal declaration of the unit is
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement`,
the input of the candidate-existence reduction. The module does not define a totally
complex form of the conjunction `AssociatedFactorStatement`.

## 1. The statements

All vocabulary is that of `AssociatedFactorStatement.md` ("Objects", "Declarations"
and "The four statements"), and nothing is redefined: the relative Weil group
`RelativeWeilGroup c F E` of an arithmetic class family `c`, weak association
`IsWeaklyAssociatedClass`, the local components `P.localComponent v` with their
p-adic classes, the local maps `ι` with `IsLocalRelativeWeilMap`, the canonical
finite additive components, and the local matching predicates `IsPairGammaMatch` and
`IsPairFactorMatch`. Write `Π_v`, `Π'_v` for the local classes of the presentations
at the finite place `v`, and `S_v = S ∘ ι`. For every arithmetic class family `c` and
every Galois extension `E/F` of number fields in `Type u` with `F` **totally
complex** and `[CompactSpace (AdeleQuotient F)]`:

- `AssociatedGammaTCStatement` (Théorème 2.3): if `S` is weakly associated with
  `T.isoClass` and `S'` with `T'.isoClass`, then at every finite place `v`, for every
  local map `ι` and every local-constant system, the pair gamma factors of
  `Π_v × Π'_v` and of `S_v ⊗ S'_v` agree (`IsPairGammaMatch`).
- `AssociatedTemperedFactorTCStatement` (Corollaire 2.3): under the same
  association, if the two local components are tempered and `S_v`, `S'_v` are
  unitary, then the pair L-factors and epsilon factors agree (`IsPairFactorMatch`).
- `AssociatedSupercuspidalInductionTCStatement` (Théorème 2.4): if `S` is irreducible
  and unitary, `T` has a unitary central character and `S` is weakly associated with
  `T.isoClass`, then every local component of every presentation of `T` at a finite
  place is equivalent to a normalized parabolic induction
  `normalizedProductInduced B σ` of unitarizable supercuspidal representations.
- `AssociatedCuspidalFactorTCStatement` (Corollaire 2.4): if `S`, `S'` are irreducible
  and unitary, `T`, `T'` have unitary central characters, and the pairs are weakly
  associated, then the conclusion of the tempered statement holds without the
  temperedness and local unitarity hypotheses.

## 2. Effect of the restriction

Only the base field carries the new instance. Every finite extension of a totally
complex field is totally complex (Mathlib `NumberField.isTotallyComplex_of_algebra`),
so `E` and every intermediate field of `E/F` are totally complex as well; the
statements need not say so. The four statements have no archimedean clause: the
restriction changes only the class of base fields over which they are asserted. The
Library's reductions between these results stay inside one base field. The published
`associatedGamma_of_inputs` derives Théorème 2.3 at `F` from the global functional
equation at the same `F`. The published
`associatedCuspidalFactor_of_supercuspidalInduction_of_tempered` derives Corollaire
2.4 at `(F, E)` from Théorème 2.4 and Corollaire 2.3 at the same `(F, E)`. So the
totally complex forms are linked in the same way (§3).

## 3. Relation to the originals

Each original implies its totally complex form at the same universe levels: apply the
original to the same `c`, `F` and `E` and forget the new instance. A private
development check of Worker 0 compiled the four implications, each as
`fun h c hc F E _ _ _ _ _ _ _ _ => h c hc F E`. The converse is not claimed. The
statements make no claim about base fields with a real place.

The totally complex forms of two reductions, Théorème 2.3 from the global functional
equation and Corollaire 2.4 from Théorème 2.4 and Corollaire 2.3, are stated in
`Langlands.Automorphic.AssociatedFactorTCReductionStatement`.

## 4. Why the totally complex forms are stated

In the Library's route to the local correspondence (route note
`notes/henniart/llc-proof-route.md`), Théorème 2.4 is used by the globalization of
Henniart (2000) §3, and Corollaire 2.4 by the relative pole comparisons and the
isometry factors, only for the CM base field produced by the globalization and its
finite extensions. These are totally complex (Mathlib
`NumberField.IsCMField.isTotallyComplex`). The totally complex forms suffice there,
and their proofs avoid the real-place archimedean theory. The unrestricted
statements stay the targets of their tasks (Tasks 5003, 5175, 4933 and 5178) as
infrastructure; the operator asked their owners to stage the totally complex forms
as supporting proof candidates.

## 5. Sources and provenance

Provenance: *derived*. The four propositions are the special cases, for totally
complex base fields, of the published statements, which follow Henniart (2000)
§§2.3–2.4. Henniart states these results for every number field. The source
correspondence of each clause is in `AssociatedFactorStatement.md`, "Source
correspondence".

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
  p-adique*, Invent. Math. 139 (2000), 439–455 (`henniart-2000-simple-proof`). §2.2,
  printed p.444 (PDF 6): association. §2.3, printed pp.444–445 (PDF 6–7): Théorème 2.3
  and Corollaire 2.3. §2.4, printed p.445 (PDF 7): Théorème 2.4 and Corollaire 2.4.
- G. Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*, Ann. of
  Math. 123 (1986), 145–203 (`henniart-1986-cyclic`). Theorem 4.1, printed p.157
  (PDF 14), and Proposition 4.5 with its Corollary, printed p.160 (PDF 17), which
  Henniart (2000) cites for Théorème 2.3 and Corollaire 2.3.
