# Square-integrable local components of cuspidal classes

Author: Worker 34. This module defines when an irreducible cuspidal class of
`GL_{r+1}` over a number field `F` has a square-integrable local component at
a finite place `v`. Harris (1998), Theorem 1.2(i), and Clozel's theorems on
which it rests assume such a component. Nothing is asserted about any
particular class.

## Setting

- `LocalRealization F (r + 1) v` is the published type of actual local
  realizations (`Langlands/Automorphic/PadicLocalCategory`): invariant
  subspaces of automorphic functions with the action `S.representation` of
  `GL_{r+1}(F_v)`, and the predicate `S.IsIrreducible`.
- `CompletionPadic.padicField v` is the completion `F_v` as a finite extension
  of `ℚ_p`, and `canonicalTopologicalData` its canonical `p`-adic topology.
- `PadicField.TopologicalData.IsSquareIntegrable` (published
  `Langlands/Representation/Classification/Tempered`) says that a
  representation of `GL_n(F_v)` is square-integrable modulo the center for
  every Haar measure on the central quotient: it is admissible, has a unitary
  central character, and all its matrix coefficients have absolute values in
  `L²` of the central quotient (`IsSquareIntegrableModCenter`).
- `CuspidalSpectralPresentation S` and its `localComponent v` are as in the
  published `Langlands/Automorphic/CuspidalSpectralPresentation` and
  `Langlands/Automorphic/SupercuspidalComponent`.

## Definitions

- `LocalRealization.IsSquareIntegrable S`: `S` is irreducible and its action
  of `GL_{r+1}(F_v)` is square-integrable modulo the center for the canonical
  topology of `F_v`.
- `CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent c v`:
  some representative `S` of `c` has a spectral presentation `P` whose local
  component `P.localComponent v` is square-integrable. The universe `uV` of
  the presentation's local factor carriers is a parameter, as in
  `HasSpectralSystem` and `HasSupercuspidalComponent`. The definition carries
  the instance parameter `[CompactSpace (AdeleQuotient F)]` of the published
  cuspidal classes, which the published `compactSpace_adeleQuotient` proves.

## Theorems

- `LocalRealization.IsSquareIntegrable.of_isoClass_eq` and
  `isSquareIntegrable_iff_of_isoClass_eq`: square-integrability depends only
  on the smooth isomorphism class. The proof transports irreducibility with
  the published `isIrreducible_iff_of_equiv` and square-integrability with
  `PadicField.TopologicalData.isSquareIntegrable_iff_of_equiv`.
- `hasSquareIntegrableComponent_iff`: a square-integrable component can be
  witnessed at every representative, by transporting a presentation along a
  full equivalence (`CuspidalSpectralPresentation.transport`, whose local
  components keep their isomorphism classes,
  `transport_localComponent_isoClass`).

## Source and conventions

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), Theorem 1.2(i), printed p.185: "the local
  constituent `π_{i,v_i}` is square-integrable". Registered original
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- L. Clozel, *Représentations galoisiennes associées aux représentations
  automorphes autoduales de GL(n)*, Publ. Math. IHÉS 73 (1991), Théorème 5.7(ii),
  printed p.142: the component "appartienne à la série discrète". Registered
  original `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.

The definition uses square-integrability modulo the center in the strict
sense, which includes a unitary central character. In the statements that use
it, the cuspidal class is conjugate self-dual, `π^∨ ≅ π ∘ c`. Its central
character `ω` then satisfies `ω^{-1} = ω ∘ c`. Since `|ω| = ‖·‖^t` for some
real `t` and `‖x^c‖ = ‖x‖` on the ideles, `|ω|^{-1} = |ω|`, so `|ω| = 1`; the strict notion and the notion "essentially
square-integrable" (a twist by `|det|^s` of a square-integrable
representation) therefore select the same local components there. This
remark explains the choice; it is not proved in Lean.

## Scope

As for supercuspidal components, the definition asks for one presentation
whose local component at `v` is square-integrable. The Library does not yet
prove that all presentations of a cuspidal class have isomorphic local
components, so "some presentation" is the faithful reading of "the local
component is square-integrable". The predicate is internal: it combines the
published local components and the published square-integrability predicate.
No relation to supercuspidality (every supercuspidal irreducible
representation with unitary central character is square-integrable) is
proved here.
