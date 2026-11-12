# Admissibility of twists by any Hecke determinant character

Author: Worker 5136.

For an arbitrary Hecke character `χ`, this internal module shows that the finite
adelic and local determinant characters have open kernels. It deduces that
twisting a finite or local realization by `χ ∘ det` preserves and reflects
admissibility.

## Open kernels (namespace `Langlands.Global.HeckeCharacter`)

- `finiteAdelicHeckeDeterminant_isLocallyConstant`: `g ↦ χ(det g)` on
  `GL_n(𝔸_F^∞)` (the Library's `χ.finiteAdelicDeterminant n`) is locally
  constant. This is `isLocallyConstant_finiteDeterminant` from module
  `Langlands.Global.HeckeDeterminantLocalConstancy`.
- `finiteAdelicHeckeDeterminant_isOpen_ker`: its kernel is open.
- `finiteLocalHeckeDeterminant_isLocallyConstant` and
  `finiteLocalHeckeDeterminant_isOpen_ker`: the same for the local character
  `χ_v ∘ det` on `GL_n(F_v)` (the Library's `χ.finiteLocalDeterminant n v`),
  by composing with the continuous local inclusion.

## Admissibility (namespace `Langlands.Automorphic`)

- `FiniteRealization.heckeDeterminantTwist_isAdmissible_iff`: the twisted
  finite realization is admissible if and only if `S` is. The representation of
  the twist is equivalent to the scalar twist of that of `S` (module
  `FiniteLocalTwist`), and the Library's `isAdmissible_twist_iff` applies to
  characters with open kernel.
- `LocalRealization.heckeDeterminantTwist_isAdmissible_iff`: the same for local
  realizations.
- `LocalRealization.heckeDeterminantTwistPadicObject` and
  `heckeDeterminantTwistPadicClass`: for an irreducible admissible local
  realization `L` of `GL_{r+1}(F_v)`, the twist of `L` as an object, and as a
  class, of the Library's p-adic automorphic category
  (`Correspondence.AutomorphicObject`). Irreducibility comes from module
  `FiniteLocalTransport`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.DeterminantTwistAdmissibility` with the finite-order
hypothesis replaced by local constancy, which holds for every Hecke character.
No correspondence with a particular passage of the literature is claimed.
