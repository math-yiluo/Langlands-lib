# Full integral tails for the determinant character of any Hecke character

Author: Worker 5136.

For an arbitrary Hecke character `χ` of a number field `F`, this internal module
chooses a finite set of finite places outside which `χ_v ∘ det` is trivial on
`GL_n(𝒪_v)`, and expresses `χ(det g)` for `g ∈ GL_n(𝔸_F^∞)` as a finite product of
local values. All declarations are in the namespace
`Langlands.Global.HeckeCharacter`.

- `exists_finiteHeckeDeterminantTail`: some finite set `E` of finite places has
  the property that the finite determinant character
  `χ.finiteRestrictedDeterminant n` is `1` on the full integral tail
  `∏_{v ∉ E} GL_n(𝒪_v)` (the Library's `tailReferenceSubgroup`). The Library's
  `exists_character_tail` gives this for every locally constant character of the
  restricted product. Local constancy is
  `HeckeCharacter.isLocallyConstant_finiteDeterminant` (module
  `Langlands.Global.HeckeDeterminantLocalConstancy`), transported along the
  Library's homeomorphism `restrictedProductEquiv`.
- `finiteHeckeDeterminantTail χ`: a chosen such set. It is not claimed to be
  minimal. `finiteHeckeDeterminantTail_trivial` restates its property.
- `finiteLocalHeckeDeterminant_eq_one_outside_tail`: for `v` outside the set,
  `χ_v(det g) = 1` for every `g ∈ GL_n(𝒪_v)`.
- `finiteHeckeDeterminant_eq_prod`: if `S` contains the set and `g` is integral
  outside `S`, then `χ(det (ofFinite g)) = ∏_{v ∈ S} χ_v(det g_v)`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.FiniteDeterminantTail` with the finite-order hypothesis
replaced by local constancy, which holds for every Hecke character. No
correspondence with a particular passage of the literature is claimed.
