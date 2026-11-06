# Unramified characters on unipotent radicals

Lean module: `Langlands.Representation.Exponents.UnramifiedTwistRadicals`.

This module contains general facts used in the first step of the proof of Renard 2026,
VII.1.3 (printed p.224/PDF p.230), where `ρ` is replaced by an unramified twist. The
twisting comparison itself is Renard III.2.11. Its Library form (in
`Langlands.Representation.Aubert.General.CharacterTwistEquivalences`) needs a smooth
character that is trivial on the radical points of the parabolic. This module supplies
that condition for unramified characters. Nothing here depends on the maximal-Levi
setting: every result is stated for an arbitrary group scheme `H` over a field `k`, with
the local-field and point-topology assumptions each result needs.

## Rational characters on unipotent groups

- `rationalCharacterEval_map_eq_one_of_isUnipotent`: for `f : V ⟶ G` with `V` unipotent,
  every rational character `c` of `G` takes the value `1` on `f(F)(y)`.

  Proof: the restriction `characterRestrict f c` corresponds to the homomorphism
  `f ≫ c` from the unipotent group `V` to the split torus `𝔾_m`. By
  `IsUnipotent.hom_eq_zero_of_isSplitTorus` this homomorphism is trivial. So the
  restricted character is `0`, and `rationalCharacterEval_characterRestrict` turns this
  into the claimed value at points.
- `map_mem_rationalCommonNormKernel_of_isUnipotent`: over a nonarchimedean local field,
  such points lie in the common kernel `Plancherel.rationalCommonNormKernel G` of the
  norms `|c(·)|`. This is immediate from the previous result.
- `unramifiedCharacter_map_eq_one_of_isUnipotent`: an unramified character of `G(F)` is
  trivial on `f(V(F))`. An element of `Plancherel.unramifiedCharacters` is by definition
  trivial on that common kernel.

## Smooth characters and radicals

- `unramifiedSmoothCharacter ψ`: the unramified character `ψ` of `H(F)` viewed as an
  `Induction.SmoothCharacter`. Its kernel is open by
  `Plancherel.unramifiedCharacter_isOpen_ker`. The definition is stated for any topology
  on `H(F)` that makes it a nonarchimedean group. `unramifiedSmoothCharacter_apply`
  states that its underlying homomorphism is `ψ`.
- `pointImage_radical_le_ker_unramifiedSmoothCharacter`: for a parabolic `p : P ⟶ H` with
  geometric unipotent radical `r : U ⟶ P`, the radical points `pointImage (r ≫ p)` lie
  in the kernel of `unramifiedSmoothCharacter ψ`. This is the previous section applied to
  `r ≫ p`, using that the radical is unipotent (`hr.1.isUnipotent`).

## Jacquet modules

Here `H(F)` carries the rational point topology `RationalPointFamily.pointTopology`,
which is locally compact and a nonarchimedean group. This is the setting of
`jacquetFunctor`.

- `jacquetFunctor_subsingleton_twist_iff`: for every actual parabolic `(p', l', r')` of
  `H` and every smooth character `χ` of `H(F)` trivial on `pointImage (r' ≫ p')`, the
  normalized Jacquet module of `A ⊗ χ` is trivial if and only if that of `A` is. Proof:
  convert `Subsingleton` of the carrier into `IsZero`
  (`SmoothRep.isZero_iff_subsingleton_carrier`), then apply the Library result
  `normalizedJacquet_isZero_characterTwist_iff`.
- `jacquetFunctor_subsingleton_unramifiedTwist_iff`: the same statement for an
  unramified `ψ` of `H(F)`, with the radical condition supplied by
  `pointImage_radical_le_ker_unramifiedSmoothCharacter`.
- `properJacquet_subsingleton_unramifiedTwist`: if every normalized Jacquet module of `A`
  for a proper actual parabolic of `H` vanishes, then the same holds for `A ⊗ ψ`, for
  every unramified `ψ`. The hypothesis and the conclusion have exactly the form of the
  supercuspidality hypothesis in
  `MaximalLeviSupercuspidalReducibilityStatement`, with `H` in place of `M`.
