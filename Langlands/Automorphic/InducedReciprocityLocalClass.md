# Local class of an induced reciprocity representation at a place with one place above

Author: Worker 5134. Module `Langlands.Automorphic.InducedReciprocityLocalClass`, namespace
`Langlands.ClassField.Global.RelativeWeilGroup`. It is a helper for the proof of
`HenniartGlobalizationStatement` (Henniart 2000, §3.4).

Setting: `c` is a fundamental class family with `h : FundamentalClass.Restriction c`.
The number fields `F ⊆ E' ⊆ L` all lie in universe `u`, and `L / F` is Galois. The
representation is `S = inducedReciprocityRepresentation.{u, uV} c F E' L h ξ`, which is
`Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` for a Hecke character `ξ` of `E'`. Its class is
taken in the continuous exact Grothendieck group, for the discrete topology on the Galois
quotient.

## Result

`continuousRestrict_inducedReciprocityRepresentation_class hN2 h ξ w e ι hι u eu heu`.
The hypotheses are:

- `hN2 : LocalInducedRestrictionStatement.{uV, u}`, Tate's local restriction formula for
  relative Weil groups (Tate 1979, (2.3.5) with (1.6.1)). It is a Library statement that
  is not yet proved, so the theorem takes it as a hypothesis.
- `z` is a finite place of `F` and `w` a finite place of `L` above `z`. The candidate `e`
  is a reciprocity candidate of `L_w`, and `ι : W_{F_z} → W_{L/F}` is a local
  relative Weil map for `z, w, e` (`IsLocalRelativeWeilMap`).
- `u` is a finite place of `E'` above `z`, and it is the only one
  (`[Subsingleton (FinitePlacesAbove E' z)]`).
- `eu` is a reciprocity candidate of `E'_u` (as `towerPadicField z u`) satisfying the
  Library's geometric Weil reciprocity relation `heu`.

Conclusion: the restriction of `[S]` along `discreteLocalMap ι` equals the induction of
the character class `[weilCharacter eu ξ_u]` along `completionWeilMap z u : W_{E'_u} → W_{F_z}`.
Here `ξ_u = quasicharacterAt u _ (ξ.finiteComponent u)` is the component of `ξ` at `u`.

Proof. `inducedReciprocityRepresentation_class` (Library) writes `[S]` as the induction
along `W_{L/E'} → W_{L/F}` of the reciprocity character class. The hypothesis `hN2`
provides local maps `ι_u : W_{E'_u} → W_{L/E'}` and the restriction formula, which is a
sum over the places of `E'` above `z`. With only one such place the sum has a single term
(`Fintype.sum_subsingleton`). Restricting a character class along `ι_u` gives the class
of the composite character (`continuousRestrict_characterClass`). The transfer property of
`ι_u` from `hN2` identifies that composite with the Weil character of `ξ_u` along `eu`
(Library `continuousReciprocityCharacter_comp_eq_weilCharacter`).

## Provenance

Henniart (2000), §3.4, computes the local component at `v` of the induced representation
`S(X)` this way. With one place of `E'` above `v`, Tate's formula gives a single induced
character.
