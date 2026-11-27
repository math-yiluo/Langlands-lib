# Arithmetic regular local approximation of a strictly Henselian trait

`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximationStatement`
states finite factorization through a Henselian regular local chart after a
uniformizer-preserving extension of traits.

## Hypotheses and conclusion

Let `W` be a commutative domain and a discrete valuation ring, with
`HenselianLocalRing W` and separably closed residue field
`IsSepClosed (ResidueField W)`. Let `L` be a field with `IsFractionRing W L`,
let `π` be a uniformizer of `W`, and let `f : C →+* L` be a ring map from a
commutative ring `C` of finite type over `ℤ`. The types `W`, `L`, and `C`
range independently over universes `u`, `v`, and `w`. Mathlib's
`IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies the
uniformizer conditions in the statement with irreducibility.

- There is a strictly Henselian DVR `W' : Type u` and a local homomorphism
  `i : W →+* W'` taking `π` to a uniformizer. The residue field extension is
  purely inseparable for the algebra structure induced by `ResidueField.map i`.
- There is a Henselian regular local domain `B : Type u`, with
  `t ∈ 𝔪_B`, `t ∉ 𝔪_B²`, and `B/(t)` regular local, and a local homomorphism
  `j : B →+* W'` taking `t` to a uniformizer. The map `j` may have a kernel.
  For some subfield `k` of `ResidueField B`, `Field.FG k` means that `k` is
  finitely generated as a field over its prime field, and `ResidueField B`
  is purely inseparable over `k` via the inclusion. In residue
  characteristic zero, a purely inseparable field extension is trivial, so
  `ResidueField B` itself is finitely generated over its prime field.
- There is a ring map `g : C →+* Localization.Away t`. The equations
  defining `iFrac : L →+* FractionRing W'` and
  `jAway : Localization.Away t →+* FractionRing W'` require them to extend
  `i` and `j` into `FractionRing W'`, respectively. A uniformizer-preserving
  map of DVRs is injective since every nonzero element is a unit times
  a power of the uniformizer. The image of `t` is invertible in `FractionRing W'`.
  The universal properties of the two localizations therefore identify
  `iFrac` and `jAway` with the induced maps. The final equation is the
  equality of ring homomorphisms `jAway.comp g = iFrac.comp f`.

## Source and derivation

The source is P. Deligne, *Résumé des premiers exposés de A. Grothendieck*,
SGA 7 I, Exposé I, Lecture Notes in Mathematics 288 (1972). See Lemma
0.5.1 and §§0.5.2–0.5.3 on pp. I-4–I-5 and the use of the regular divisor
in Variante 1.3 on pp. I-6–I-7. The retained PDF is registered as
`deligne-1972-sga7-i-expose-i-monodromie` and has SHA-256
`b5a598de1362529cd2be9f71ba17a40e07bc36cef9431f0586caa317653957ce`.

In mixed characteristic, the reduction to a complete DVR with perfect
residue field in Variante 1.3 cites EGA 0 III, Proposition 10.3.1.
Apply its flat local extension construction to the perfection of the
residue field. Its construction extends the maximal ideal from the
original ring, a property retained on completion. Flatness keeps `π`
a nonzero divisor, and the complete Noetherian local ring with this
principal maximal ideal is a DVR. Its residue field is the perfection
of the original separably closed residue field, hence is algebraically
closed. This gives a strictly Henselian `W'` and the required purely
inseparable residue extension. The retained EGA source is
A. Grothendieck, *Préliminaires*, EGA III, first part, Chapter 0, pp. 20–23,
registered as `grothendieck-1961-ega-0-iii-preliminaires`.
The file `Grothendieck--Preliminaires (EGA III-1, Chapitre 0, sections 8-13)--1961.pdf`
has SHA-256 `24cb7a75e125f44022411d4b2a86afd2453ab45876945e0ee02b5dd8d5dc5655`.
In equal characteristic one can take `W' = W`.

Write `A → W'` for the arithmetic base DVR of §0.5.2 or §0.5.3 and `τ`
for its uniformizer. In equal characteristic the base is obtained by
localizing the polynomial ring in a uniformizer over the prime field.
In mixed characteristic §0.5.3 uses an Eisenstein extension of the
Cohen ring over the perfection of a finitely generated residue subfield.
In both cases the map takes `τ` to a uniformizer and the generic and residue
field extensions are separable, as in Lemma 0.5.1.

Multiply the images of finitely many `ℤ`-algebra generators of `C` by
powers of `τ` to put them in `W'`. The `A`-subalgebra of `W'` generated
by these numerators has a localization at `τ` containing the image of
`C`. Factor its map to `W'` through a smooth finite type `A`-algebra,
as in the approximation of Lemma 0.5.1. Localize that smooth algebra at the
inverse image of the maximal ideal of `W'` and take the henselization `B`.
The local map to `W'` extends to `B` by the Henselian property. Smoothness
over the regular DVR and smoothness of the closed fibre give regularity
of the local chart and of its quotient by `τ`, which persists under
henselization. Regular local rings are domains. Take `t` to be the image
of `τ` in `B`. It lies in `𝔪_B` and maps to a uniformizer of `W'`, so it
lies outside `𝔪_B²`. Localizing at `t` gives the required factorization
and the composite identity.

The residue field of the point of the smooth chart is finitely generated
as a field over the arithmetic base residue field and is unchanged by
henselization. For the base in §0.5.3, adjoin the same generators to the
finitely generated subfield whose perfection is the base residue field.
The chart residue field is purely inseparable over the resulting
finitely generated field. For the prime field base in §0.5.2, the chart
residue field is itself finitely generated over the prime field.
