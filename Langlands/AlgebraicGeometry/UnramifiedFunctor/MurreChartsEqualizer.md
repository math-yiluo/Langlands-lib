# The locus where two elements of `F(Spec C)` agree

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsEqualizer`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts`. `F` is a presheaf on
`Over (Spec R)`, `C` an `R`-algebra, `ξ₁ ξ₂ ∈ F(Spec C)` (objects `ovR R C` of
`MurreChartsAffine`). This module plays the role of Murre's Lemma 4 (Bourbaki exp. 294,
printed p.252) in the proof of Proposition 2: there the kernel of a pair `η₁, η₂` of elements
over `U ×_S U` is representable by an open immersion; here only the openness of the agreement
locus is proved, from the local representability hypothesis of Proposition 2.

## Contents

* `residueOver R c : Spec κ(c) ⟶ Spec C` for a prime `c` of `C`, `κ(c) = c.ResidueField`.
* `AgreeAt ξ₁ ξ₂ c`: `ξ₁` and `ξ₂` have the same restriction to `Spec κ(c)`.
* `exists_residue_factor`: a morphism `Spec K ⟶ Spec C` over `Spec R` from a field `K`,
  with image `c`, factors through `Spec κ(c)` (`Ideal.ResidueField.lift`).
* `AgreeAt.map_eq`: agreement at `κ(c)` gives agreement at every field point with image `c`.
* `agreeAt_of_map_eq` ((F1b)): conversely, agreement at one field point with image `c` gives
  agreement at `κ(c)`, by `map_injective_of_field`.
* `agreeAt_localization`: suppose every base change of `F` to `Spec 𝒪_{Spec R, s}` is
  represented by a formally unramified scheme `Y_s` locally of finite type (part of the
  hypothesis `UnramifiedRepresentable`). If `ξ₁, ξ₂` agree at `κ(c)`, they agree on
  `Spec C_c`. Proof: `Spec C_c ⟶ Spec R` factors through `Spec 𝒪_r`, `r` the image of the
  closed point (`exists_comp_fromSpecStalk`); by `elemEquiv` the two restrictions are
  morphisms `Spec C_c ⟶ Y_r` over `Spec 𝒪_r` that agree on `Spec κ(c)`; the diagonal of `Y_r`
  is an open immersion, so they agree (`eq_of_isLocalRing`).
* `isOpen_agreeAt` ((F1a), (F2), local representability): `{c | AgreeAt ξ₁ ξ₂ c}` is open.
  If `c` is in it, `ξ₁, ξ₂` agree on `Spec C_c`, hence (F2, `exists_away_eq_of_eq` with
  `M = C \ c`) on some `Spec C[1/a]` with `a ∉ c`; every point of `D(a)` has its residue field
  over `C[1/a]`, so `D(a)` lies in the set.
