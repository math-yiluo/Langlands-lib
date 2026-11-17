# Torsion determination for diagonalizable groups over an affine base

Module `Langlands.GroupScheme.Torus.TorsionDetermination.Diagonalizable`, namespace
`Langlands.GroupScheme.TorsionDetermination`.

This module proves the split affine case of the torsion-determination argument of SGA 3,
Exposé IX, 4.8–4.9, for the diagonalizable group `D_R(Λ) = Spec R[Λ]`
(`Diagonalizable.groupScheme R Λ`) over `Spec R`. It is a helper module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement`. The general case
reduces to this one by an fppf-local argument. The structure `TorsionClosed` and all lemmas
here are internal, not statements quoted from the literature.

## Main results

- `TorsionClosed i`: for a group scheme `G` over `S` and a morphism `i : Z ⟶ G.X` in
  `Over S`, a predicate with two fields. `mul`: for every `T : Over S`, the points
  `T ⟶ G.X` that factor through `i` are closed under multiplication. `torsion`: every point
  `x : T ⟶ G.X` with `x ^ n = 1` for some `n > 0` factors through `i`.
- `isIso_left`: if `Λ` is finitely generated, `i : Z ⟶ D_R(Λ).X` satisfies
  `TorsionClosed i` and the underlying morphism of schemes `i.left` is an immersion, then
  `i.left` is an isomorphism.
- `isIso_left_of_diagonalizable`: the same statement with the two hypotheses of
  `TorsionClosed` written out (`hmul`, `htors`). This is the interface used by the
  general case.

## Points of `D_R(Λ)` as characters

For an `R`-algebra `S`, `affineCharEquiv S` is the multiplicative equivalence between points
`Spec S ⟶ D_R(Λ)` over `Spec R` and characters `Multiplicative Λ →* Sˣ`. It is
`Corepresented.affinePointsEquiv` for the Library's corepresentation of `D_R(Λ)`.
`charPoint χ` is the point of the character `χ`, and `charPoint_eq` shows it is `Spec` of
the algebra map `Diagonalizable.lift R Λ χ : R[Λ] → S`. `charMap g χ` pushes `χ` forward
along an algebra map `g`. `comp_charPoint` gives the naturality
`Spec g ≫ charPoint χ = charPoint (charMap g χ)`, and `charPoint_mul`, `charPoint_pow`,
`charPoint_one` give compatibility with the group structure.

`Lifts i χ` says that `charPoint χ` factors through `i`. Basic properties:

- `Lifts.map`: stable under push-forward along algebra maps.
- `Lifts.mem_range`: the image of every point of `Spec S` under `charPoint χ` lies in the
  image of `i.left`.
- `lifts_of_mem_range`: if `i.left` is an immersion and `F` is a field, `χ` lifts as soon as
  the image of the closed point of `Spec F` lies in the image of `i.left`. Proof: apply
  `exists_lift_of_mem_range` (module `FieldPointLift`).
- `Lifts.of_map`: a character with values in a field `K` lifts if its push-forward along some
  `K → S'` lifts. Both points of `Spec K` and of `Spec S'` map to the same point of `D_R(Λ)`,
  because they are images of the unique point of `Spec K`.
- Under `TorsionClosed i`: `lifts_of_pow_eq_one` (characters with `χ ^ n = 1`, `n > 0`, lift)
  and `Lifts.mul` (lifting characters are closed under products).

## Step A: `i.left` is surjective (`surjective_left`)

1. **Generic points of a torus** (`bot_mem_of_isLocallyClosed`). Let `K` be a field and `I`
   finite. Let `s` be a locally closed subset of `Spec K[ℤ^I]` that contains the image of
   `Spec K[(ℤ/n)^I]` under the reduction map `castPi I n`, for every `n > 0` invertible in
   `K`. Then `s` contains the generic point `(0)`. Write `s = U ∩ C` with `U` open and `C`
   closed. The case `n = 1` puts a point of `s` in `U`, and `(0)` specializes to it, so
   `(0) ∈ U`. For `C`: if a nonzero `a` vanished on `C`, then by
   `exists_not_isNilpotent_mapDomain_castPi` (module `Algebra`) the reduction of `a` modulo
   some `n` would avoid some prime `q` of `K[(ℤ/n)^I]`, whose image lies in `C`. That is a
   contradiction, so the vanishing ideal of `C` is `0` and `(0) ∈ C`.
2. **Universal characters lift** (`lifts_univChar`). Let `π : Λ →+ ℤ^I`. The character
   `univChar K π : λ ↦ e^{π λ} ∈ K[ℤ^I]ˣ`, pushed into any field `F` by an injective algebra
   map `j`, lifts. Its point has image `g((0))`, where `g` is the map of spectra induced by
   `R[Λ] → K[ℤ^I]`. The set `g⁻¹(range i.left)` is locally closed, because the image of an
   immersion is (`Scheme.Hom.isLocallyClosed_range`). It contains the reductions modulo every
   `n`, because the reduced characters are `n`-torsion (`charMap_castPi_pow`) and so lift.
   Step 1 gives `(0) ∈ g⁻¹(range i.left)`, and `lifts_of_mem_range` concludes.
3. **Characters through a free quotient lift** (`lifts_comp_free`). For
   `ψ : ℤ^I → Kˣ`, the character `ψ ∘ π` with values in `K` lifts. Let `F` be the fraction
   field of `K[ℤ^I]`. `twist R ψ` is the automorphism `e^d ↦ ψ(d) e^d` of `K[ℤ^I]`; it is
   injective (`twist_injective`, inverse `twist R ψ⁻¹`). `invMap` is the automorphism
   `e^d ↦ e^{-d}`. After pushing forward to `F`, `charMap_twist_mul` writes `ψ ∘ π` as the
   product of the two universal characters `twist R ψ ≫ j` and `invMap ≫ j`, both of which
   lift by step 2. So the product lifts (`Lifts.mul`), and `Lifts.of_map` brings this back to
   `K`.
4. **All field-valued characters lift** (`lifts_field`). Write
   `Λ ≅ ℤ^I × A` with `A` finite (`Diagonalizable.exists_freeFiniteEquiv`), with projection `π` and section
   `s` of the free part. For `χ : Λ → Kˣ`, put `ψ = χ ∘ s` and `χ₁ = χ · (ψ ∘ π)⁻¹`. Then
   `χ₁` is trivial on `s(ℤ^I)`, so `χ₁ ^ |A| = 1` and `χ₁` lifts. Also `ψ ∘ π` lifts by
   step 3, so `χ = χ₁ · (ψ ∘ π)` lifts.
5. **Surjectivity.** A point `𝔭` of `Spec R[Λ]` is the image of the closed point under the
   character of `R[Λ] → κ(𝔭)`, which lifts by step 4, so `𝔭` lies in the image of `i.left`.

## Step B: `i.left` is an isomorphism (`isIso_left`)

An immersion with closed (here: full) image is a closed immersion
(`IsClosedImmersion.of_isPreimmersion`). A closed immersion into an affine scheme whose map
on global sections is injective is an isomorphism
(`IsClosedImmersion.isIso_of_injective_of_isAffine`). Suppose `a ∈ R[Λ]` is nonzero but is
sent to `0` in `Γ(Z)`. By `exists_mapDomain_mk_ne_zero` (module `Algebra`), its image in
`R[Λ/nΛ]` is nonzero for some `n > 0`. But the quotient character
`Λ → R[Λ/nΛ]ˣ` is `n`-torsion (`quotientChar_pow`), so its point factors through `i`. Hence
the quotient map `R[Λ] → R[Λ/nΛ]` (`Diagonalizable.incl`) factors through `Γ(Z)` and kills
`a`, a contradiction.

## Source

SGA 3, Exposé IX, 4.8–4.9 (torsion determination for groups of multiplicative type). SGA 3
deduces these from the density of the torsion subgroups (IX 4.7). The proof here proves the
needed density statements directly: for fibres over fields (step 1) and for the coordinate
ring (`exists_mapDomain_mk_ne_zero`).
