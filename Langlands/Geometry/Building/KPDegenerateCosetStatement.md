# KP Proposition 13.7.4 (1): translates meeting a deeper lattice are degenerate

Author: Worker 3557.

This module belongs to the Kaletha–Prasad Bruhat–Tits program (task
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`). It states part (1) of KP
Proposition 13.7.4 for the Library's supplied Lie filtrations and for points
of the apartment. Let `X ∈ 𝔤_{x,r}`. If the translate `Ξ = X + 𝔤_{x,r+}` in
the Lie algebra meets `𝔤_{y,s}` for some `s > r`, then `Ξ` contains a
nilpotent element. For periodic `L` the translate is KP's coset in
`𝔤_{x,r}/𝔤_{x,r+}`; for arbitrary supplied data it need not lie in
`𝔤_{x,r}` (see "Setting"). The module has one statement and proves nothing.

## Setting

`F` is a nonarchimedean local field with ring of integers `𝒪[F]`, and `G` a
group scheme over `Spec F` with `[IsAffineHom G.X.hom]`.
`P : ParahoricBuildingData G` is the Library's building data. It contains the
connected reductive structure of `G`, the maximal split torus `P.i : S → G`
and the apartment `P.Apartment`. Its affine roots `P.affineRoots` are those
of KP Definition 6.3.4 (module `Langlands.Geometry.Building.KPApartment`); by
that definition the derivative of every affine root `ψ` is `rootForm P.i a`
for a relative root `a`. `L : P.LieFiltrationData` supplies the
lattices `z_r` in `Lie(Z)` and `u_ψ` in the root spaces (module
`Langlands.Geometry.Building.KPLieFiltration`). For real `r`:

- `L.lieFiltrationReal x r` is `𝔤_{x,r}`, extended from `r ≥ 0` to real `r`
  as in KP 13.3.1 (module `Langlands.Geometry.Building.KPLieFiltrationDual`).
  With `n = ⌈-r⌉₊`, it consists of the `Y` with `a • Y ∈ 𝔤_{x,r+n}` for all
  `a ∈ 𝔪^n`.
- `L.lieFiltrationPlusReal x r` is `𝔤_{x,r+}`, the supremum of the
  submodules `𝔤_{x,s}` for `s > r`. For every `L` it contains each
  `𝔤_{x,s}` with `s > r` (`lieFiltrationReal_le_lieFiltrationPlusReal`).
- When `L` is periodic (`L.IsPeriodic`, KP's `𝔤_{x,r+1} = 𝔪 𝔤_{x,r}`), the
  real family `r ↦ 𝔤_{x,r}` is decreasing (`lieFiltrationReal_antitone`).
  Then `𝔤_{x,r+}` is KP's union `⋃_{s>r} 𝔤_{x,s}`
  (`mem_lieFiltrationPlusReal`), and it lies in `𝔤_{x,r}`
  (`lieFiltrationPlusReal_le`), so `𝔤_{x,r}/𝔤_{x,r+}` is defined.
- For arbitrary supplied data neither holds in general. The field
  `centralizerLie_antitone` makes `z_t` decreasing for `t ≥ 0`, but the
  extension to negative depths need not be decreasing. For example, take
  `G = 𝔾_m`, so `Lie(G) = F`, with the Library's torus building data
  (`ParahoricBuildingData.ofTorus`, which has no affine roots), a
  uniformizer `ϖ`, and `z_t = 𝒪` for `0 ≤ t < 1/2`, `z_t = ϖ²𝒪` for
  `t ≥ 1/2`. At `r = -1/4` the shift is `n = 1` and `r + n = 3/4`, so
  `𝔤_{x,r} = {Y : ϖY ∈ ϖ²𝒪} = ϖ𝒪`. But `𝔤_{x,r+}` contains `𝔤_{x,0} = 𝒪`,
  so `𝔤_{x,r+} ⊄ 𝔤_{x,r}`, and the supremum is not KP's quotient
  denominator.

Nilpotence and degeneracy are those of KP Definition 13.6.5 (module
`Langlands.Geometry.Building.KPNilpotentCoset`): `IsDegenerateLieCoset M X`
says that `X + M` contains an element `Y` that some 1-parameter subgroup
`ν : 𝔾_m → G` over `F` contracts to `0`, i.e. `Y ∈ 𝔤_{>0}(ν)`.

## The statement

### `DegenerateCosetOfDeeperIntersectionStatement`

For every `F`, `G`, `P` and `L` as above, all points `x y : P.Apartment` and
all real `r < s`: if `X ∈ L.lieFiltrationReal x r` and some
`Y ∈ L.lieFiltrationReal y s` satisfies
`Y - X ∈ L.lieFiltrationPlusReal x r`, then
`IsDegenerateLieCoset (L.lieFiltrationPlusReal x r) X`.

In KP's notation, for periodic `L`: if the coset `Ξ = X + 𝔤_{x,r+}` of
`𝔤_{x,r}/𝔤_{x,r+}` satisfies `Ξ ∩ 𝔤_{y,s} ≠ ∅` for some `s > r`, then `Ξ` is
degenerate. For arbitrary `L` the statement is the same implication for the
translate `Ξ = X + 𝔤_{x,r+}` in `Lie(G)`, with `X ∈ 𝔤_{x,r}`. That translate
need not be a coset of `𝔤_{x,r}/𝔤_{x,r+}`, because `𝔤_{x,r+}` need not lie
in `𝔤_{x,r}`. `IsDegenerateLieCoset M X` only asks for a nilpotent element of
`X + M`, so it applies to any such translate.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page numbers are the
PDF page numbers minus 31.

- Proposition 13.7.4, printed p. 483, PDF p. 514: "Let Ξ be a coset in
  𝔤_{x,r}/𝔤_{x,r+}. (1) If for some y ∈ B(G) and s > r, Ξ ∩ 𝔤_{y,s} ≠ ∅,
  then Ξ is degenerate." The sentence before the proposition fixes `x`:
  "In the following proposition, x is a point of the apartment A of B(G)
  corresponding to the maximal k-split torus S of G." Part (2), the
  equivalence with instability under `G_x`, continues on printed p. 484,
  PDF p. 515.
- Proof of 13.7.4 (1), printed p. 483, PDF p. 514: by Lemma 13.7.3,
  `𝔤_{y,s} ⊂ 𝔤_{x,s} + N ⊂ 𝔤_{x,r+} + N`, where `N` is the set of nilpotent
  elements. Hence `Ξ` contains a nilpotent element.
- Lemma 13.7.3, printed p. 483, PDF p. 514: `𝔤_{y,r} ⊂ 𝔤_{x,r} + N` for all
  `x, y ∈ B(G)` and `r ∈ ℝ`. The proof first reduces to `x, y` in one
  apartment `A`. It then splits `𝔤_{y,r}` along the root spaces of roots `a`
  with `a(v) > 0`, `= 0` and `< 0`, where `x = v + y`.
- Definition 13.6.5, printed p. 480, PDF p. 511 (nilpotent elements,
  degenerate cosets).
- The authors' corrections of 1 November 2024
  (`kaletha-prasad-2024-corrections`), PDF p. 49: the Chapter 13 entries
  concern Proposition 13.5.2(1), the end of 13.6.2 and the proof of Theorem
  13.8.5. None concerns Lemma 13.7.3 or Proposition 13.7.4.

## Derived formulation

**Points of the apartment.** KP allow any `y ∈ B(G)`. The supplied Lie
filtration `L` defines `𝔤_{x,r}` only for points `x` of the apartment
`P.Apartment`. The Library does not extend it to the reduced building
`P.ReducedBuilding`; that would need the adjoint action of `G(F)` on `Lie(G)`
and a compatibility of `L` with `N(F)`. So `x` and `y` range over
`P.Apartment`. KP's proof of Lemma 13.7.3 reduces to this case ("Without
loss of generality we can assume that both x and y lie in A"), using the
action of `G(k)` on the building.

**Supplied lattices.** KP's `𝔤_{x,r}` are the Lie lattices of their integral
models (§13.3). Here they are given by supplied `L`. KP's lattices are
periodic, and for periodic `L` the translate `X + 𝔤_{x,r+}` is KP's coset in
`𝔤_{x,r}/𝔤_{x,r+}`. For arbitrary `L` it is a translate in `Lie(G)` (see
"Cosets and translates" below). The statement assumes neither the apartment
axioms nor periodicity of `L`,
because the expected argument, the route of Lemma 13.7.3, needs neither. It
is not proved here. The argument uses only that the derivative of each
affine root is a relative root, which holds by the definition of
`P.affineRoots`, and the field `affineRootLie_le` of `L`
(`u_ψ ⊆ Lie(U_a)` when `a` is the derivative of `ψ`).

1. Let `s ≥ 0` first. An element `Y ∈ 𝔤_{y,s}` is a finite sum of an
   element of the image of `z_s` and elements of `u_ψ` with `ψ(y) ≥ s`.
   Collect the terms with `ψ(x) ≥ ψ(y)`, and the `z_s` term, into `A`; they
   lie in `𝔤_{x,s}`. Put the terms with `ψ(x) < ψ(y)` into `B`.
2. By the definition of `P.affineRoots`, the derivative of each `ψ` in `B`
   is `rootForm P.i a` for a relative root `a`. So `u_ψ` lies in `Lie(U_a)`,
   the sum of the weight spaces `𝔤_{na}`, `n ≥ 1`
   (`P.rootLieSpace a`), and `a(y - x) = ψ(y) - ψ(x) > 0`. Only finitely
   many roots occur. `P.Apartment` is an affine space under
   `TranslationSpace P.i`, a quotient of `V S = ℝ ⊗ X_*(S)` on which the
   roots are defined. So some cocharacter `ν` of `S` near a lift of `y - x`
   has `⟨a, ν⟩ > 0` for all these roots. Then `B ∈ 𝔤_{>0}(ν)`, and `B` is
   nilpotent.
3. `A ∈ 𝔤_{x,s} ⊆ 𝔤_{x,r+}` since `s > r`
   (`lieFiltrationReal_le_lieFiltrationPlusReal`, no hypothesis on `L`).
   If `Y - X ∈ 𝔤_{x,r+}`, then `B - X = (Y - X) - A ∈ 𝔤_{x,r+}`. So the
   translate contains the nilpotent element `B`.
4. For `s < 0`, let `n = ⌈-s⌉₊` and `ϖ` a uniformizer. Then
   `ϖⁿ Y ∈ 𝔤_{y,s+n}`, and step 1 gives `ϖⁿ Y = A + B`. Here
   `ϖ⁻ⁿ A ∈ 𝔤_{x,s}`, by the definition of `lieFiltrationReal`, and
   `ϖ⁻ⁿ B` is nilpotent for the same `ν`. Steps 2 and 3 then apply to
   `Y = ϖ⁻ⁿ A + ϖ⁻ⁿ B`.

**Cosets and translates.** `Ξ ∩ 𝔤_{y,s} ≠ ∅` is written as "some
`Y ∈ 𝔤_{y,s}` has `Y - X ∈ 𝔤_{x,r+}`". Degeneracy is
`IsDegenerateLieCoset (𝔤_{x,r+}) X`: some element of `X + 𝔤_{x,r+}` is
nilpotent. Both are conditions on the translate `X + 𝔤_{x,r+}` in `Lie(G)`.
The hypothesis `X ∈ 𝔤_{x,r}` takes the representative `X` from the depth-`r`
lattice. When `𝔤_{x,r+} ⊆ 𝔤_{x,r}`, for instance for periodic `L`
(`lieFiltrationPlusReal_le`), the translate is then a coset of
`𝔤_{x,r}/𝔤_{x,r+}`, and every such coset has this form, as in KP. For
arbitrary `L` the inclusion can fail (example under "Setting"); then the
translate need not lie in `𝔤_{x,r}`, and the statement is only about the
translate. The argument above does not use `X ∈ 𝔤_{x,r}`.

## Not included

- `y` outside the apartment (see above).
- Part (2) of Proposition 13.7.4 and the second sentence of Proposition
  13.6.7 (instability under `G_x`). KP's instability means that `0` lies in
  the Zariski closure of an orbit of the algebraic group `G_x` over the
  residue field. The Library has orbits and orbit closures for scheme
  actions (`SchemeAction.orbit`, `SchemeAction.exists_reduced_orbitClosure`),
  but no residue-field group `G_x` acting algebraically on
  `𝔤_{x,r}/𝔤_{x,r+}`.
- The first sentence of Proposition 13.6.7 (optimal points, §13.4).

## Provenance

Derived. The statement is KP Proposition 13.7.4 (1), with `y` restricted to
the apartment, with the Library's supplied Lie filtration in place of KP's
lattices, and with KP's coset read as a translate in `Lie(G)` (a coset of
`𝔤_{x,r}/𝔤_{x,r+}` for periodic `L`). The name
`DegenerateCosetOfDeeperIntersectionStatement` is internal. The module uses
Worker 13's `LieFiltrationData`, `lieFiltrationReal` and
`lieFiltrationPlusReal` (modules `KPLieFiltration` and
`KPLieFiltrationDual`), and `IsDegenerateLieCoset` (module
`KPNilpotentCoset`).
