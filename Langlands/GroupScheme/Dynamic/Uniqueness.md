# Uniqueness of orbit extensions and limits for separated group schemes

This module proves three facts about the dynamic notions of `Langlands.GroupScheme.Dynamic.Basic`
for a cocharacter `λ : 𝔾_{m,S} ⟶ G`. Here `G` is a group scheme over an arbitrary base scheme
`S` whose structure morphism is separated (`[IsSeparated G.X.hom]`). The facts hold on every
test scheme `T` over `S`.

1. An extension of the orbit map of a point from `T ×_S 𝔾_{m,S}` to `T ×_S 𝔸¹_S` is unique.
2. The limit at zero of a point is unique.
3. The limit at zero lies in the centralizer `Z_G(λ)`.

`G` needs no other hypothesis: no affineness, no finite presentation, no flatness. `T` needs no
flatness either.

## Sources

- Conrad, *Reductive group schemes* (2014), p. 111: for a `𝔾_m`-action on a separated group
  scheme, an extension of the orbit map to `𝔸¹_S` "is unique if it exists since `G` is
  separated and `k[x] ⊂ k[x, 1/x]` for any ring `k`". Also p. 112, for a separated `S`-scheme
  `X` with a `𝔾_m`-action and any `S`-scheme `S'`: the extension over `S'` is unique "because `X`
  is separated and a closed subscheme of `𝔸¹_{S'}` that contains `𝔾_m` must be the entire
  affine line".
- Conrad, Gabber, Prasad, *Pseudo-reductive groups*, 2nd ed. (2015). Lemma 2.1.4 (printed p. 49,
  PDF p. 75) says "extends (necessarily uniquely)". Proposition 2.1.8(2), proof Step 2 (printed
  p. 54, PDF p. 80), shows that the limit lies in `Z_G(λ)`: "`t'.g' = lim_{t→0} (t't).g` because
  the `GL₁`-action on itself by translation extends to an action of `GL₁` on the affine line
  preserving the origin".

Both sources state these facts for affine groups over a ring, or for separated schemes with a
`𝔾_m`-action, using points valued in algebras. This module covers the conjugation action of a
cocharacter on a separated group scheme over an arbitrary base, with arbitrary test schemes.
The route differs from the sources and is described below.

## General separatedness lemmas

- `ext_of_isSchemeTheoreticallyDominant`: let `f, g : X ⟶ Y` and let `s : Y ⟶ Z` be separated
  with `f ≫ s = g ≫ s`. If `f` and `g` agree after a scheme-theoretically dominant morphism
  `j : W ⟶ X`, then `f = g`. Proof: in `Over Z`, the equalizer of `f` and `g` is a closed
  immersion into `X`. This is Mathlib's `isClosedImmersion_equalizer_ι_left`, which uses
  separatedness. `j` factors through the equalizer. So the ideal sheaf of the equalizer lies in
  the kernel of `j`, which is `⊥`. A closed immersion with zero ideal sheaf is an isomorphism, so
  the equalizer inclusion is an epimorphism. The proof follows the structure of Mathlib's
  `ext_of_isDominant_of_isSeparated`. That lemma needs a reduced source and a dominant `j`, and
  does not apply here.
- `isSchemeTheoreticallyDominant_specMap`: if `φ : A ⟶ B` is injective, then
  `Spec φ : Spec B ⟶ Spec A` is scheme-theoretically dominant. Its kernel is the ideal sheaf of
  the kernel of `φ` (Mathlib's `Scheme.ker_of_isAffine`).

## The affine line over an affine open

Fix `f : Spec A ⟶ S`. `Spec A` is regarded as a scheme over `S` through `f`.

- `AffineLine.polynomialScheme f` is `Spec A[X]` over `S` through `Spec A`.
  `AffineLine.polynomialProj f` is its projection to `Spec A`.
- `AffineLine.polynomialPoint f : Spec A[X] ⟶ Spec A ×_S 𝔸¹_S` is the point whose first
  component is the projection and whose coordinate is `X`.
- `AffineLine.polynomialSections f : A[X] ⟶ Γ(Spec A ×_S 𝔸¹_S)` sends `a` to its pullback along
  the first projection and `X` to the coordinate. It is `Polynomial.eval₂RingHom`.
  `polynomialPointInvLeft` and `polynomialPointInv` are the corresponding morphism
  `Spec A ×_S 𝔸¹_S ⟶ Spec A[X]` over `S`. `polynomialPointInvLeft_comp`,
  `polynomialPointInv_comp_polynomialProj` and `homEquiv_polynomialPointInv_comp_snd` give its
  two components.
- `polynomialPointInv_comp_polynomialPoint`: `polynomialPointInv f ≫ polynomialPoint f = 𝟙`.
  So `polynomialPoint f` is a split epimorphism, which is all that is used. The module does not
  prove that it is an isomorphism.
- The existing `Gm.relativeCoordUnit A` from
  [`MultiplicativeLaurent`](../MultiplicativeLaurent.md) is the unit `X` of
  `A[X, X⁻¹]`. `laurentScheme f` is
  `Spec A[X, X⁻¹]` over `S`. `laurentInclusion f : Spec A[X, X⁻¹] ⟶ Spec A[X]` is the inclusion,
  and `laurentUnit f` is the global unit `X` on `Spec A[X, X⁻¹]`. The ring maps
  `polynomialC A : A ⟶ A[X]` and `polynomialToLaurent A : A[X] ⟶ A[X, X⁻¹]` are abbreviations
  for `Polynomial.C` and `Polynomial.toLaurent`.
- `laurentInclusion_polynomialPoint`: on `Spec A[X, X⁻¹]`, `polynomialPoint f` factors through
  `Spec A ×_S 𝔾_{m,S}` via the point `(projection, X)`.

## Agreement on `T ×_S 𝔾_{m,S}` forces equality

- `AffineLine.hom_ext_of_unitInclusion_affine`: let `Y` be separated over `S`. If two morphisms
  `e, e' : Spec A ×_S 𝔸¹_S ⟶ Y` agree on `Spec A ×_S 𝔾_{m,S}`, they are equal. Because
  `polynomialPoint f` is a split epimorphism, it suffices that `e` and `e'` agree on
  `Spec A[X]`. They agree on `Spec A[X, X⁻¹]` by `laurentInclusion_polynomialPoint`. Since
  `A[X] ⟶ A[X, X⁻¹]` is injective, `Spec A[X, X⁻¹] ⟶ Spec A[X]` is scheme-theoretically
  dominant, and `ext_of_isSchemeTheoreticallyDominant` applies. This is the
  `k[x] ⊂ k[x, 1/x]` argument of Conrad p. 111, with `k = A`.
- `AffineLine.pullbackFstToWhiskerRight` and `pullbackFstToWhiskerRight_comp`: for an affine
  open `a : Spec A ⟶ T`, the pullback of the first projection `T ×_S 𝔸¹_S ⟶ T` along `a` maps
  to `Spec A ×_S 𝔸¹_S`. Its composite with `a × 𝔸¹` is the projection of the pullback.
- `AffineLine.hom_ext_of_unitInclusion`: let `T` be any scheme over `S` and `Y` separated over
  `S`. Two morphisms `e, e' : T ×_S 𝔸¹_S ⟶ Y` over `S` that agree on `T ×_S 𝔾_{m,S}` are equal.
  The proof pulls back the affine open cover of `T` along the first projection and uses
  `Scheme.Cover.hom_ext`. On each piece it applies the affine case to the restrictions along
  `a × 𝔸¹`, which agree on `Spec A ×_S 𝔾_{m,S}` by `whisker_exchange`.

Conrad (p. 112) phrases the argument through closed subschemes containing `𝔾_m`. That needs
`T ×_S 𝔾_{m,S}` to be scheme-theoretically dense in `T ×_S 𝔸¹_S`. Base change does not preserve
scheme-theoretic density without flatness, so the proof here works on affine opens of `T` and
uses the polynomial point. This route needs no flatness of `T`.

## The scaling action

- `AffineLine.scale T : (T ×_S 𝔾_{m,S}) ×_S 𝔸¹_S ⟶ T ×_S 𝔸¹_S` is `((t, s), x) ↦ (t, s x)`.
  Its second component is the product of the coordinate functions.
- `whiskerLeft_unitInclusion_scale`: on `(T ×_S 𝔾_{m,S}) ×_S 𝔾_{m,S}`, scaling is the map
  `((t, s), x) ↦ (t, s x)` given by the group law of `𝔾_{m,S}`, followed by the inclusion
  `T ×_S 𝔾_{m,S} ⊆ T ×_S 𝔸¹_S`.
- `lift_zeroSection_scale`: scaling sends the zero section of `(T ×_S 𝔾_{m,S}) ×_S 𝔸¹_S` to the
  zero section of `T ×_S 𝔸¹_S`, composed with the projection to `T`.

## Consequences for separated group schemes

Fix `λ` and `[IsSeparated G.X.hom]`.

- `Dynamic.IsOrbitExtension.unique`: two extensions of the orbit map of `g : T ⟶ G` are equal.
  This is `hom_ext_of_unitInclusion`.
- `Dynamic.HasLimit.unique`: if `l` and `l'` are both limits of `g`, then `l = l'`.
- `Dynamic.HasLimit.mem_centralizer`: if `l` is a limit of `g`, then `l` lies in `Z_G(λ)(T)`.
  Let `e` be an extension with value `l` at zero, and work on the test scheme
  `T ×_S 𝔾_{m,S}`. Consider two morphisms `(T ×_S 𝔾_{m,S}) ×_S 𝔸¹_S ⟶ G`: the first is
  `((t, s), x) ↦ λ(s) e(t, x) λ(s)⁻¹`, and the second is `e ∘ scale`, that is
  `((t, s), x) ↦ e(t, s x)`. On `(T ×_S 𝔾_{m,S}) ×_S 𝔾_{m,S}` both equal
  `λ(s x) g(t) λ(s x)⁻¹`. This uses `whiskerLeft_unitInclusion_scale`, that `λ` is a group
  homomorphism (`MonObj.mul_comp`), and the orbit naturality `whiskerRight_orbit`. So the two
  morphisms are equal by `hom_ext_of_unitInclusion`. Evaluating at `x = 0` gives
  `λ(s) l(t) λ(s)⁻¹` on the left. On the right it gives `l(t)`, by `lift_zeroSection_scale`.
  This is the argument of CGP Proposition 2.1.8, proof Step 2. Since `l` is a point of the
  centralizer exactly when its orbit map is constant, the conclusion is `l ∈ Z_G(λ)(T)`.

Together with the published `hasLimit_of_mem_centralizer` (`Dynamic.Basic`), these facts say
that for separated `G`, sending a point of `P_G(λ)(T)` to its limit is a well-defined
retraction onto `Z_G(λ)(T)`. This module does not prove that limits are multiplicative or that
`P_G(λ) = U_G(λ) ⋊ Z_G(λ)` on points. It does not prove representability of `P_G(λ)`,
`U_G(λ)` or `Z_G(λ)`.
