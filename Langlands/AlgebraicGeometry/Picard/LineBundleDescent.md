# Descent of a line bundle from compatible sections

This helper module proves a gluing statement used in the proof of
`Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingStatement`.
It is internal: it is not a Library statement and has no literature source of its own.
It replaces, in the special situation needed there, the descent of an invertible module
along a cofiltered limit (Stacks Project, Limits, Lemma 32.10.3).

## Section-map lemmas (namespace `Langlands.SchemeModule.LineBundleDescent`)

These lemmas are kept in their own namespace so that their generic names cannot collide
with lemmas of other modules in `Langlands.SchemeModule`.

- `sectionHom_app`, imported from `Modules/TensorSections`: the morphism `sectionHom M s : 𝒪_X ⟶ M` of a global section `s`
  sends `a ∈ Γ(X, U)` to `a • s|_U`.
- `trivializesOn_iff_bijective`: `TrivializesOn M s U` holds exactly when
  `(sectionHom M s).app V` is bijective for every open `V ≤ U`. The proof uses that an
  isomorphism of module sheaves is one on every open
  (`Scheme.Modules.Hom.isIso_iff_isIso_app`) and that opens of `U` correspond to opens of the
  open subscheme `U`.
- `hom_app_map`, `map_map_apply`, `map_id_apply`: naturality of a morphism of module sheaves
  with respect to restriction, and composition and identity of restrictions, on elements.
- `sectionHom_pushforward_app`: for `π : Y' ⟶ Y` and a module sheaf `F` on `Y'`, the section
  morphism of `t` viewed in `π_* F` sends `a ∈ Γ(Y, V)` to the image under `sectionHom F t` of
  `π^#(a) ∈ Γ(Y', π⁻¹ V)`.
- `sectionHom_app_of_eq_smul`, `trivializesOn_of_eq_smul`: if `t|_V = c • s|_V` with `c` a
  unit and `s` trivializes on `V`, then `t` trivializes on `V`.
- `nonempty_iso_of_trivializesOn`: a trivializing section gives `M|_U ≅ 𝒪_U`.

## The submodule `rangeOn`

These declarations are in the same namespace `Langlands.SchemeModule.LineBundleDescent`.
For a family of morphisms `φ i : A ⟶ B` of module sheaves on `Y` and opens `U i`,
`RangeOnMem (φ i) (U i) V σ` says that the restriction of `σ ∈ Γ(B, V)` to `V ⊓ U i` lies in
the image of `(φ i).app (V ⊓ U i)`. The lemmas `RangeOnMem.add`, `.zero`, `.smul`, `.map`
show that these sections form a sub-presheaf of modules `rangeOnSubmodule φ U`
(membership: `RangeOnMem` for every `i`). If every `(φ i).app V` with `V ≤ U i` is injective,
`RangeOnMem.of_cover` shows that membership is local: the local preimages agree on overlaps
by injectivity, glue in the sheaf `A`, and the glued section maps to `σ` because `B` is
separated. Hence `rangeOn φ U hφ` is a `SheafOfModules.Submodule` of `B`.
`RangeOnMem.of_app_eq` and `RangeOnMem.exists_app_eq` produce and use membership.

## Main theorem `exists_lineBundle_of_descent`

Let `π : Y' ⟶ Y` be injective on sections over every open of `Y` and surjective on points,
`F` a module sheaf on `Y'`, `U i` an open cover of `Y` and `t i` global sections of `F` with
`trivializationOpen F (t i) = π⁻¹(U i)`. Assume that for all `k, i` there is
`a ∈ Γ(Y, U i)` with `t k|_{π⁻¹ U i} = π^#(a) • t i|_{π⁻¹ U i}`. Then there is a line bundle
`M` on `Y` with global sections `s k` such that `trivializationOpen M (s k) = U k` exactly.

Construction. Let `P = π_* F` and `ψ i = sectionHom P (t i) : 𝒪_Y ⟶ P`. Since `t i`
trivializes `F` on `π⁻¹(U i)`, `(ψ i).app V` is `a ↦ π^#(a) • t i|` composed with a bijection,
so it is injective for `V ≤ U i`. Put `M = (rangeOn ψ U).toSheafOfModules`, a subsheaf of `P`.
The transition hypothesis says that every `t k`, as a global section of `P`, lies in `M`;
these are the sections `s k`.

Trivialization on `U k`. The composite of `sectionHom M (s k)` with the inclusion `M ⟶ P` is
`ψ k` (`sectionHom_naturality`). On `V ≤ U k` the map `(sectionHom M (s k)).app V` is injective
because `ψ k` is, and surjective because a section of `M` over `V ≤ U k` lies in the image of
`ψ k` by the membership condition with index `k`. By `trivializesOn_iff_bijective`, `s k`
trivializes `M` on `U k`. Since the `U k` cover `Y`, `M` is locally free of rank one.

Exact locus. If `s k` trivializes `M` on `W = trivializationOpen M (s k)`, take `x ∈ W` and
`i` with `x ∈ U i`, and `V = W ⊓ U i`. Bijectivity on `V` gives `b ∈ Γ(Y, V)` with
`s i|_V = b • s k|_V`, hence `t i = π^#(b) • t k` on `π⁻¹ V`. With the transition
`t k = c • t i` (`c` the restriction of `π^#(a)`), injectivity of the section map of `t i` on
`π⁻¹ V` gives `π^#(b) * c = 1`, so `c` is a unit and `t k` trivializes `F` on `π⁻¹ V`.
Thus `π⁻¹ V ≤ trivializationOpen F (t k) = π⁻¹(U k)`, and surjectivity of `π` gives
`x ∈ U k`. So `W ≤ U k`; the reverse inclusion is the maximality of the locus. No cocycle
condition on the transition functions is needed, because `M` is defined inside `π_* F`.
