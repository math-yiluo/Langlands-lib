# Gluing actual module sheaves over an arbitrary scheme open cover

The proposition
`Langlands.Scheme.Modules.OpenCoverModuleGluingStatement.{u}` says that sheaves
of modules can be glued along an open cover. Take a module sheaf on each member
of an arbitrary open cover of a scheme, and isomorphisms between their pullbacks
to the pairwise overlaps that satisfy the cocycle condition on the triple
overlaps. Then these data glue to a module sheaf on the whole scheme. The
proposition uses the actual category `AlgebraicGeometry.Scheme.Modules`, its
actual pullback functors and actual scheme fiber products.

## Statement

Let `X : Scheme.{u}` and let `𝒰 : X.OpenCover.{u}`. Write `uᵢ : Uᵢ ⟶ X` for
`𝒰.f i`, where `Uᵢ` is `𝒰.X i`. The index type of the cover is arbitrary in
universe `u`. The cover maps are open immersions whose ranges cover `X`.
Below, `g*` denotes `AlgebraicGeometry.Scheme.Modules.pullback g`, on both
objects and morphisms.

The data are:

- for each index `i`, a sheaf of modules `Mᵢ : Uᵢ.Modules` over the structure
  sheaf of `Uᵢ`;
- for each ordered pair `i,j`, an isomorphism

  ```text
  φᵢⱼ : p₁* Mᵢ ≅ p₂* Mⱼ
  ```

  of module sheaves on `Pᵢⱼ := Uᵢ ×[X] Uⱼ`. Here `p₁ = pullback.fst uᵢ uⱼ` and
  `p₂ = pullback.snd uᵢ uⱼ`. The pairs are ordered and include `i = j`.

### Cocycle hypothesis

For indices `i,j,k`, the triple overlap is the actual fiber product

```text
W := Pᵢⱼ ×[Uᵢ] Pᵢₖ = pullback (pullback.fst uᵢ uⱼ) (pullback.fst uᵢ uₖ),
```

with projections `t₁ : W ⟶ Pᵢⱼ` and `t₂ : W ⟶ Pᵢₖ`. The map `q : W ⟶ Pⱼₖ` is
`pullback.lift (t₁ ≫ pullback.snd uᵢ uⱼ) (t₂ ≫ pullback.snd uᵢ uₖ)`. Its
well-definedness proof comes from the two `pullback.condition`s and the
defining equation of `W`. The three maps relate the three overlaps by
commutative squares:

```text
t₁ ≫ pullback.fst uᵢ uⱼ = t₂ ≫ pullback.fst uᵢ uₖ   (pullback.condition),
t₁ ≫ pullback.snd uᵢ uⱼ = q ≫ pullback.fst uⱼ uₖ    ((pullback.lift_fst _ _ _).symm),
q ≫ pullback.snd uⱼ uₖ = t₂ ≫ pullback.snd uᵢ uₖ    (pullback.lift_snd _ _ _).
```

The published [`squarePullbackIso`](SquarePullbackComparison.md),
`squarePullbackIso p p' s t hs A : p'* (t* A) ≅ s* (p* A)` for
`hs : p' ≫ t = s ≫ p`, turns each square into a comparison of iterated
pullbacks:

```text
β₀ := squarePullbackIso (pullback.fst uᵢ uₖ) t₁ t₂ (pullback.fst uᵢ uⱼ)
        pullback.condition Mᵢ
   : t₁* (fstᵢⱼ* Mᵢ) ≅ t₂* (fstᵢₖ* Mᵢ),
β₁ := squarePullbackIso (pullback.fst uⱼ uₖ) t₁ q (pullback.snd uᵢ uⱼ)
        (pullback.lift_fst _ _ _).symm Mⱼ
   : t₁* (sndᵢⱼ* Mⱼ) ≅ q* (fstⱼₖ* Mⱼ),
β₂ := squarePullbackIso (pullback.snd uᵢ uₖ) q t₂ (pullback.snd uⱼ uₖ)
        (pullback.lift_snd _ _ _) Mₖ
   : q* (sndⱼₖ* Mₖ) ≅ t₂* (sndᵢₖ* Mₖ).
```

The hypothesis requires, for every triple `i,j,k`,

```text
t₁*(φᵢⱼ.hom) ≫ β₁.hom ≫ q*(φⱼₖ.hom) ≫ β₂.hom = β₀.hom ≫ t₂*(φᵢₖ.hom).
```

Both sides are morphisms from `t₁* (fstᵢⱼ* Mᵢ)` to `t₂* (sndᵢₖ* Mₖ)`. Thus the
hypothesis says that `φᵢₖ` equals the composite of `φᵢⱼ` and `φⱼₖ` on the
triple overlap, modulo the canonical comparisons between iterated pullbacks.
The statement does not require `φᵢᵢ` to be the identity. For an open cover,
that would follow from the cocycle condition with `i = j = k` (see the
comment noted under Source). This file does not state or prove that
consequence.

### Conclusion

There exist a module sheaf `N : X.Modules` and, for each index `i`, an
isomorphism

```text
ψᵢ : uᵢ* N ≅ Mᵢ
```

such that for every ordered pair `i,j`

```text
p₁*(ψᵢ.hom) ≫ φᵢⱼ.hom = α_N.hom ≫ p₂*(ψⱼ.hom),
α_N := squarePullbackIso uⱼ p₁ p₂ uᵢ pullback.condition N
     : p₁* (uᵢ* N) ≅ p₂* (uⱼ* N).
```

Both sides are morphisms from `p₁* (uᵢ* N)` to `p₂* Mⱼ`. So the overlap
isomorphism `φᵢⱼ` is the one induced by `ψᵢ` and `ψⱼ` under the canonical
comparison of the two pullbacks of `N` to `Pᵢⱼ`.

The conclusion asserts existence only. It states no uniqueness of `N`, no
functoriality of the construction, and no equivalence between module sheaves
on `X` and glueing data.

## Scope

The proposition quantifies over every scheme in universe `u` and every open
cover of it in universe `u`. It imposes no reducedness, quasi-separatedness,
quasi-compactness, affineness or finiteness condition. The local module
sheaves need not be quasi-coherent, locally free, finitely presented or of
any specified rank. In particular, the proposition makes no claim that the
glued sheaf is invertible or locally free; such properties are not part of
the conclusion. The definition is a Prop-valued `def`; this file supplies the
proposition to be proved, not a proof of it.

## Internal provenance

The mathematical content is Stacks Lemmas 6.33.2 and 6.33.3, cited below:
glueing data of sheaves of `𝒪`-modules on an open cover glue to a sheaf of
`𝒪`-modules. The Lean form is an internal reformulation of that lemma. It
differs from the source in three ways, which do not change the content.

- Stacks restricts sheaves to the open subsets `Uᵢ ∩ Uⱼ` and
  `Uᵢ ∩ Uⱼ ∩ Uₖ` of `X`. The Lean form uses the cover members `uᵢ : Uᵢ ⟶ X`,
  the fiber products `Uᵢ ×[X] Uⱼ` and the triple fiber product `W`, and pulls
  back along open immersions. Pulling back along an open immersion corresponds
  to restriction to its image. The overlap fiber products correspond to
  intersections of images.
- Stacks writes the cocycle condition as `φᵢₖ = φⱼₖ ∘ φᵢⱼ` and the
  compatibility as `φᵢⱼ ∘ φᵢ = φⱼ` on restrictions. Restrictions of
  restrictions are equal on the nose there. In the Lean form, iterated
  pullbacks along different but equal composites are only canonically
  isomorphic. The comparisons `β₀`, `β₁`, `β₂` and `α_N` above are these
  canonical isomorphisms, all given by `squarePullbackIso`.
- The Lean form names the triple overlap as the specific fiber product
  `pullback (pullback.fst uᵢ uⱼ) (pullback.fst uᵢ uₖ)` and the map `q` to
  `Pⱼₖ`. Mathlib defines no separate triple-intersection object for open
  covers. Its glue data of an open cover,
  `AlgebraicGeometry.Scheme.Cover.gluedCover`, uses the same fiber product as
  triple overlap (the domain of `Scheme.Cover.gluedCoverT'`).

The comparisons in the hypothesis and conclusion follow the same convention as
the published
[`OpenCoverHomGluingStatement`](OpenCoverHomGluingStatement.md), which glues
morphisms between two fixed global module sheaves along the same kind of cover.
Together, the two statements form the object and morphism parts of the
gluing of module sheaves along an open cover (Stacks Lemma 6.33.4, which this
file does not formulate).

Worker 281 wrote the Lean interface for the proof that Zariski-local actual
rigidified abelian-scheme classes glue
(`Langlands.AbelianScheme.RigidifiedClassesZariskiGluingStatement`). Worker 303
drafted an equivalent form independently, and the two were merged into this
text. This module isolates the general object-gluing prerequisite. The
consumer's final proof assembly is separate.

## Source

- `stacks-glueing-sheaves-00AK-2026-10-31`, folder SHA256
  `ad47acf5d196d42f013f4deb43d78b288cc8bba3a649626bdd5d94169b375c03`, retained
  file `00AK.html` (SHA256
  `347ecf70bb9879c764862d6c23fe8bb1cf0cee1f06134c8773d7840649c3867c`),
  Stacks Project, Sheaves on Spaces, Section 6.33 (tag 00AK), Glueing sheaves.
  - Before Lemma 6.33.2, the section defines glueing data `(𝓕ᵢ, φᵢⱼ)` for
    sheaves of sets on an open covering `X = ⋃ Uᵢ`. These are isomorphisms
    `φᵢⱼ : 𝓕ᵢ|_{Uᵢ ∩ Uⱼ} → 𝓕ⱼ|_{Uᵢ ∩ Uⱼ}` with `φᵢₖ = φⱼₖ ∘ φᵢⱼ` on
    `Uᵢ ∩ Uⱼ ∩ Uₖ`.
  - Lemma 6.33.2 gives a sheaf `𝓕` with isomorphisms
    `φᵢ : 𝓕|_{Uᵢ} → 𝓕ᵢ` such that `φᵢⱼ ∘ φᵢ = φⱼ` on `Uᵢ ∩ Uⱼ`. Its first
    proof takes sections over `W` to be the compatible families in
    `∏ᵢ 𝓕ᵢ(W ∩ Uᵢ)`.
  - Lemma 6.33.3 says that the same construction gives a sheaf of
    `𝒪`-modules when the glueing data consist of sheaves of `𝒪`-modules, for
    any sheaf of rings `𝒪` on `X`. This is the source of the present
    proposition, applied to `𝒪 = 𝒪_X`.
  - Comment #7767 asks whether `φᵢᵢ = id` should be part of the definition.
    Comment #7768 (Johan) answers that it follows from the cocycle condition
    with `i = j = k`.

  The cited section does not state the pullback-based, fiber-product
  formulation used here. That formulation is derived internally, as explained
  above.
