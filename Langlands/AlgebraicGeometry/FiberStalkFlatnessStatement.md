# Flatness of a residue-field fibre map in terms of stalks

`Langlands.AlgebraicGeometry.FiberStalkFlatnessStatement` is a
proposition-valued definition in
`Langlands.AlgebraicGeometry.FiberStalkFlatnessStatement`. It is an internal,
derived interface. It isolates the step in the first proof paragraph of Stacks
Project Theorem 37.16.2 (tag [039C](https://stacks.math.columbia.edu/tag/039C))
that turns flatness of a scheme-theoretic fibre morphism into flatness of a
ring base change of stalks, applied to the structure sheaf `𝓕 = 𝒪_X`.

## Statement

Let `S : Scheme.{u}`, `X Y : Over S`, `f : X ⟶ Y` a morphism of `S`-schemes,
and `x : X.left` a point. Set

- `y = f.left x`, a point of `Y.left`;
- `s = Y.hom y`, a point of `S`;
- `R = S.presheaf.stalk s`, the local ring `𝒪_{S,s}`;
- `A = Y.left.presheaf.stalk y`, the local ring `𝒪_{Y,y}`;
- `B = X.left.presheaf.stalk x`, the local ring `𝒪_{X,x}`;
- `k = IsLocalRing.ResidueField R`, the residue field `κ(s) = R/𝔪_s`;
- `F = A ⊗[R] k`.

If the morphism `((Over.pullback (S.fromSpecResidueField s)).map f).left` is
`Flat`, then `F ⊗[A] B` is a flat `F`-module, that is,
`Module.Flat F (F ⊗[A] B)`.

All objects are Mathlib's: `AlgebraicGeometry.Scheme`, `Over`, the structure
presheaf stalks, `Scheme.Hom.stalkMap`, `IsLocalRing.ResidueField`,
`Scheme.fromSpecResidueField`, `Over.pullback`, the scheme-morphism class
`AlgebraicGeometry.Flat`, `TensorProduct` and `Module.Flat`. The local
definitions in the Lean statement are `let` bindings that abbreviate these
actual objects; none of them is a free parameter.

## Algebra and module structures

The statement uses the actual stalk maps, written explicitly with
`RingHom.toAlgebra`:

- `R` acts on `A` through `(Y.hom.stalkMap y).hom : 𝒪_{S,s} →+* 𝒪_{Y,y}`, the
  stalk map at `y` of the structure morphism `Y.hom : Y.left ⟶ S`. Its source
  is the stalk of `S` at `Y.hom y = s`, so no transport is needed.
- `A` acts on `B` through `(f.left.stalkMap x).hom : 𝒪_{Y,y} →+* 𝒪_{X,x}`, the
  stalk map at `x` of `f.left`, whose source is the stalk of `Y.left` at
  `f.left x = y`.
- `R` acts on `B` through the composite ring map
  `(f.left.stalkMap x).hom.comp (Y.hom.stalkMap y).hom`, so the algebra map
  `R → B` is literally the composite of the two stalk maps `R → A → B`. This
  structure records the tower `𝒪_{S,s} → 𝒪_{Y,y} → 𝒪_{X,x}` of the source; the
  conclusion itself only uses the `A`-module structure of `B`.
- `k = R/𝔪_R` is an `R`-algebra by the quotient map (Mathlib's instance on
  `IsLocalRing.ResidueField`). It is `κ(s)`: Mathlib defines
  `S.residueField s` as the residue field of `S.presheaf.stalk s`, and
  `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is built from it.
- `F = A ⊗[R] k` is the tensor product ring. It is an `A`-algebra through
  `a ↦ a ⊗ 1`, i.e. `a • (a' ⊗ c) = (a a') ⊗ c`, Mathlib's
  `Algebra.TensorProduct.leftAlgebra`. Mathematically `F ≅ A/𝔪_s A`, the ring
  written `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` in the source.
- `F ⊗[A] B` is the tensor product over `A` of the `A`-modules `F` and `B`,
  with `F` acting on the left factor: `c • (c' ⊗ b) = (c c') ⊗ b`. This is the
  base change of `B` along `A → F`. As an `F`-module it is
  `(A ⊗_R k) ⊗_A B ≅ B ⊗_R k ≅ B/𝔪_s B`, the module written
  `𝒪_{X,x}/𝔪_s 𝒪_{X,x}` in the source, with its module structure over
  `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}`. These isomorphisms explain the meaning of the
  conclusion; they are not part of the Lean statement.

## The fibre morphism and the point `s`

`S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism.
`Over.pullback (S.fromSpecResidueField s) : Over S ⥤ Over (Spec κ(s))` is the
actual categorical base change: it sends `X` to `X_s = X ×_S Spec κ(s)` and
`f` to the induced morphism `f_s : X_s ⟶ Y_s`, whose `.left` is the scheme
morphism `f_s` of Stacks Section 37.16. The hypothesis is flatness of this
whole scheme morphism, the form in which the parent proof (below) has it.

The point `s` is defined as `Y.hom (f.left x)`. The image of `x` in `S`,
`X.hom x`, equals it by `Over.w f : f.left ≫ Y.hom = X.hom`; this equality is
a consequence of the data and is not a hypothesis of the statement. A
consumer holding flatness of the fibre over `X.hom x` rewrites it with that
equality before applying the statement; a private development check confirmed
that this transport works.

## Mathematical content and provenance

Write `x'` for the point of `X_s` over `x` and `y'` for the point of `Y_s` over
`y`. The source asserts that the local ring of `Y_s` at `y` is
`𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` and, for `𝓕 = 𝒪_X`, that the stalk of `𝒪_{X_s}` at `x`
is `𝒪_{X,x}/𝔪_s 𝒪_{X,x}`. With these identifications, compatible with the
stalk map of `f_s` at `x'`, flatness of `f_s` at `x'` is flatness of
`B/𝔪_s B` over `A/𝔪_s A`, which is the conclusion. The proposition therefore
asserts the "only if" direction of that equivalence, from global flatness of
`f_s`.

Provenance. The retained Stacks page `039C.html` (Theorem 37.16.2) states, in
the first paragraph of its proof: "Consider the ring maps
`𝒪_{S,s} → 𝒪_{Y,y} → 𝒪_{X,x}` and the module `𝓕_x`. The stalk of `𝓕_s` at
`x` is the module `𝓕_x/𝔪_s 𝓕_x` and the local ring of `Y_s` at `y` is
`𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}`. Thus the implication (1) ⇒ (2) is Algebra, Lemma
10.128.9." The present proposition is that identification step, specialised to
`𝓕 = 𝒪_X` and phrased as an implication between the flatness conditions. Stacks
does not state it as a separate lemma, so this is a derived statement; the
theorem's finite-presentation hypotheses are not used by this step and are
omitted.

The retained page `01K1.html` (Lemma 26.18.5) says that
`X_s → X` and `Spec(𝒪_{S,s}) ×_S X → X` induce fibre squares of topological
spaces, the top arrows being homeomorphisms onto their images. It supplies
only the underlying topology of the fibre, for example the unique point `x'`
of `X_s` over `x`; it says nothing about local rings and does not by itself
prove the ring statement.

## Scope

The schemes `S`, `X`, `Y` and the point `x` are arbitrary, all in
`Scheme.{u}`. There is no finite presentation, finite type, flatness of
`X → S`, noetherian, affine, quasi-compactness or nonemptiness hypothesis. The
fibre is the actual scheme-theoretic base change, not an arbitrary family, and
no isomorphism of stalks is assumed in the data. The statement does not assert
the identification of the local rings of the fibres, flatness of `f_s` at a
single point, or the converse direction.

## Intended application

The proof task `bd62242a-a240-4c31-a976-42e83d95485b` for the published
`Langlands.AlgebraicGeometry.FiberwiseFlatnessStatement` (Stacks Lemma 37.16.4)
follows the 039C route: it applies Stacks Algebra Lemma 10.128.9 (tag 05UV,
stated by task `9a978548-8ac6-4c7c-b3bf-40faac6282b8`) to
`R = 𝒪_{S,s}`, `A = 𝒪_{Y,y}`, `B = M = 𝒪_{X,x}`. That lemma's fibre
hypothesis is
`Module.Flat (A ⊗[R] IsLocalRing.ResidueField R) ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] B)`,
which is the conclusion here. A private development check confirmed that this
proposition yields the `hfiber` hypothesis of the parent's shared assembly
draft by `fun S X Y f x => h S X Y f x`; that check is not part of this
artifact.

## Status

This file states the bridge only. It is not proved here and is not installed
as an axiom, instance or structure field; its proof is a separate exact-target
task. In the pinned Mathlib, `Mathlib/AlgebraicGeometry/Fiber.lean` provides
`Scheme.Hom.fiber`, `fiberι`, `fiberHomeo` and `asFiber` but no stalk
comparison, and `Spec.fiberToSpecResidueFieldIso` identifies only the
structure morphism of the fibre of an affine morphism.

## Sources

- `stacks-algebra-flatness-criteria-2026-10-22`, folder SHA256
  `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`:
  `039C.html`, Theorem 37.16.2, first proof paragraph (the stalk
  identifications).
- `stacks-fiberwise-isogeny-2026-10-22`, folder SHA256
  `db82f1556e926672cc2278329e279f7fcaceb540c23e323a7c266a6a6b1f0dca`:
  `01K1.html`, Lemma 26.18.5 (topology of the fibre only).
