# Morphisms of schemes from natural maps on affine points

Author: Worker 1399. Internal helper module for the proof of
`Langlands.GroupScheme.GeneralLinearSolvableStabilizerStatement`; it has no literature source.
It is the standard fact that a scheme is the colimit of its affine points ("functor of points
on affine schemes"). Mathlib has no such Yoneda statement for `Scheme`, so the module glues
the morphism by hand along `X.affineCover`.

Namespace `Langlands.AlgebraicGeometry.AffinePoints`, universe `u`.

## Absolute version

- `hom_ext`: two morphisms `f g : X ⟶ Y` with `t ≫ f = t ≫ g` for every
  `t : Spec A ⟶ X` (`A : CommRingCat.{u}`) are equal. Proof: `Scheme.Cover.hom_ext` for the
  affine cover of `X`, whose members are such affine points.
- `comp_eq_of_natural`: let `F A : (Spec A ⟶ X) → (Spec A ⟶ Y)` be natural along ring maps,
  `F B (Spec.map φ ≫ t) = Spec.map φ ≫ F A t`. Then `s ≫ F A t = F B (s ≫ t)` for every
  morphism `s : Spec B ⟶ Spec A`, because `s = Spec.map (Spec.preimage s)`.
- `exists_hom`: such a natural family `F` comes from a morphism: there is `f : X ⟶ Y` with
  `t ≫ f = F A t` for every affine point `t`. Proof: put `g i := F _ (X.affineCover.f i)`.
  The gluing condition on `pullback (f i) (f j)` is checked on affine points by `hom_ext`;
  both sides reduce to `F` of the same affine point by `comp_eq_of_natural` and
  `pullback.condition`. `glueMorphisms` gives `f`. For an arbitrary affine point `t`, the
  equation `t ≫ f = F A t` is checked on the cover of `Spec A` pulled back from the affine
  cover of `X` (`pullback₁ t`), and on affine points `s` of its members. There both sides
  again reduce to `F` of the same point, through `ι_glueMorphisms` and `comp_eq_of_natural`.
  The proof is written with term-mode `Eq.trans` chains, since rewriting with cover indices
  produced motive errors.

## Version over `Spec R` (section `Over`)

Here `R : Type u` is a commutative ring and points are indexed by `R`-algebras.

- `specOver A`: the affine scheme of an `R`-algebra `A` as an object of
  `Over (Spec R)`, with structure map `Spec.map (algebraMap R A)`.
- `specMapOver φ`: the morphism `specOver B ⟶ specOver A` induced by `φ : A →ₐ[R] B`,
  with `specMapOver_left` (its underlying morphism is `Spec.map φ`).
- `algebraOfHom s`: the `R`-algebra structure on `A` induced by `s : Spec A ⟶ Spec R`, and
  `specMap_algebraMap_algebraOfHom` (it induces `s` back).
- `algebra_ext_of_specMap`: two `R`-algebra structures on `A` inducing the same morphism to
  `Spec R` are equal (by `Spec.map_injective`).
- `algHomOfSpec φ h`: a ring map `φ : A →+* B` compatible with the structure morphisms to
  `Spec R` is an `R`-algebra map; `algHomOfSpec_toRingHom` records that its ring map is `φ`.
- `pointOfHom t`: an affine point `t : Spec A ⟶ T.left` of `T : Over (Spec R)` as a morphism
  `specOver A ⟶ T` for the induced algebra structure; `pointOfHom_left`.
- `over_hom_ext`: two morphisms over `Spec R` agreeing on all points `specOver A ⟶ X`
  (all `R`-algebras `A`) are equal. Proof: reduce to `hom_ext` using `pointOfHom`.
- `F_left_congr`: a technical transport lemma. The underlying morphism of `F A x` does not
  change when the algebra structure on `A` is replaced by an equal one and `x` by a point with
  the same underlying morphism.
- `exists_over_hom`: a family
  `F A : (specOver A ⟶ X) → (specOver A ⟶ Y)`, natural for `R`-algebra maps
  (`F B (specMapOver φ ≫ x) = specMapOver φ ≫ F A x`), comes from a morphism `f : X ⟶ Y`
  over `Spec R` with `x ≫ f = F A x` for all `x`. Proof: define the absolute family
  `F' A t := (F A (pointOfHom t)).left` with the induced algebra structure. It is natural
  because `pointOfHom (Spec.map φ ≫ t) = specMapOver ψ ≫ pointOfHom t` for the algebra
  map `ψ := algHomOfSpec φ`. `exists_hom` gives `f`. It lies over `Spec R` (checked on
  affine points with `Over.w`). For a point `x` with a given algebra structure, the induced
  structure `algebraOfHom (x.left ≫ X.hom)` equals the given one by
  `algebra_ext_of_specMap`, and `F_left_congr` finishes.

These lemmas are used in `Langlands.GroupScheme.GeneralLinearActionOfPoints` to build the
action morphism of `GL_N` on the flag scheme from its action on points.
