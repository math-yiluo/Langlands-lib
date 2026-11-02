# Equal fppf Picard classes of two actual line bundles form an immersion locus

Author: Worker 766.

## Statement

`Langlands.AlgebraicGeometry.Picard.FieldPicardClassEqualizerImmersionStatement.{u}`
is the proposition

```lean
∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))), IsProper X.hom →
  ∀ (T : Over (Spec (CommRingCat.of k)))
    (L M : LineBundle ((relativeSpace X.hom).obj T)),
    ∃ (Z : Over (Spec (CommRingCat.of k))) (ι : Z ⟶ T), IsImmersion ι.left ∧
      AlgebraicSpace.RepresentsEqualizer (F := RelativePicard.classSheafPresheaf X.hom) ι
        (RelativePicard.sheafClassOf X.hom T L) (RelativePicard.sheafClassOf X.hom T M)
```

The file defines this proposition only. It proves nothing.

## Meaning

Write `S = Spec (CommRingCat.of k)` and `F = RelativePicard.classSheafPresheaf X.hom`.
`F` is the presheaf underlying the Library's actual fppf Picard class sheaf
`RelativePicard.classSheaf X.hom`, valued in `Type (u+1)` on `Over S`.

- `k : Type u` is an arbitrary field, and `X` is an arbitrary scheme over `S` with
  `IsProper X.hom`. No other hypothesis on `X` is made. In particular `X` need not be
  reduced, connected, geometrically integral or projective, and
  `H⁰(X, O_X) = k` is not assumed.
- `T` is an arbitrary scheme over `S`. `(relativeSpace X.hom).obj T` is the Library's
  fibre product `T ×_S X`, the source of the second projection to `X`.
- `L` and `M` are actual line bundles on `T ×_S X`, that is, objects of the Library's
  `LineBundle`: sheaves of modules that are locally free of rank one.
- `RelativePicard.sheafClassOf X.hom T L` is the image of the isomorphism class of `L`
  in the sheafified presheaf `F` at `T`.
- The conclusion gives a scheme `Z` over `S` and a morphism `ι : Z ⟶ T` over `S`. Its
  underlying morphism of schemes `ι.left` is an immersion in Mathlib's sense
  `IsImmersion`: a locally closed topological embedding with surjective stalk maps.
  By Mathlib's `isImmersion_iff_exists`, this is a closed immersion followed by an
  open immersion.
- `AlgebraicSpace.RepresentsEqualizer` is the Library definition in
  `Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer`. Here it says: for
  every scheme `T'` over `S` and every morphism `g : T' ⟶ T` over `S`, some
  `z : T' ⟶ Z` over `S` satisfies `z ≫ ι = g` if and only if
  `F.map g.op (sheafClassOf X.hom T L) = F.map g.op (sheafClassOf X.hom T M)`.

By the Library lemma `RelativePicard.map_sheafClassOf`, the two sides of the last
equation are the fppf classes of the pullbacks of `L` and `M` along the induced
morphism `T' ×_S X ⟶ T ×_S X`. By the Library lemma
`RelativePicard.sheafClassOf_eq_iff_isomorphismSieve_mem`, these classes are equal
exactly when the two pullbacks become isomorphic on an fppf covering of `T'`. Thus `Z`
is the locus of test schemes over which `L` and `M` are fppf-locally isomorphic.

`RepresentsEqualizer` only asks for the existence of a factorization. Immersions of
schemes are monomorphisms (Mathlib's instance for `IsPreimmersion`), so the
factorization is unique here. Hence `ι` identifies the functor of points of `Z` with the
subfunctor of the functor of points of `T` on which the two classes agree.

## Role

This is the line-bundle case of the representability of the diagonal of `F` by
immersions. The Library theorems
`AlgebraicSpace.relative_diag_of_representsEqualizer` and
`AlgebraicSpace.relative_isImmersion_diag_of_representsEqualizer` reduce the latter to
equalizer loci of arbitrary pairs of sections of `F`. An arbitrary section of the
sheafification is only fppf-locally of the form `sheafClassOf`. Passing from the present
case to arbitrary sections therefore needs a separate fppf descent of immersion loci.
That step is not part of this unit. The closedness of the diagonal, which is the
separatedness conjunct of the Library's `FieldPicardSheafAlgebraicSpaceStatement`, is
also not claimed here.

## Provenance

This proposition is derived. It is not a numbered result of the literature.

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft, Chapter VI
§1. Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. Definition (6.1),
printed p.87 (PDF p.91), defines the relative Picard functor as the fppf sheaf
associated to `T ↦ Pic(X ×_S T)`. The Library's `RelativePicard.classSheaf` formalizes
this sheaf. Paragraph (6.3)(iii), printed p.89 (PDF p.93), states that for
`S = Spec(k)` and `X` proper over `k` this sheaf is representable by a scheme
`Pic_{X/k}` that is separated and locally of finite type over `k`; the source attributes
this to Murre.

The present proposition follows from (6.3)(iii) as follows. The two classes
`sheafClassOf X.hom T L` and `sheafClassOf X.hom T M` correspond to two morphisms
`T → Pic_{X/k}` over `k`. Their equalizer is the pullback of the diagonal of `Pic_{X/k}`,
which is a closed immersion because `Pic_{X/k}` is separated. So the literature gives a
closed immersion. The present proposition keeps only the weaker immersion form, which
is what the separate proof of the immersion part of the diagonal needs. This derivation
assumes the scheme theorem (6.3)(iii), the Library's
`FieldPicardSheafRepresentabilityStatement`, which is not an available proof. A proof of
the present proposition must not assume that theorem or the Library's
`FieldPicardSheafAlgebraicSpaceStatement`.

A direct argument for an immersion locus is Stacks Project, More on Morphisms,
Lemma 37.33.1 (tag 0BDP). Registered source:
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, SHA-256
`b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`, file
`more-morphisms.tex` at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, label
`lemma-diagonal-picard-flat-proper`, lines 9198–9214. For a flat proper morphism of
finite presentation `f : X → S` with `O_T → p_* O_{X_T}` an isomorphism for every base
change, and a finite locally free `E` on `X`, it gives an immersion of finite
presentation `Z → S` through which `g : T → S` factors exactly when `q^* E ≅ p^* N` for
some finite locally free `N` on `T`. That lemma does not cover the present scope:

- it assumes `O_T ≅ p_* O_{X_T}` universally, which fails for general proper `X` over `k`
  (for example when `H⁰(X, O_X) ≠ k`);
- its condition "`q^* E` comes from the base" differs from fppf-local isomorphism when
  that assumption fails. For `X = Spec k ⊔ Spec k`, every line bundle on `T ×_S X` is
  fppf-locally trivial over `T`, so here `Z = T`; but a line bundle given by two line
  bundles `N₁, N₂` on `T` is a pullback from `T` only when `N₁ ≅ N₂`.

So the cited lemma is a model for the method, not a source of the statement.
