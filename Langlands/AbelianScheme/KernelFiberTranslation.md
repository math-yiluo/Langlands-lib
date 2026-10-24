# Kernel identification for split fibres

For an arbitrary universe `u`, scheme `S : Scheme.{u}`, group objects `G H : Grp (Over S)`, group-scheme homomorphism `f : G ⟶ H`, and section `x : 𝟙_ (Over S) ⟶ G.X`, this module constructs

```text
Langlands.GroupScheme.kernelFiberIso f x :
  (Langlands.GroupScheme.kernel f).X ≅
    CategoryTheory.Limits.pullback f.hom.hom (x ≫ f.hom.hom).
```

This is an actual isomorphism in `Over S`. Applying `(Over.forget S).mapIso` gives an isomorphism of the underlying schemes. No commutativity, field-base, finiteness, smoothness, properness, or surjectivity hypothesis is used. The section `x` is supplied as data: the construction makes no claim that an arbitrary target section lifts, or that an arbitrary fibre has a point over its original residue field. Translation is generally not a group homomorphism, and the resulting isomorphism is asserted in `Over S`.

## Original source and derived scope

The motivating source is J. S. Milne, *Abelian Varieties* (1986 article, author revision January 2, 2022), proof of Proposition 8.1, printed/PDF page 12. Its isogeny argument identifies scheme-theoretic fibres with the kernel after the relevant field extension by translation. The opening of section 20, printed/PDF page 42, supplies the group-scheme context for abelian schemes. Both pages were read in the retained original `literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`, registered as `milne-abelian-varieties-1986-author-2022`, SHA256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`. No source-specific errata note was present in the available project or Library notes.

The arbitrary-base split-fibre construction here is derived from group-object axioms and pullback universal properties; it is not a verbatim formalization of Milne's proposition or a proof of its equivalent isogeny criteria. The supplied source section is exactly the datum needed for translation to make sense over the chosen base. For consumers extending the base field, the existing [KernelBaseChange](KernelBaseChange.md) construction remains the base-change interface; this module introduces no replacement for it.

## Construction and proof

The module imports the published [Kernel](Kernel.md) construction. It uses `(kernelι f).hom.hom` as the kernel inclusion and `kernel_isPullback f` as its pullback universal property. All group operations on test-object morphisms come from Mathlib's actual group-object structure.

Mathlib already provides the isomorphism `GrpObj.mulRight x : G.X ≅ G.X`. This module reuses it. For any test scheme `T : Over S` and morphism `a : T ⟶ G.X`, the two private calculation lemmas express its maps as

```text
a ≫ (GrpObj.mulRight x).hom = a * (toUnit T ≫ x),
a ≫ (GrpObj.mulRight x).inv = a * (toUnit T ≫ x)⁻¹.
```

The private forward map is the pullback lift of the translated kernel inclusion and the terminal morphism. Its compatibility equation follows because the kernel inclusion maps to the identity, and postcomposition with `f.hom.hom` preserves multiplication. The private inverse is the lift into the kernel of the fibre's first projection followed by inverse translation. The fibre equation identifies the image of its first projection with the image of the supplied section; multiplication by the inverse then gives the identity. Uniqueness of maps to the terminal object identifies the second projections.

To prove the forward map followed by the inverse is the identity, the implementation composes with the monomorphic kernel inclusion. The two lift-projection formulas reduce the result to `GrpObj.mulRight x` followed by its inverse. The other composite is checked on both pullback projections: the first reduces to inverse translation followed by translation, and the second follows from terminal uniqueness. These are proofs of inverse laws for morphisms, not merely bijections on a chosen set of points.

## Public projection and structure formulas

All public names are in `Langlands.GroupScheme`. The following lemmas have simp and reassociation attributes:

- `kernelFiberIso_hom_fst` identifies the forward map followed by `pullback.fst` with `(kernelι f).hom.hom ≫ (GrpObj.mulRight x).hom`.
- `kernelFiberIso_hom_snd` identifies the forward map followed by `pullback.snd` with `toUnit (kernel f).X`.
- `kernelFiberIso_inv_ι` identifies the inverse followed by `(kernelι f).hom.hom` with `pullback.fst f.hom.hom (x ≫ f.hom.hom) ≫ (GrpObj.mulRight x).inv`.
- `kernelFiberIso_hom_structure` states that the underlying forward scheme map followed by the split fibre's structure morphism is `(kernel f).X.hom`.
- `kernelFiberIso_inv_structure` states that the underlying inverse scheme map followed by `(kernel f).X.hom` is the split fibre's structure morphism.

The last two identities are the defining over-category morphism laws. In particular, `kernelFiberIso_inv_structure` gives the factorization of the fibre structure morphism through the kernel structure morphism by a scheme isomorphism. This is the interface for downstream transport of finiteness. The module itself imposes no finiteness assumption and asserts no finite-kernel-to-quasi-finite theorem.
