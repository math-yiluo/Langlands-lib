# Transport of tensor homology presheaves along homotopy equivalences

Let `R : CommRingCat.{u}` and let `K, L` be integer cochain complexes of
`R`-modules. For a scheme test `T` over `Spec R`, the presheaf
`TensorSections.homologyPresheaf K n` takes the value
`Hⁿ(Γ(T,𝒪_T) ⊗[R] K)`, lifted to `Type (u+1)` (see
`TensorSectionsHomology`).

- `TensorSections.tensorComplexMap φ` is the natural transformation
  `tensorComplex K ⟶ tensorComplex L` induced by a map of complexes
  `φ : K ⟶ L`. Its component at a coefficient module `A` is
  `(tensorLeft A).mapHomologicalComplex` applied to `φ`. Naturality in `A`
  is the whisker-exchange law of the monoidal category of `R`-modules.
- `TensorSections.homologyPresheafMap φ n` whiskers this transformation with
  `sectionModules` on the left and with the degree `n` homology functor,
  the forgetful functor and the universe lift on the right. This gives a
  map of presheaves `homologyPresheaf K n ⟶ homologyPresheaf L n` on the
  whole slice over `Spec R`.
- `TensorSections.homologyPresheafIsoOfHomotopyEquiv h n` is the natural
  isomorphism `homologyPresheaf K n ≅ homologyPresheaf L n` attached to a
  homotopy equivalence `h : HomotopyEquiv K L`. For each test `T`, its
  component is Mathlib's `HomotopyEquiv.toHomologyIso` for the homotopy
  equivalence `(tensorLeft Γ(T,𝒪_T)).mapHomotopyEquiv h`. The additive
  functor `tensorLeft` preserves homotopies, so this is a homotopy
  equivalence. The forward map of this isomorphism is the homology map of
  `h.hom`. Naturality is therefore the naturality of
  `homologyPresheafMap h.hom n`.

This is an internal construction from Mathlib's homotopy and homology APIs.
It assumes nothing about `R`, `K` or `L` beyond the homotopy equivalence.
It is used to transport the degree-zero homology presheaf of a perfect
complex to that of a homotopy equivalent finite free model.
