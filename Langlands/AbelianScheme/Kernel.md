# Generic group-scheme kernels

For any scheme `S`, this module constructs kernels of homomorphisms between actual group objects `G H : Grp (Over S)`. No commutativity, field-base, finite-type, flatness, smoothness, or separatedness assumptions enter the construction. The instances for the cartesian monoidal structure on `Over S` are Mathlib's choices based on scheme fibre products.

## Source and scope

The original source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary chapters, Definition (3.13) and its following paragraph, printed pages 36–37, corresponding to PDF pages 40–41. The registered source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, in `literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`. These pages were read directly. No source-specific errata note was present in the available project notes.

Definition (3.13) defines the kernel by inverse image of the target unit section, displays its cartesian square, and identifies its test-scheme points with the kernel of the induced group map. The continuation on printed page 37 asserts closedness when the target is separated. Our construction realizes this definition using Mathlib's created limits. The naturality and commutativity proofs below are internal consequences of the universal property, not separately numbered results attributed to the source. This unit does not formalize the source's additional normal-subgroup assertion.

## Construction and interface

All declarations are in `Langlands.GroupScheme`.

- `kernelUnit H` is the target unit section, bundled as a group-object homomorphism from the trivial group scheme.
- `kernel f` is the pullback of `f` and `kernelUnit H` in `Grp (Over S)`. It is an actual group scheme with an induced group structure, obtained from Mathlib's existence and creation of limits for group objects.
- `kernelι f : kernel f ⟶ G` is the first pullback projection, hence a homomorphism of group schemes.
- `kernel_isPullback f` proves the underlying square in `Over S` has first projection `(kernelι f).hom.hom`, second projection the unique map to the unit object, and lower arrows `f.hom.hom` and the target unit. The forgetful functor creates and thus preserves the pullback; its second projection is identified with the unique terminal map.
- `kernel_isPullback_scheme f` applies `Over.forget S` to this square. It proves the square of actual scheme morphisms has vertices `(kernel f).X.left`, `G.X.left`, `S`, and `H.X.left`, with second projection `(kernel f).X.hom`. Thus the underlying scheme satisfies exactly the fibre-product property in the source, independently of the choice of a particular pullback representative.
- `kernelι_mono f` proves that the inclusion in `Over S` is a monomorphism, because it is a pullback of the unit morphism, which is a monomorphism from a terminal object.

## Points and naturality

For every test scheme `T : Over S`, `kernelPointsEquiv f T` is a multiplicative equivalence

```text
(T ⟶ (kernel f).X) ≃* (((yonedaGrp.map f).app (.op T)).hom.ker).
```

The target is the actual subgroup `MonoidHom.ker` of the map on points furnished by Mathlib's group-valued Yoneda functor. The forward function composes a point with the kernel inclusion. Its inverse is the unique pullback lift of a source point whose image is the identity, together with the terminal map from `T`. The pullback equation proves membership in the subgroup; uniqueness and the first-projection equation prove the inverse laws. Preservation of multiplication follows from the fact that the inclusion is a group-object homomorphism. `kernelPointsEquiv_val` records the forward function.

`kernelPointsRestrict f a` is the group homomorphism on these kernel subgroups induced by precomposition with any test-scheme map `a : T' ⟶ T`. Membership follows from the kernel equation and preservation of the identity by precomposition. `kernelPointsEquiv_naturality` proves the equality of subgroup elements

```text
kernelPointsEquiv f T' (a ≫ x) =
  kernelPointsRestrict f a (kernelPointsEquiv f T x).
```

Its proof is associativity of composition, followed by subtype extensionality. This quantifies over every map of test schemes, rather than only field-valued points.

## Commutativity and closedness

`kernel_isCommMonObj f` installs `IsCommMonObj (kernel f).X` under the sole additional assumption `IsCommMonObj G.X`. The proof uses the characterization of commutative monoid objects by commutativity on all test objects. Composing two products with the monomorphic inclusion reduces their equality to commutativity of the source's group of points. The target need not be commutative.

`kernelι_isClosedImmersion f` assumes `IsSeparated H.X.hom` and proves `IsClosedImmersion (kernelι f).hom.hom.left`. The target unit composed with its structure morphism is the identity of `S`; since the structure morphism is separated, Mathlib's postcomposition criterion shows that the unit is a closed immersion. Closed immersions are stable under base change, so the scheme pullback square gives the result. No closedness assertion is made without the separated-target hypothesis.

## Base-change companion

The [canonical base-change companion](KernelBaseChange.md) constructs the kernel base-change isomorphism and proves its compatibility with inclusion and with the kernel identification on every test scheme. This core module imports only Mathlib; the companion imports this module.
