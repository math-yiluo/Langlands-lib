# Essential finite presentation of scheme stalk maps

The theorem `Langlands.AlgebraicGeometry.stalkEssFinitePresentation.{u}` has
complete type
`Langlands.AlgebraicGeometry.StalkEssFinitePresentationStatement.{u}`.
The final example applies the theorem constant without supplying any arguments,
checking that complete type. The published statement, its essential finite
presentation predicate, and their imports are unchanged.

For schemes `X Y : Scheme.{u}`, a morphism `f : X ⟶ Y`, and a point `x : X`,
local finite presentation of `f` implies essential finite presentation of
`X.presheaf.stalk x` over `Y.presheaf.stalk (f x)`. The algebra structure is
precisely `(f.stalkMap x).hom.toAlgebra`. Local finite presentation is the only
hypothesis on the morphism.

## Implemented local-ring argument

The private helper `localRingHom_essFinitePresentation` starts with a finitely
presented ring homomorphism `f : R →+* S` and a prime ideal `q` of `S`.
Write `p = q.comap f`, `M = p.primeCompl`, and `N = q.primeCompl`. The image
`M.map f` lies in `N`. The proof factors the map of local rings through

\[
R_p \longrightarrow A = (f(M))^{-1}S \longrightarrow B = S_q.
\]

The first map is `g := IsLocalization.map A f M.le_comap_map`.
`RingHom.finitePresentation_localizationPreserves` shows that it is finitely
presented. Installing `g.toAlgebra` therefore supplies
`Algebra.FinitePresentation R_p A`.

For the second map, `IsLocalization.localizationAlgebraOfSubmonoidLe` and
`IsLocalization.localization_isScalarTower_of_submonoid_le` give the natural
`A`-algebra structure on `B` and the compatible tower `S → A → B`.
`IsLocalization.isLocalization_of_submonoid_le` identifies `B` as the
localization of `A` at the image of `N` under `algebraMap S A`.

The proof installs the `R_p`-algebra structure on `B` induced by the actual
`Localization.localRingHom _ q f rfl`. It verifies compatibility with
`R_p → A → B` using `IsScalarTower.of_algebraMap_eq'`. Equality of homomorphisms
from `R_p` reduces to equality on `R` by `IsLocalization.ringHom_ext`.
`Localization.localRingHom_to_map`, `IsLocalization.map_eq`, and the already
established `S → A → B` tower prove this equality. Thus the argument establishes
the conclusion for the specified local-ring map, including its algebra
structure.

The imported theorem
`Langlands.Algebra.essFinitePresentation_of_isLocalization` now gives essential
finite presentation of `B` over `R_p`: `A` is finitely presented over `R_p`, and
`B` is its localization at the indicated arbitrary submonoid. This uses the
published polynomial-quotient localization predicate directly.

## Passage to schemes

The closing theorem introduces the schemes, morphism, point, and local finite
presentation hypothesis, then applies Mathlib's
`AlgebraicGeometry.HasRingHomProperty.stalkMap_of_respectsIso`. Its two inputs
are the imported
`Langlands.Algebra.essFinitePresentation_respectsIso` and the private
local-ring helper above. The ring-hom property is essential finite presentation
for the algebra induced by the ring homomorphism. Mathlib's reduction uses
affine neighborhoods and the isomorphisms identifying affine stalk maps with
maps of localized coordinate rings. Isomorphism invariance transports the
local-ring result to `(f.stalkMap x).hom`.

No affine, Noetherian, flatness, quasi-compactness, or quasi-separatedness
hypothesis is required. The argument does not assert finite presentation of
the stalk algebra: the localization submonoid need not be finitely generated.

## Derived provenance

The scheme-stalk assertion is a derived consequence of affine local finite
presentation and the definition of essential finite presentation, rather than
a verbatim named theorem in the source. The registered source
`stacks-algebra-flatness-criteria-2026-10-22`, file `07DR.html`, gives
Definition 10.54.1 (tag 00QM), and Comment #2262 specifies arbitrary
multiplicatively closed subsets. Lemma 10.54.3 (tag 0AUF) provides the broader
base-change context. The registered folder SHA256 is
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
These passages were checked; no source-specific errata note was present.

The implemented route uses the previously published
`Langlands.Algebra.EssFinitePresentationTransportProof` and the pinned Mathlib
modules `AlgebraicGeometry.Morphisms.RingHomProperties`,
`RingTheory.RingHom.FinitePresentation`, and
`RingTheory.Localization.LocalizationLocalization`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Worker 136 implemented this local-ring and scheme reduction.
