# Classification of geometrically Picard-zero line bundles up to a base twist

Authors: Worker 270 drafted the formulation and explanation; Worker 310 checked
the original source and Library interfaces and prepared the reviewed pair.

`Langlands.AbelianScheme.PicardZeroLineBundleClassificationStatement` is a
proposition definition. It quantifies over a proof `preservation` of the
existing `pullbackTensorComparisonIsIsoStatement`, every scheme
`S : Scheme.{u}`, every abelian scheme `A/S`, every proof
`hA : HasDualScheme A`, every `S`-scheme `T : Over S`, and every ordinary,
unrigidified line bundle `N` on the chosen total space
`(relativeSpace A.X.hom).obj T`, that is, on `T ×_S A`.

## Hypothesis

`N` is assumed to be Picard-zero on geometric fibres. The condition is the
existing `IsGeometricallyPicardZero` for the abelian scheme
`(baseChange T.hom).obj A` over `T`. It is applied to the pullback of `N`
along the inverse of the canonical symmetry
`relativeSpaceSymmetry A.X.hom T : T ×_S A ≅ A ×_S T`. This is the same
transport that `familyLineBundle` uses for rigidified families, so for the
underlying bundle of a rigidified family the hypothesis is exactly
`IsPicardZeroFamily`. The geometric-fibre predicate means translation invariance of the fibre
line bundle over each algebraically closed field in universe `u`, using
the actual fibre group law. No rigidification of `N` is assumed or supplied.

## Conclusion

There is a parameter map `φ : T ⟶ dualScheme A hA` in `Over S` and an
isomorphism of line bundles on `T ×_S A`

`N ≅ P_φ ⊗ pr_T^* (e_T^* N)`.

The factors are the following:

* `P_φ` is the underlying line bundle (`RigidifiedLineBundle.forget`) of the
  actual relative rigidified pullback
  `RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) _ φ` of the
  chosen `poincareFamily A hA`.
* `e_T` is the section `(relativeSection A.X.hom (unitSection A) _).app T`
  of `T ×_S A → T` induced by the unit section, and `e_T^* N` is the ordinary
  line-bundle pullback of `N` to `T`.
* `pr_T` is `(relativeProjection A.X.hom).app T`, the first projection
  `T ×_S A → T`.
* `⊗` is the existing `LineBundle.tensor preservation`.

The isomorphism is an isomorphism of underlying line bundles, not of
rigidified bundles. The conclusion asserts existence of `φ` only. It does not
assert uniqueness, and it does not claim the isomorphism is compatible with
the canonical identification of the restrictions along `e_T`.

There are no reducedness, noetherian, flatness or finiteness hypotheses on
`T`, and none on `S` beyond the existing abelian-scheme structure of `A`.
`HasDualScheme A` supplies an actual universal Picard-zero rigidified family.
The statement does not assert representability for every abelian scheme.

## Source and provenance

The original source is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI, (6.2), is on printed pp.88–89 (PDF pp.92–93). Under the
conditions (∗) of (6.2) (`f` quasi-compact and quasi-separated,
`f_*(O_{X×_S T}) = O_T` for all `T`, and a section `ε`), item (ii) states the
following. The class of a line bundle `L` on `X_T` maps to the bundle
`L ⊗ f^* ε^* L^{-1}` with its canonical rigidification. This map induces an
isomorphism `Pic(X_T)/pr_T^* Pic(T) ≅ P_{X/S,ε}(T)`. The universal property
of the Poincaré bundle is on printed p.88.

The Lean proposition is a derived statement. It combines surjectivity of the
map in (6.2)(ii) with the universal property of the chosen Picard-zero
family. It is rearranged so that it needs no inverse line bundles: instead
of `N ⊗ pr_T^* e_T^* N^{-1} ≅ P_φ`, it asserts `N ≅ P_φ ⊗ pr_T^* e_T^* N`.
It is restricted to bundles that are Picard-zero on geometric fibres, which
is the subfunctor that the chosen dual represents. The normalization keeps
this property because a line bundle pulled back from the parameter scheme
is trivial on each geometric fibre; tensoring by that trivial bundle does
not change the fibre isomorphism class. For abelian schemes the
source conditions (∗) follow from properness, smoothness, geometric
connectedness and the unit section. The relative statement
`f_* O = O` is the Library's separate, unproved proposition
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions`.

The cited pages were checked directly, including the normalization formula
in (6.2)(ii). No source-specific project errata note was present.

This explanation records the mathematical provenance. It is not a proof.
The module contains no proof or axiom of the proposition.

## Intended proof route

The following route is a lead for the separate proof task, not a formal
result. Cover `T` by opens on which `e_T^* N` is trivial. On each such open,
a trivialization makes `N` a rigidified family whose class is Picard-zero, so
`dualClassify` gives a local parameter map. Changing the trivialization by a
unit changes the rigidified class by a scalar automorphism, so the local maps
agree on overlaps and glue. For the local isomorphisms, normalize each one so
that its restriction along `e_T` is the canonical identification. Two such
normalized isomorphisms differ by an automorphism that is a global function
equal to `1` along the section, and relative global functions show it is
the identity. The normalized local isomorphisms therefore glue. The Library's
internal Hom sheaf of modules (`ModuleDual.lean`) is one way to glue them.

## Use

Task `b71714f0-c50a-4258-94ac-e065ce455f61` uses this proposition to prove
`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`. It applies
the proposition to `N = (m × id)^* P` on `B ×_S (B ×_S T)` for the
group law `m` of `B` and the Poincaré bundle `P` of `B`. A rigidity argument
then shows that the classifying map factors through the projection to `T`.
