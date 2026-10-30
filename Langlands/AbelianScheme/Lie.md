# Relative Lie modules of group schemes

For every actual group scheme `G : Langlands.GroupScheme S` over an arbitrary
scheme `S`, this module constructs `G.Lie : S.Modules` by

```
Lie(G/S) = Hom_OS(e* Omega_(G/S), O_S).
```

Here `e*` means pullback along the identity section, and `Hom_OS` is the
internal Hom sheaf. No smoothness, finiteness, affineness, commutativity or
quasicoherence assumption is imposed. The result is a sheaf of modules with
its genuine local scalar actions and descent, not a chosen module supplied
as additional input.

## Construction and local interpretation

`GroupScheme.identitySection G` is the underlying scheme morphism of the
unit of the actual group object in `Over S`. Mathlib's chosen cartesian
monoidal structure uses `Over.mk (identity S)` as its unit object, so this
morphism has domain `S` itself. `identitySection_comp` proves that it is a
section of `G.X.hom`. `identitySection_naturality` proves that every actual
group-scheme homomorphism preserves it, by taking underlying scheme maps
in the group-object unit law. The reassociated forms follow automatically.

`GroupScheme.cotangentAtIdentity G` applies Mathlib's module-sheaf pullback
along that section to the published concrete
`Langlands.Scheme.relativeDifferentials G.X.hom`.
`GroupScheme.Lie G` applies the published internal sheaf dual to this object.
Its target is the actual structure module
`Langlands.SchemeModule.structureModule S`.

For every open `U` of `S`, `lieSectionsEquiv G U` identifies sections with
module-sheaf morphisms from the cotangent module restricted to `U.toScheme`
to the structure module restricted to that same open subscheme. It uses
`internalHomSectionsEquiv`; it is not merely a Hom between the two modules
of sections on `U`. `lieEval G U` is the bilinear evaluation into
`O_S(U)`, obtained from `dualEval`. Both APIs inherit the already constructed
varying-ring module structure of the internal Hom.

`CommGroupScheme.Lie` and `AbelianScheme.Lie` are abbreviations for the same
construction on the underlying group scheme. The latter uses the published
actual abelian-scheme bundle, including its explicit commutativity convention.
There is no additional assumed tangent object.

## Provenance and scope

Conrad, Gabber and Prasad, *Pseudo-reductive Groups*, second edition (2015),
Section 2.1, printed page 52 (one-based PDF page 78), defines the cotangent
module along the identity by its conormal module and defines its linear
dual as the tangent module, written `Lie(G)`. The Stacks Project, Section
29.33, Lemma 29.33.16, identifies the conormal sheaf of any section with the
pullback of the relative differential sheaf along that section. These give
the formula implemented here. The scheme-wide formulation uses the internal
Hom of Stacks Section 17.22, opening definition. The existing differential,
pullback and internal-Hom constructions implement these sheaf operations.
The unit-section laws and specialization aliases are derived from those
constructions. This module does not separately formalize the comparison
with a conormal presentation or with dual-number kernels.

Registered sources:

- `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
  printed page 52, cotangent/tangent definitions and the notation `Lie(G)`.
- `stacks-relative-differentials-internal-hom-2026-10-21`, folder SHA256
  `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
  retained `01UM.html`, Definition 29.33.1 and Lemma 29.33.16;
  `01CM.html`, opening definition of internal Hom.

This is the object-construction unit. The differential of a group-scheme
homomorphism, its identity/composition and additivity laws, endomorphism
actions, base-change comparison, local freeness and rank statements are not
part of this module. No Lie bracket is constructed here. The universal
property of the constructed differential sheaf is proved separately:
`Langlands.Scheme.relativeDifferentialsUniversal :
RelativeDifferentialsUniversalStatement f`, for every morphism `f`, in module
`Langlands.AlgebraicGeometry.RelativeDifferentialsUniversal`. This module does
not import that theorem and does not use it.
