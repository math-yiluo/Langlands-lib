# A projective embedding of a represented quotient Grassmannian

This module constructs a closed immersion of a supplied scheme representing
the quotient Grassmannian into polynomial projective space over the base.
The representing scheme and its affine chart description are hypotheses of
this intermediate result. They are not hypotheses added to the division-CM
representability target.

## Source and conventions

The source is the registered complete Anthropic FLT Lean distribution
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, distribution SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The two original files were read in full:

- `P2M/Sol/S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents.lean`,
  lines 1–571, SHA-256
  `4d4269c2c36c7009907ad98f8c5224cbb094793c6baf8ab467f36bbe76a48f50`.
- `Theorems/Thm_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents.lean`,
  lines 1–29, SHA-256
  `eea81622fe9982ad3bac4cd124774dc057c3a3b37b11f803d0eca3277e673dc6`.

The implementation retains the source's universe-zero rings, modules and
test algebras. For a commutative ring `A`, Mathlib's
`Module.Grassmannian A (A ⊗[R] M) k` consists of submodules whose **quotients**
are finite projective of constant stalk rank `k`. The rank condition concerns
the quotient, not the submodule. All base changes are the actual
`Module.Grassmannian.map` operations.

The projective-space object in the conclusion is exactly
`Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)`.
Its structure morphism is the existing `AlgebraicGeometry.ProjSpace.π`.
The imported `Langlands.AlgebraicGeometry.ProjectiveSpace.Charts` adapter,
through `Langlands.AlgebraicGeometry.ProjectiveSpace.PointComparison`,
connects this existing polynomial `Proj`
to the Library projective-space API. No new projective-space definition is
introduced.

## Exact inputs and conclusion

The helper structure `Module.Grassmannian.ProjectiveEmbedding.Rep R M k`
packages the following data:

- A universe-zero scheme `Gr` and a morphism `p : Gr ⟶ Spec R`.
- For every universe-zero commutative `R`-algebra `A`, an equivalence `pt A`
  between the quotient Grassmannian and actual scheme morphisms
  `Spec A ⟶ Gr` over `Spec R`.
- Naturality of `pt` for every `R`-algebra homomorphism `A →ₐ[R] B`, using
  Grassmannian base change and precomposition with the corresponding spectrum
  map.
- Open subsets `V x`, indexed by all tuples `x : Fin k → M`, whose supremum
  is the whole scheme, and a proof that each `V x` is affine.
- The exact chart criterion: the image of the morphism corresponding to `N`
  lies in `V x` if and only if the combination map
  `v ↦ ∑ i, v i • q_N (1 ⊗ x i)` from `Fin k → A` to the quotient by `N`
  is bijective.

`InChart` is a Prop-valued definition of this last bijectivity condition.
These inputs do not impose finiteness or freeness on `M`.

The exported theorem
`Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents`
additionally assumes `Module.Finite R M`. It concludes that there exist a
natural number `m` and an actual scheme morphism

```text
ι : Gr ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)
```

such that `IsClosedImmersion ι` and `ι ≫ ProjSpace.π R m = p`.
Its complete signature is byte-identical to the pinned original wrapper.
There is no nontriviality, positivity, finite presentation, freeness or
Noetherian hypothesis on the base ring or ambient module. In particular,
`k = 0` is included; some or all chart opens may be empty.

## Implemented construction

The helper namespace is
`Module.Grassmannian.ProjectiveEmbedding`. Its definitions and proofs retain
the following route from the original solution.

### Actual affine points and chart rings

For an arbitrary morphism `h : Spec A ⟶ Gr`, `algOfHom` obtains the
`R`-algebra structure on `A` from the ring homomorphism corresponding to
`h ≫ p`. `ptOf` then recovers the Grassmannian point using the inverse
of the given equivalence. `pt_ptOf` proves that its representing morphism
is exactly `h`. Conversely, `exists_algHom` recovers an actual algebra
homomorphism from an affine scheme morphism over `Spec R`.

For a tuple `x`, `S D x` is the actual section ring `Γ(Gr, V x)`.
The map `gS D x` is the affine-open map from its spectrum to `Gr`.
Its image is exactly `V x`. The universal point `NS D x` is recovered
from that map, and `NS_inChart` follows from the supplied image criterion.
The ring and scalar instances used by these definitions come from these
actual section rings and structure maps.

### Normalized determinant coordinates

`exists_Pl` imports the six proved Plucker-coordinate identities from
`Module.Grassmannian.exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit`.
`Pl` chooses a family satisfying them. The supporting lemmas retain:

- Reconstruction of each quotient image from single-entry tuple replacements.
- Normalization at the chart tuple.
- Naturality for every algebra homomorphism.
- The equivalence between another tuple being a quotient basis and its
  coordinate being a unit.
- Multiplicative coordinate transitions on two charts of the same quotient.

The imported existential statement also retains the determinant expression.
`eq_Pl_update` uses injectivity of the chart combination map to identify any
given quotient coefficient with the corresponding replacement coordinate.
These are coordinates of the same quotient point throughout the overlap
argument.

### A finite cover and local morphisms

Given a spanning family `g : Fin (n + 1) → M`, set
`mm k n = (n + 1) ^ k - 1`. The equivalence `ε` identifies
`Fin (mm k n + 1)` with all functions `Fin k → Fin (n + 1)`.
Thus `τ g l` enumerates all ordered `k`-tuples drawn from `g`, including
repetitions.

For each index `l`, the homogeneous coordinate family on `S D (τ g l)` is
`a l l' = Pl (τ g l) (Nτ l) (τ g l')`; its `l`th entry is one.
The published ratio-existence theorem gives an algebra homomorphism `ψ l`
from the `l`th affine chart of projective space to this section ring, taking
each normalized ratio to the prescribed coordinate. Taking spectra and then
the projective-chart inclusion defines `fS`; `fV` transports it to `V (τ g l)`.
The primary definition
`Module.Grassmannian.ProjectiveEmbedding.fS` is this actual local scheme
morphism. It is defined for every such family `g`; spanning is needed for
the covering and closed-immersion conclusions.

To prove these finitely many opens cover `Gr`, the implementation first
places a point in some original affine chart, then passes to its actual
residue field. The published field-valued spanning-family theorem supplies
a quotient basis drawn from `g`. The chart criterion and the actual
residue-field spectrum map return membership in the corresponding open.
This proves `exists_mem_V_τ` and `iSup_V_τ`.

### Agreement and gluing

`fS_indep` considers two affine chart maps lying over the same represented
Grassmannian point over an arbitrary test algebra `B`. Spectrum full
faithfulness and naturality recover the two algebra homomorphisms and identify
both base-changed universal points with that same point. The coordinate
transition identity provides a common homogeneous coordinate family. The
imported projective-point comparison theorem then proves equality of the
two actual morphisms to projective space.

`fV_compat` applies this affine argument on the affine cover of each
scheme-theoretic pullback of two covering opens. Mathlib's `glueMorphisms`
constructs `ιmap`. The chart restriction formula `Vι_ιmap`, cancellation
through the affine chart isomorphism, and compatibility of the ratio maps
with scalar maps prove `gS_ιmap` and `ιmap_π`.

### Closed immersion

`preimage_basicOpen` proves that the inverse image under `ιmap` of the
projective basic open `D₊(X l)` is exactly `V (τ g l)`. One inclusion uses
the ratio formula and the residue-field unit criterion to recover chart
membership. The other follows from factorization through the projective
affine chart.

`ψ_surjective` applies the imported chart-algebra generation theorem to the
actual affine chart `gS`. That theorem says that its ring is generated by
coefficients expressing the spanning family `g` in the quotient basis.
Each such coefficient is the image under `ψ` of a ratio indexed by a
single-entry replacement. Hence `ψ` is surjective.

On every target affine chart, the inverse-image equality identifies the
square with an actual pullback square of open immersions. The spectrum map
of the surjective ring homomorphism is a closed immersion. Transport along
the pullback isomorphism and Zariski locality at the target give
`isClosedImmersion_ιmap`.

The exported proof obtains a finite spanning family from `Module.Finite`,
pads it by an initial zero to obtain `Fin (n + 1)`, constructs `Rep` from
the supplied data, and returns `mm k n`, `ιmap`, its closed-immersion proof
and its compatibility with `p`.

## Adaptations and attribution

The port replaces generated `P2MW` and `GrassPluckerEmb` namespaces with
`Module.Grassmannian.ProjectiveEmbedding`, replaces the generated
`p2m_reactivate`/`p2m_exact_reverting` wrapper with a direct theorem export,
and imports the focused Library prerequisites by their Lean names. The
existing ratio-existence theorem is reused without modification.

There are seven local compatibility edits for the prepared Lean/Mathlib
version: five coercion-sensitive `rw` calls become `erw`, and the two
finite-cover indices in `ιmap_π` and `isClosedImmersion_ιmap` receive explicit
`Fin (mm k n + 1)` types. These edits affect elaboration, not the
objects, hypotheses or conclusions. Five proof-local instance declarations
are changed from `letI`/`haveI` to `let`/`have`. The two elementary tuple-index
lemmas `τ_symm` and `update_τ` omit an unused `AddCommGroup M` section
instance. The final exported signature and proof are unchanged apart from
the helper namespace qualification in the proof. No custom proof-generation
command or proof hole is retained.

The original distribution is Copyright 2026 Anthropic, PBC, under the
Apache License 2.0. See [LICENSE](../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../licenses/Anthropic-FLT/NOTICE) and
[ATTRIBUTION](../../../licenses/Anthropic-FLT/ATTRIBUTION.md). Worker 344
made the adaptations described above.

## Scope

This conditional result supplies a projective embedding of an already
represented finite-module quotient Grassmannian. It does not construct a
PEL abelian moduli scheme or assert smoothness, CM admissibility, a
polarization/Rosati comparison, an adelic level comparison, or a natural
identification with the normalized Harris CM presheaf.
`DivisionCMRepresentabilityStatement` remains a separate proof obligation,
including construction and applicability of the representing scheme and
all its specified geometric and normalized comparison properties.
