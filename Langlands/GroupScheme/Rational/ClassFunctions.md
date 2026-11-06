# Regular class functions and the canonical affine conjugation quotient

Author: Worker 1360.

This module constructs a fixed regular-class-function algebra and its canonical
spectrum map for the actual given affine group scheme. All exported names below
are in `Langlands.GroupScheme.ClassFunctions`, in the module
`Langlands.GroupScheme.Rational.ClassFunctions`.

## Scope and actual coordinates

There is one arbitrary universe `u`, a field `K : Type u`, and a group scheme
`G` over `Spec (CommRingCat.of K)`, with `[IsAffineHom G.X.hom]`. There are
no smoothness, reducedness, connectedness, reductivity, finite-type, perfection,
or infinitude assumptions. Every coefficient algebra also belongs to universe
`u`.

`Coord G` is `Lie.coordinateAlgebra G`, a commutative `K`-algebra chosen
together with `Lie.coordinateIso G : Spec (Coord G) ≅ G.X` over `Spec K`.
Thus these are coordinates of the original group scheme. The map constructed
below is canonical relative to this one fixed coordinate presentation; no
comparison between different choices of presentation is asserted.

## Conjugation pullback and invariant algebra

Write `C = Coord G`. The maps `includeLeft G` and `includeRight G` are the
two algebra homomorphisms `C →ₐ[K] C ⊗[K] C`, sending `f` respectively to
`f ⊗ 1` and `1 ⊗ f`. The points `leftPoint G` and `rightPoint G` are their
inverse images under `Lie.pointCoordinates G`.

`conjugationHom G : G.X ⊗ G.X ⟶ G.X` is the actual morphism formed from
the first and second projections and the given group-scheme operations.
`conjugationHom_apply` proves on every test scheme that its value is
`g * x * g⁻¹`. The algebra homomorphism

```lean
conjugationPullback G : Coord G →ₐ[K] Coord G ⊗[K] Coord G
```

is the evaluation homomorphism of
`leftPoint G * rightPoint G * (leftPoint G)⁻¹`.
`conjugationPullback_eq` identifies this formula with coordinates of the
actual conjugation morphism evaluated on that universal pair.

The definition is the literal equalizer subalgebra:

```lean
algebra G = AlgHom.equalizer (conjugationPullback G) (includeRight G)
```

`mem_algebra` exposes its defining equation. `IsInvariant G f` means that for
every commutative `K`-algebra `A : Type u` and every pair of actual points
`g, x ∈ G(A)`, evaluation of `f` at `g * x * g⁻¹` equals evaluation at `x`.
`mem_algebra_iff_invariant` proves equivalence with membership in `algebra G`.
The quantifier includes nonreduced coefficient algebras. Values at fields, or
only at `K`-points, are not the definition.

The elementary proof uses `tensorEvaluation G g x`, the tensor-product algebra
map induced by the two evaluation homomorphisms. Its composites with the tensor
inclusions are the given evaluations, so it sends the universal pair to `g, x`.
Naturality of `Lie.pointCoordinates` and preservation of multiplication and
inverse under coefficient extension give `evaluate_conjugationPullback`.
Applying tensor evaluation to the equalizer equation proves invariance. For the
converse, take `A = C ⊗[K] C` and the universal pair itself.

## The fixed quotient object and morphism

`inclusion G : algebra G →ₐ[K] Coord G` is the subalgebra inclusion;
`inclusion_equalizes` gives equality of its composites with the conjugation
and projection pullbacks. The object and map are defined as

```lean
quotient G = (algSpec (CommRingCat.of K)).obj
  (op (CommAlgCat.of K (algebra G)))

rho G = (Lie.coordinateIso G).inv ≫
  (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (inclusion G)).op
```

`coordinateIso_hom_rho` exposes the defining spectrum map after the coordinate
presentation isomorphism. The name `quotient` denotes this affine invariant-ring
construction; this module does not prove a categorical universal property.

`quotientPointCoordinates G` identifies points of this spectrum on an affine
test `Spec A` with `K`-algebra homomorphisms `algebra G →ₐ[K] A`.
`quotientPointCoordinates_rho` proves that the coordinates of `x ≫ rho G` are
exactly `(Lie.pointCoordinates G x).comp (inclusion G)`. Full faithfulness of
relative Spec and extensionality of algebra homomorphisms then give
`rho_eq_iff`: two affine points have equal quotient images if and only if they
agree on every element of `algebra G`. Its forward direction is also exported
as `evaluation_eq_of_rho_eq`, valid for every commutative coefficient algebra,
and hence in particular for points valued in any field extension.

`rho_conjugation_affine` follows from that equality criterion and the
all-algebra invariance characterization. `rho_conjugation` proves

```lean
(g * x * g⁻¹) ≫ rho G = x ≫ rho G
```

for every scheme `Z` over `Spec K` and `g, x : Z ⟶ G.X`. Its implemented
proof uses the unit of `algΓAlgSpecAdjunction`: every map from `Z` to the
affine target `G.X` factors through the same affine object
`Spec ((algΓ K).obj Z).unop`. Apply affine invariance to the two resulting
points and precompose with this unit. Precomposition preserves the group
operations. The equivalent single morphism identity is exported as
`conjugationHom_rho`.

All these laws are proved from the constructed algebra and morphism. No
quotient object or desired invariance property is supplied as a premise.

## Sources and derived provenance

Provenance: derived/internal.

R. Steinberg, *Regular elements of semi-simple algebraic groups*,
Publications Mathématiques de l'IHÉS 25 (1965), 49–80, registered source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
The cited passages were read in the registered PDF; PDF pages are numbered from
one. No corresponding project errata note was found.

- Section 6.1 and its preceding definition, printed p.62, PDF p.15, introduce
  the algebra of regular class functions.
- Section 6.10 and its preceding paragraph, printed p.64, PDF p.17, describe
  fibres by equality on every regular class function and give the
  fundamental-character map in the simply connected case.
- Section 6.16, printed pp.65–66, PDF pp.18–19, gives Steinberg's quotient
  interpretation in that setting.

The Lean construction derives the elementary affine scheme-theoretic
invariant-subalgebra construction from this viewpoint and extends the definition
to arbitrary affine group schemes over arbitrary fields. The all-algebra
equalizer and the Γ–Spec coherence proofs are internal constructions, not claims
that Steinberg states them in this generality. In particular, this module proves
no finite generation, generation by fundamental characters, base-change
isomorphism, geometric-fibre theorem, cross-section or rational lifting theorem.
It leaves the existing `QuasiSplitSteinbergQuotientStatement` and all of its
imports unchanged.
