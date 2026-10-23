# The geometric Picard-zero condition for the Mumford family

`Langlands.AbelianScheme.MumfordBundlePicardZeroStatement` is the precise
proposition needed to classify the constructed Mumford family by a dual
parameter scheme. It is a `Prop`-valued definition, with no proof of its
truth in this module.

For every base scheme `S`, abelian scheme `A/S`, and proof of the
canonical pullback-tensor comparison proposition, it quantifies a line
bundle `L` rigidified along `unitSection A`, an ordinary line bundle `M`
on `A`, and an evaluation isomorphism `L tensor M ≅ O_A`. It asserts

`IsPicardZeroFamily A (mumfordBundle A preservation L M evaluation)`.

All these arguments are universally quantified. In particular, no dual
scheme, arbitrary classifying map, or geometric Picard-zero condition
is supplied as input.

## Exact geometric meaning

The Mumford family is on the parameter-first product `A ×_S A`,
projected to its first factor. Its underlying bundle is
`(m*L tensor p1*M) tensor p2*M`; its rigidification along `(id,e)` was
constructed in `MumfordBundle`.

The existing `IsPicardZeroFamily` first moves the underlying bundle
across the canonical product symmetry to the total space of the
base-changed abelian scheme over the parameter `A`.
`IsGeometricallyPicardZero` then quantifies every algebraically closed
field `K : Type u` and every scheme morphism `a : Spec K → A`.
On that geometric fibre the line bundle must be isomorphic to its
pullback by translation by every `K`-valued point of the fibre group.
The isomorphisms in this condition are isomorphisms of actual line
bundles, not merely equality of point counts or numerical invariants.

This is a fibrewise condition on the actual family. It does not assert
a universal property, existence of a representing scheme, an
isomorphism of Picard functors, or additivity of a classifying morphism.

## Source and derived provenance

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft:

- Theorem (2.9), printed p.20 (PDF p.24), gives the theorem of the
  square: for an abelian variety `X`, line bundle `N`, and rational
  points `a,b`, the bundle `t_(a+b)*N tensor N` is isomorphic to
  `t_a*N tensor t_b*N`.
- Definition (2.15) and the following paragraph, printed p.22
  (PDF p.26), give the Mumford three-factor bundle and identify its
  restriction along a point in either factor with
  `t_a*N tensor N⁻¹`, up to the scalar line factor.

Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Both cited pages were read in the original PDF.

The statement is derived from these field results by applying them on
each geometric fibre. For a geometric parameter `a : Spec K → A`, let
`X = A_K` over the composite map to `S`, and let `N` be the restriction
of `L`. The same map `a` gives a `K`-point of `X`.
The fibre of the Mumford bundle is isomorphic to
`t_a*N tensor N⁻¹` tensor a line pulled back from `Spec K`.
The latter factor is trivializable, since it is a one-dimensional
`K`-vector space. The supplied evaluation identifies the restriction
of `M` with an inverse of `N`.

For every `b : X(K)`, the theorem of the square gives

`t_b*(t_a*N tensor N⁻¹)
  ≅ t_(a+b)*N tensor (t_b*N)⁻¹
  ≅ t_a*N tensor N⁻¹`.

This is precisely the translation-invariance condition used in the
Library. No identity-component comparison theorem is required to
state this target, because the Library predicate already uses
translation invariance.

The arbitrary-base scope here arises from quantifying geometric
fibres and applying the field theorem on each fibre. It does not
generalize a relative representability theorem beyond its source
hypotheses. A future proof must implement the actual base-change,
product-symmetry, translation-pullback and tensor comparisons, the
scalar-line trivialization, and the use of the evaluation isomorphism.
The displayed mathematical derivation records provenance; these
comparisons and the theorem-of-the-square consequence remain the
exact proof obligation.
