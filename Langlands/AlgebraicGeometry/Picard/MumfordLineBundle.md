# The Mumford construction for an ordinary line bundle

`Langlands.AbelianScheme.mumfordHomOfLineBundle` gives an entry point
for an ordinary line bundle `L` on an abelian scheme `A/S`.
It first constructs its normalization along the unit section, then
applies the existing Mumford construction to that rigidified bundle.

## Normalization and explicit inputs

Write `f : A → S` for the structure morphism and `e : S → A` for
the unit. The constructor takes an ordinary line bundle `B` on `S`
and an actual evaluation isomorphism `e*L tensor B ≅ O_S`.
`LineBundle.normalize` then constructs

`N = L tensor f*B`

with its rigidification `O_S ≅ e*N`. Thus the base factor needed
for an unrigidified input is present in the actual constructed bundle.
No rigidification of `L` is assumed.

The next inputs are an ordinary inverse `M` of this normalized `N`
and an evaluation `N tensor M ≅ O_A`. This is an inverse of `N`,
not an inverse of the original `L`. Inverse existence and independence
of the choices of inverse bundles and evaluations are not proved here.

`mumfordFamilyOfLineBundle` is the actual rigidified Mumford family
of `N`, with the first product factor as parameter. The theorem
`mumfordFamilyOfLineBundle_forget` gives its exact ordinary bundle:

`(m*(L tensor f*B) tensor p1*M) tensor p2*M`.

Its proof is reflexivity after unfolding the existing normalization
and Mumford-family constructions.

## Classification and homomorphism

`mumfordSchemeMapOfLineBundle` classifies this actual family by the
chosen universal Poincare family. In addition to the normalization
and inverse inputs it requires the canonical pullback-tensor comparison
proposition, `MumfordBundlePicardZeroStatement`, and
`hA : HasDualScheme A`. The last predicate is actual universal-family
existence on all test schemes, including nonreduced schemes.

`mumfordSchemeMapOfLineBundlePullbackIso` is an isomorphism of
rigidified line bundles from Poincare pullback to the normalized family.
`mumfordSchemeMapOfLineBundle_unique` proves that any map with such
an isomorphism is the constructed map.
`mumfordSchemeMapOfLineBundle_points` gives the corresponding
parameter-pullback class formula on every `T : Over S`.
These declarations specialize the existing classification results to
the explicitly constructed `N`.

`mumfordHomOfLineBundle` bundles this same map as a homomorphism
from `A` to `dualAbelianSchemeFromEvaluation A ...`. Its additional
inputs are exactly those of `mumfordHom`: composition, unit,
associativity, left-unitor and symmetry coherences for the canonical
tensor comparison; Picard-zero pullback stability; the fixed
`MumfordSchemeMapHomomorphism` equations for `N`; a Poincare inverse
with its evaluation; and `DualSchemeGeometry A hA` for the same
chosen representing scheme. No morphism or target group operation
is supplied arbitrarily.

`mumfordHomOfLineBundle_hom` is the reflexive equality of the
underlying scheme morphism with `mumfordSchemeMapOfLineBundle`.
`mumfordHomOfLineBundlePullbackIso` and
`mumfordHomOfLineBundle_unique` specialize the rigidified pullback
isomorphism and uniqueness of the existing bundled homomorphism.
Uniqueness concerns the map for fixed data, not the isomorphism witness
or different choices of normalization.

All constructions are over an arbitrary base scheme, conditional on
their explicit inputs. This module proves no existence, geometric
Picard-zero, tensor-coherence, homomorphism-equation, or dual-geometry
theorem. It also asserts no ampleness, polarization, or isogeny result.

## Source and derived provenance

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft, section (6.2)(ii), printed p.89 (PDF p.93), normalizes an
ordinary line bundle to `L tensor f*e*L⁻¹` with its canonical
rigidification. Registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
This page was read in the original PDF. The supplied `B` and
evaluation give the same normalization, while the source's stronger
hypotheses for the relative Picard comparison are not needed for
this explicit conditional construction.

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, March 14, 2021 thesis revision, Construction 1.3.2.7,
printed p.75 (PDF p.103), constructs the associated homomorphism
from a rigidified line bundle. Registered source
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
This page was read in the original PDF; the corresponding March 2021
errata, registered `lan-2008-pel-thesis-errata-2021`, were checked
at pp.1 and 8–9 in the development of the imported construction.
Lan uses the second factor as parameter; the imported Mumford family
uses the first, with the positive-translation convention obtained
by exchanging factors using commutativity and tensor symmetry.

The present module is the derived composition of these two
constructions. It applies the rigidified construction to the
explicitly normalized bundle and reuses its proven conditional
properties. It does not remove the hypotheses or prove the deeper
relative existence and rigidity assertions in either source.
