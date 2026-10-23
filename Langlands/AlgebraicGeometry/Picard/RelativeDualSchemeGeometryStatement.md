# Geometry of the chosen dual over a quasi-separated base

`Langlands.AbelianScheme.DualSchemeGeometry A hA` is the conjunction
that the structural morphism of the actual chosen parameter scheme
`dualScheme A hA` is smooth, proper and geometrically connected. This
predicate is defined for every base scheme. Its argument `hA` is the
existing proposition `HasDualScheme A`, which asserts existence of an
actual universal rigidified Picard-zero family.

`Langlands.AbelianScheme.RelativeDualSchemeGeometryStatement` asserts
this predicate for every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]`, every `A : AbelianScheme S`, and every
`hA : HasDualScheme A`. There is no noetherian, reducedness,
quasi-compactness or projectivity assumption. The quasi-separatedness
assumption on the base is essential to the stated source scope and is
retained explicitly. This is a proposition definition, not a proof.

The lemma `RelativeDualSchemeGeometryStatement.field` proves that a
proof of this relative statement supplies the existing
`FieldDualSchemeGeometryStatement`. Its proof specializes to `Spec k`,
which is affine and hence quasi-separated, and unfolds the geometric
conjunction by definitional equality. It does not prove either
geometric statement unconditionally.

## Original source and scope

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, Harvard thesis, revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`:

- The conventions, printed p.xxvi (PDF p.26), use quasi-separated
  preschemes as schemes.
- Definition 1.3.1.1, printed p.67 (PDF p.95), defines an abelian scheme
  by properness, smoothness and geometrically connected fibres, matching
  the geometric fields of the Library's `AbelianScheme`.
- Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74
  (PDF pp.101–102), describe Picard-zero families by fibrewise algebraic
  equivalence to zero and their rigidified representatives.
- Theorem 1.3.2.3, printed p.74 (PDF p.102), represents the rigidified
  Picard-zero functor by an abelian scheme. Definition 1.3.2.5 on the
  same page identifies its universal rigidified Poincare bundle.

The author's March 14, 2021 errata, registered separately as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9.
Page 1 replaces the older separated-scheme convention by
quasi-separatedness and recommends using the revision. Page 8 corrects
base-pulled line bundles in the original Picard functor to come from
`T`, rather than `S`; the revision incorporates this correction. We
use the revision's theorem numbering, not the original 2008 numbering.

Theorem 1.3.2.3 is the stronger relative theorem. Its following Remark
1.3.2.4 distinguishes it from the locally projective route. Consequently
this target does not silently remove the projectivity or locally
noetherian hypotheses from GIT, Chapter 6. Nor does it assert the
relative theorem over bases outside Lan's scheme convention.

## Derivation required for the exact Library target

The chosen scheme is selected from the universal property in
`HasDualScheme`. Its fibre predicate is translation invariance after
base change to every geometric point, using ordinary line bundles and
rigidification at the unit. The source instead describes algebraic
equivalence to zero. Over algebraically closed fields their comparison
uses Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft, Corollary (7.22), printed p.106 (PDF p.110), identifying `Pic⁰`
with the kernel of the line-bundle homomorphism. That registered source
is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

A proof must compare the actual rigidified functors, including families
over nonreduced test schemes; an equality of geometric point sets is
insufficient. In particular it must justify the passage between the
source's fibrewise algebraic-equivalence condition and the Library's
geometric-fibre condition, as well as their ordinary line bundles and
pullbacks. The source's convention restricts its test schemes to
quasi-separated schemes. The Library's universal property is stronger,
quantifying over all test schemes. For the present conditional geometry
claim, it can first be restricted to the source's test category. Its
comparison with the source representer must then recover an isomorphism
of the actual parameter schemes; affine test schemes and gluing detect
such an isomorphism even when the chosen parameter scheme is not yet
known quasi-separated. Finally, transport smoothness, properness and
geometric connectedness along that isomorphism. This is the required
mathematical derivation, not an implemented proof.

## Boundary

This unit does not establish universal-family existence. It keeps the
actual representability proof `hA` as a hypothesis and extracts no
arbitrary replacement scheme from geometric properties. The group
operations are already constructed separately from the Poincare family
in `DualGroupScheme`; this target supplies only the three remaining
geometric properties of that same underlying scheme. Tensor coherence,
ordinary inverse bundles, addition of dual maps, polarizations, and the
extension to a non-quasi-separated base are separate obligations. A
separate proof task must prove the exact relative proposition after
publication. No new axiom is introduced.
