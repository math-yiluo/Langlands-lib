# Exact representability target for the normalized CM class presheaf

This pair defines a precise, unproved existence target for the existing
conditional Harris–Taylor normalized CM presheaf. It supplies no representing
scheme and no proof of representability.

`SmallCMLevel D` is the full subcategory of the original Harris transporter
category on the actual sufficiently small levels. Smallness tests finite order
after the actual projection to a finite local group. Morphisms retain their
original translating elements. `smallLevelClassPresheafTower` transposes the
existing `disconnectedClassTowerPresheaf` and restricts its level variable to
this category. Its value at a small level is therefore the actual presheaf of
normalized classes on the existing componentwise admissible CM bases. Its
arrows are precisely the existing natural level maps.

The arithmetic carriers are in universe zero. The codomain is `Type 1`, as
for the existing classes. For this reason the representing functor is Mathlib's
`uliftYoneda.{1}`: at an admissible base `S` it is the universe lift of the
actual morphisms `S → X` in the full subcategory of schemes over `Spec F`.
These are exactly actual scheme maps commuting with the given CM structure
maps. The lift changes no mathematical value.

`CMLevelRepresentation U` consists of:

- an actual object `X` of that same componentwise admissible base category;
- `Smooth X.obj.hom`;
- `IsHProjective X.obj.hom`, the existing predicate asserting a closed
  immersion into some finite polynomial-Proj projective space over `F`,
  commuting with the actual structure maps;
- a natural isomorphism from `uliftYoneda.obj X` to the actual presheaf at `U`.

Requiring `X` itself to belong to the test category is explicit. It includes
local Noetherianity and all the named componentwise prerequisites; these are
not proved here for arbitrary schemes. This requirement ensures that ordinary
fully faithful Yoneda applies to the actual representing objects. Restricting
the functor of points of a scheme outside the test category would not by
itself justify recovering a unique scheme map.

`CMLevelRepresentabilityStatement U` is the proposition that this precise
type is nonempty. `CMRepresentabilityStatement` requires it at every small
level of the particular supplied datum. Neither definition is a theorem.
A proof must construct the actual schemes and the specified natural
isomorphisms. No level maps, finite etale maps, Galois covers, complex
uniformization comparisons or local systems are stored as arbitrary output
fields in this representing evidence.

The inherited inputs remain explicit: the original number fields and
central simple algebra with involution and Harris signature charts, tensor
pullback comparisons and coherence, the named Picard and duality assertions,
polarization base change, finite Weil transitions, the rational profinite
integer/adele comparison and torsion finite etaleness. The class presheaf
retains its actual dimension, positive auxiliary involution, normalized CM
Lie condition, rational isogeny classes, level orbits, geometric-point
compatibility and product over actual connected components.

The source is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.90–91 (one-based PDF pp.98–99),
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 91 asserts smooth projective representability. Chapter III explicitly
uses the running assumptions of I.7, printed pp.51–55 (PDF pp.59–63), including
a **division algebra**, its local conditions and the specified signatures.
The host's `CentralSimpleUnitaryData` is more general. This pair defines the
pointwise desired property for that supplied datum; it does not assert its
truth for every such datum. In particular the source projectivity assertion
cannot be applied to arbitrary split central simple inputs without additional
justification. Any existence proof or proof task must state the applicable
arithmetic hypotheses as well as resolve the inherited named prerequisites
and the representing object's membership in the test category.

The target is a precise formulation on the currently constructed restricted
presheaf. Identifying it with the source functor on **all** locally Noetherian
`F`-schemes requires proving the retained prerequisites there. The categorical
transpose and restriction are derived from the preceding presheaf; the
representability property follows the cited source's desired conclusion with
these domain and hypothesis limits kept explicit. All code and prose in this
pair are by Worker 57. The pinned environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
