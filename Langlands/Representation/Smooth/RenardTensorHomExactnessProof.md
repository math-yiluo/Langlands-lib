# Exactness and preservation properties of smooth tensor and Hom

Author: Worker 139. The theorem `tensorHomExactness` proves the exact published
`TensorHomExactnessStatement` in `Langlands.Renard.Smooth`, with independent
group and carrier universes and no additional hypotheses.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, III.1.15, Theorem and proof, printed pp.69–70 (PDF pp.75–76),
registered as `renard-2026-representations-groupes-reductifs-padiques`.
The internal helper definitions and lemmas assemble published representation,
smooth-part, semisimplicity and linear-algebra results; they make no additional
literature assertion.

## Compact splitting and smooth Hom exactness

`compact_semisimple` specializes the published general theorem
`CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients`
to a compact Hausdorff totally disconnected group. Every coefficient has
compact support on a compact domain. The proof introduces the Borel measurable
structure and Haar measure internally, then uses Mathlib's correspondence
between representation semisimplicity and semisimplicity of its actual
group-algebra module. This uses neither the pending proof of the separate
Renard IV.1.1 statement nor an extra premise on the ambient group.

Mathlib's semisimple-module extension and lifting properties give a linear
retraction of an injective intertwiner and a linear section of a surjective
intertwiner over the group algebra. The published equivalence between
intertwiners and group-algebra linear maps turns these into compact-group
intertwiners (`compact_retraction` and `compact_section`). The carrier
universes in these helpers may differ.

`hom_fixed_iff` identifies fixed vectors for the Hom conjugation action with
maps intertwining the subgroup actions. For a smooth Hom vector, the published
`commonCompactOpenBiInvariance`, applied to the empty family of test functions,
refines its open fixing subgroup to a compact open subgroup. Pullback preserves
smoothness of the restricted representations. Composing with the compact
retraction or section extends or lifts the prescribed map. The result still
intertwines this subgroup, so it is smooth. The composition identities follow
from the splitting identities. These are `extend_smooth` and `lift_smooth`,
which establish the two exactness conclusions of the published statement.

## Projective and injective preservation

The internal predicates `IsProjective` and `IsInjective` are the same lifting
and extension formulas as the two local predicates of the published statement,
including its fixed carrier universe. `postcompose` and `precompose` are
algebraic Hom intertwiners; their smooth parts provide the relevant maps of
smooth Hom spaces. Smoothness of the diagonal tensor action follows by
intersecting pure-tensor stabilizers and using that pure tensors span
(`tensor_smooth`).

- `tensor_projective`: postcomposition by a surjective intertwiner is
  surjective on smooth Hom by `lift_smooth`. Curry the given map out of the
  tensor product, apply the source's projective lifting property, and uncurry
  the resulting lift. Evaluating the lift identity on pure tensors proves the
  required equality.
- `hom_projective_injective`: transposing an equivariant bilinear map gives
  an equivalence between maps into the two smooth Hom representations
  (`smoothIntertwinerFlip`). Precomposition by an injective intertwiner is
  surjective on smooth Hom by `extend_smooth`. Transpose the given map, use
  projectivity to lift it across this surjection, and transpose back. The
  extension identity is checked by evaluating in the two variables.
- `hom_injective`: tensoring an injective linear map over the field of complex
  numbers remains injective, by Mathlib's flat-module theorem. The tensor
  representations are smooth by `tensor_smooth`. Uncurry the prescribed map,
  extend it using the target's injective property, then curry the extension.
  Evaluation on pure tensors gives its extension identity.

Finally `tensorHomExactness` assembles these three preservation results and the
two smooth Hom exactness results in the order required by the unchanged
published proposition. All maps used by projectivity or injectivity stay in
its carrier universe; no group-size restriction or common universe for group
and carrier is introduced.
