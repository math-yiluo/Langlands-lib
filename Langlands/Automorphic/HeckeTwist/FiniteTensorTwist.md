# Finite tensor presentations after multiplication by any Hecke determinant character

Author: Worker 5136.

A finite tensor presentation (the Library's `FiniteTensorPresentation F n ρ E e he S`)
identifies a finite realization `S` with the restricted tensor product of local
representations `ρ v`, built from reference vectors `e v` fixed by `GL_n(𝒪_v)`
outside a finite set `E`. For an arbitrary Hecke character `χ`, this internal
module builds a finite tensor presentation of the twist
`S.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.FiniteLocalTwist`) from the local twists
`determinantTwistFactors χ` (the Library's `v ↦ (χ_v ∘ det) ⊗ ρ v`).

- `heckeDeterminantTwistExceptional χ`: the enlarged exceptional set
  `E ∪ χ.finiteHeckeDeterminantTail n` (module `FiniteTail`).
- `reference_fixed_on_heckeDeterminantTwistExceptional` and
  `heckeDeterminantTwistReference_fixed`: outside the enlarged set, the
  reference vectors are fixed by `GL_n(𝒪_v)` for the original and for the
  twisted factors, because `χ_v ∘ det` is trivial on `GL_n(𝒪_v)` there
  (`finiteLocalHeckeDeterminant_eq_one_outside_tail`).
- Private lemma: the restricted tensor representation of the twisted factors
  equals the twist, by `g ↦ χ(det (ofFinite g))`, of the restricted tensor
  representation of the original factors over the enlarged set. This uses the
  Library's `twistedRepresentation_eq` for a character trivial on the tail.
- `heckeDeterminantTwistEnlargedEquiv`: the original presentation, transported
  to the enlarged exceptional set (a private `tensorChangeEquiv`). Its
  `_pure` lemma says pure tensors go to the same forms as before.
- `heckeDeterminantTwistEquiv`: the restricted tensor product of the twisted
  factors is equivalent to the representation on `S.heckeDeterminantTwist χ`.
  The lemmas `_apply` and `evaluate_heckeDeterminantTwistEquiv` say that the
  form of a tensor is the original form multiplied by `χ(det a)`.
- `heckeDeterminantTwist P χ`: the resulting finite tensor presentation of
  `S.heckeDeterminantTwist χ` with the same reference vectors and the enlarged
  exceptional set. `evaluate_heckeDeterminantTwist_pure` evaluates it on pure
  tensors.

Provenance: internal. This is the Library module
`Langlands.Automorphic.FiniteTensorDeterminantTwist` with the finite-order
hypothesis removed. The tail of the character now comes from local constancy
(module `FiniteTail`). No correspondence with a particular passage of the
literature is claimed.
