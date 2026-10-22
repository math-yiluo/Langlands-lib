# Local maximality of the orthogonal and unitary matrix groups

`Langlands.Group.UnitaryMatrixCompactOvergroupStatement` is a proposition
parameterized by a field `𝕜 : Type u` with `[RCLike 𝕜]` and a natural number
`n`. The universe `u` is arbitrary. The proposition states:

> For every subgroup `U` of `Matrix.GeneralLinearGroup (Fin n) 𝕜`, if its
> carrier is compact and it contains `Unitary.toUnits q` for every
> `q : Matrix.unitaryGroup (Fin n) 𝕜`, then every `g ∈ U`, viewed as a matrix,
> belongs to `Matrix.unitaryGroup (Fin n) 𝕜`.

This is a target for a separate proof. The module proves no maximality theorem.
There is no positive-rank assumption: `n = 0` uses the ordinary empty-matrix
convention. There is no invariant form, chosen compact-group model, or supplied
maximality assumption among the parameters or hypotheses.

## Groups, maps, and topologies

The `RCLike` structure supplies the scalar field operations, conjugation, norm,
and topology. Specialization to `ℝ` gives the full orthogonal group, and
specialization to `ℂ` gives the unitary group. No determinant-one restriction is
imposed.

`Matrix.GeneralLinearGroup (Fin n) 𝕜` is Mathlib's abbreviation for the units
of the matrix ring `Matrix (Fin n) (Fin n) 𝕜`. Matrices carry the existing
entrywise product topology. Matrix units carry the existing units topology,
induced by the map recording the value matrix and its inverse in the product
of the matrix ring and its multiplicative opposite. The opposite factor has
the transported matrix topology. Thus `IsCompact (U : Set _)` refers to the
carrier of the subgroup in that ambient units topology. No topology instances
are replaced.

`Matrix.unitaryGroup (Fin n) 𝕜` is Mathlib's actual unitary submonoid of the
matrix ring, with its existing group structure. Membership means that the
conjugate transpose is a two-sided inverse. Over `ℝ`, the conjugation is
trivial, so this is orthogonality. When viewed as a topological space, this
group has the matrix subtype topology; the proposition itself imposes no
additional topological hypothesis on it.

`Unitary.toUnits` is Mathlib's monoid homomorphism from unitary elements to
units. For a unitary matrix `q`, its value matrix is `q` and its inverse matrix
is the conjugate transpose of `q`. Consequently the containment hypothesis is
exactly containment of every standard unitary matrix in `U`. The conclusion
uses the ordinary coercion from a matrix unit to its value matrix.

## Consumer interface and internal provenance

Given `h : UnitaryMatrixCompactOvergroupStatement 𝕜 n`, a subgroup `U`, its
compactness proof `hU`, and `hcontains : ∀ q : Matrix.unitaryGroup (Fin n) 𝕜,
Unitary.toUnits q ∈ U`, the expression `h U hU hcontains g hg` gives the
unitary membership of any `g` with `hg : g ∈ U`. This pointwise conclusion is
the interface needed for coordinatewise use; it needs no intervening
range-equality theorem.

The statement is an internal structural prerequisite proposed for the published
`Langlands.Global.StandardInfiniteCompactMaximalityStatement` in
`Langlands.Global.ArchimedeanCompactMaximalityStatement`. The associated
`Langlands.Global.ArchimedeanCompact` module constructs the standard product of
real orthogonal and complex unitary groups, proves its compactness, and gives
`mem_standardInfiniteCompact_iff`, a coordinatewise membership criterion.
The present local target supplies the intended compact-overgroup maximality
input for those real and complex coordinates. Projecting compact overgroups,
verifying containment, and transporting back to the infinite completions remain
part of the separate global proof.

This provenance is internal: the target extracts a missing local assertion
from the existing global construction and maximality obligation. It is not
quoted as a theorem of Borel–Jacquet, and compactness of the standard group
alone does not prove it. No new literature claim or proof is asserted here.
