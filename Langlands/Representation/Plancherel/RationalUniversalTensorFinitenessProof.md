# Universal tensor fixed modules

Worker 1780. Proof of the published
`Langlands.Plancherel.RationalNormalized.RationalUniversalTensorFinitenessStatement.{uV,u}`,
from David Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, VI.8.1,
printed pp.187–189 / PDF pp.193–195. Source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The final theorem `rationalUniversalTensorFiniteness` proves the exact existing
proposition with independent field/group universe `u` and representation-carrier
universe `uV`. It uses the literal actual Levi subgroup, the complete
`parabolicLeviRationalNormCharacters r` family, and the existing universal action
on `RegularAlgebra r ⊗[ℂ] E`. No definition in the statement or its imports is
changed. The hypotheses of the published proposition, including its actual
point topology and parabolic presentation, are preserved.

The internal helper `universalTensorFixedInclusion_bijective` works for any
family of continuous positive norm characters on a topological group. It
proves bijectivity of the published canonical inclusion
`B ⊗[ℂ] E^J → (B ⊗[ℂ] E)^J` for every compact subgroup `J`, without
smoothness or admissibility assumptions. This supplies the tensor comparison
used in the source example on printed p.189.

The proof chooses a complex vector-space basis of the actual regular algebra
`B`. The equivalence `TensorProduct.equivFinsuppOfBasisLeft` writes each tensor
as a finite sum of basis vectors tensored with coefficients in `E`. By the
published compact-character theorem, every norm character is one on `J`.
Consequently the universal evaluation character is one there, and the
coefficient of the universal action is the original action on that coefficient.
Each coefficient of a fixed tensor therefore belongs to `E^J`. Reassembling
the same finite sum with coefficients in `E^J` gives a preimage under the
canonical inclusion. Injectivity follows because the complex vector space `B`
is flat, so tensoring preserves the original fixed-subspace inclusion.

`universalTensorFixed_finite_projective` uses this bijection and the
finite-dimensionality of `E^J` to transfer finite generation and projectivity
from `B ⊗[ℂ] E^J`. Mathlib supplies finite generation by scalar extension,
freeness of a tensor of free modules, and projectivity of free modules. The
internal theorem `universalTensorFlatness` similarly uses that the literal
`B ⊗[ℂ] E` is free over `B`, hence flat. This does not require Noetherianity,
nor a finite selection of the rational norm characters.

`universalTensorFixedComparison` takes the inverse of the equivalence obtained
from the canonical inclusion. Its inverse linear map is definitionally the
published `tensorFixedInclusion`, as required by the exact comparison predicate.
`universalTensorFiniteness` combines flatness with this comparison and finite
projectivity for each compact open subgroup, using the corresponding original
fixed-space finiteness from `IsAdmissible σ`.

These basis and scalar-extension arguments are internal proofs of the
assertions in Renard VI.8.1; they do not formalize the full criterion for
arbitrary flat admissible families on pp.187–188. Normalized induced-family
finiteness and native coefficient Jacquet finiteness are subsequent obligations.
In particular this module constructs no geometric-lemma filtration and makes
no assertion of output-Jacquet admissibility.
