# Local-field neighborhood bases from actual congruence towers

The stable full target declaration is
`Langlands.GroupScheme.LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement`.
It is a Prop-valued `def`, with arbitrary universe parameter `u`, and is **an
unproved target**. This pair states no theorem establishing it.

This is an internal topological consequence proposed for the actual model
and quotient constructions in `IntegralModel.CongruenceTower`. Its provenance
is the finite-coordinate description of an affine finite-type scheme over a
local-field valuation ring, rather than a building theorem or a new
literature-specific assertion. The intrinsic quotient, point-map, normality,
antitone and residue-comparison laws are already constructed there. The
compactness, openness and cofinality assertions in this file remain separate
proof obligations.

The target quantifies over every `F : Type u` carrying `Field F`,
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`,
every affine `G/F`, and every supplied
`M : LocalFieldIntegralModel F G`. This model is exactly an
`IntegralModel ↥𝒪[F] F G`; its data already include an affine, flat,
locally finite-type structural morphism and the specified generic-fibre
isomorphism. Over the affine base an affine morphism is quasi-compact, so the
model is finite type. The explicit `IsAffine G.X.left` instance is needed to
name the rational-point topology; it is consistent with, and follows from,
the affine model and its generic-fibre isomorphism.

The topology on the original carrier `rationalPoints G` is assigned explicitly
by the local instance `rationalPointTopology F G.X` inside the statement.
The integral subgroup is the published image `M.integralPoints` under the
original `M.integralPointMap`. The level-`n` subgroup is exactly
`IntegralModel.congruenceSubgroupAt M n`: the image of the kernel of reduction
to the actual base change over
`↥𝒪[F] / (IsLocalRing.maximalIdeal ↥𝒪[F]) ^ (n : ℕ)`.
The original supplied generic identification is retained in this image.

The conjunction asks for these precise conclusions:

1. `M.integralPoints` itself is compact and open in the ambient rational-point
group with that topology.
2. For **every positive level `n : ℕ+`**, the same actual generic congruence
subgroup is compact and open in the full ambient group, and its restriction
to `M.integralPoints` is normal there.
3. For **every set `U` in the full ambient filter `𝓝 (1 : rationalPoints G)`**,
some positive congruence subgroup is a subset of `U`.

Thus cofinality is in the full ambient identity-neighborhood filter; neither
openness nor cofinality is restricted to an unproved relative topology on the
integral image. Every subgroup contains the identity, so the openness and
cofinality conclusions describe an identity-neighborhood basis. The
construction supplies the antitone positive indexing. Level zero is excluded
consistently. Its level-one subgroup is proved in the construction file to
be the published residue congruence subgroup via the canonical residue
quotient equivalence.

Smoothness is **not needed** for this proposed topology result and is not a
premise. The reason for this choice is a finite-coordinate proof route: choose
finitely many generators for the actual model coordinate algebra. A generic
point is integral exactly when those generator values lie in the open
valuation subring, using affine descent and the actual coefficient inclusion.
A congruence condition on those values is membership of their differences
from the identity values in the open ideals `m^n`; the same generators detect
the equality of the two quotient-valued points. Small powers of `m` shrink
these finitely many coordinates inside any prescribed ambient neighborhood.
Compactness follows from closed coordinate conditions on the compact integral
section space and continuity of the original integral-point map. This route
uses no lifting of arbitrary quotient points, so it introduces no smoothness
or reduction-surjectivity requirement. These sentences explain the scope
choice and proposed proof, not a completed Lean proof.

The existing published `IntegralModel.isCompact_integralPoints_localField`
already supplies the integral-image compactness conjunct. Kernel normality
and the image-normality conjunct are intrinsic construction laws.
The compactness of each congruence image, openness of the integral image and
each congruence image, and cofinality remain to be established by the proof
successor targeting this exact declaration.

Both equal and mixed characteristic local fields are included. No
reductivity, connectedness, smoothness or maximal-reductive-quotient condition
on the full special fibre is assumed. There is no special-compact, building,
fixer, Iwahori, geometric Levi or simultaneous-basis premise or conclusion.
