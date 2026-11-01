# Actual left-Phi coefficient localization

Author: Worker 499.

This module constructs the linear equivalence `leftPhiTensorEquiv` in
`Langlands.Derivative.MirabolicProductMinus`. It identifies the actual
identity-orbit coefficient localization with the tensor of the first
factor and the positive-character localization of the second factor.
It proves naturality in both factors and proves that the actual
left-cycle coefficient localization has a subsingleton carrier.
These are coefficient constructions for the left mixed product.
The normalized representation comparison and final six-part host
statement remain separate obligations.

## Source and provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8, printed pp.444–445 (one-based PDF pages 5–6), supplies
character localization. Sections 3.1–3.2, printed pp.450–451 (PDF
pages 11–12), define the positive last-coordinate character and minus
functors. Section 4.12(II), printed pp.456–457 (PDF pages 17–18),
gives the left mixed subgroup; §4.13(b), printed p.458 (PDF page 19),
states the corresponding functorial comparisons. Section 7.2, printed
p.471 (PDF page 32), gives the cycle representatives used here.
These passages and the relevant page images were read during this
task. The bounded supplied-literature and public-note errata search
found no applicable BZ77 entry; no global absence is asserted.

The present quotient maps, equivalence and naturality proof are
internal derived constructions. Their actual matrix and character
inputs are the published `MirabolicMixedOrbitRadicals` and
`MirabolicMixedOrbitCharacters` formulas. The argument works over an
arbitrary commutative ring carrying the specified nontrivial additive
character, so this generality is not attributed verbatim to BZ77.
The source motivates the specialization, but its representation
comparison is not assumed. The quotient construction uses the
published universal property of `Jacquet.Localization`, not a
pending comparison theorem. Worker 499 wrote this construction;
no peer draft contributes a proof body.

## Parameters and actual carriers

Let `R : Type uR` be any commutative ring, and let `k,r : ℕ` be
arbitrary, including zero. The surjectivity lemma is entirely
algebraic. The character-localization declarations additionally take
an arbitrary `[TopologicalSpace R]` and
`ψ : UnitaryAdditiveCharacter R`; this bundle contains continuity
and nontriviality. They require no topological-ring, local-compactness
or field assumption. The pure tensor action lemma needs no topology.

Take arbitrary complex representations

```text
ρ : Representation ℂ GL_(k+1)(R) V,
τ : Representation ℂ P_(r+2)(R) W.
```

Here `V : Type uV` and `W : Type uW` have independent universes,
additive group structures and complex module structures. There is
no smoothness, finite-dimension, admissibility, irreducibility,
finite-length or genericity premise. Zero carriers are allowed.
The naturality theorem also allows `V' : Type uV'` and
`W' : Type uW'` in independent universes. No chosen vector or
universe saturation is used.

Library `mirabolic (r+1) R` denotes `P_(r+2)(R)`. The ambient
mirabolic group is `mirabolic (k+r+2) R = P_(k+r+3)(R)`.
For `i : Fin 2`, write

```text
I_i = leftRadicalIntersection k r R i,
c_i = leftRadicalCoefficient k r R i,
a_i = leftRadicalSource k r i,
θ_i = leftOrbitTheta k r ψ i.
```

`I_i` is the actual subgroup of the ambient radical obtained from
the published stabilizer and representative. Representative `0`
is the descending cycle, and representative `1` is the identity.
The maps `c_i` and `a_i` are the published homomorphisms on these
actual intersections. In particular the entire coefficient pair is
`c_i(u) = (1, a_i(u).val)`. No abstractly isomorphic group replaces
these domains or maps.

`leftPhiOrbitRepresentation i` is precisely
`(MixedProductTensor.external ρ τ).comp c_i`, a representation of
`I_i` on `V ⊗[ℂ] W`. To localize this representation by every element
of `I_i`, the subgroup argument of `Jacquet.Localization` is the
top subgroup *inside* `I_i`. Accordingly
`leftPhiOrbitCharacter i` is `θ_i` composed with that top subgroup's
subtype. The actual carrier is

```text
C_i = leftPhiCoefficientQuotient k r ψ ρ τ i
    = Coinvariants (leftPhiOrbitRepresentation i) ⊤
        (leftPhiOrbitCharacter i).
```

`leftPhiCoefficientMk i` is its canonical quotient map. Thus the
relations are exactly

```text
[c_i(u) acting on x] = (θ_i(u) : ℂ) • [x],   for every u in I_i.
```

The character is positive, with no inverse in these relations.
The source coefficient localization is

```text
Q_τ = Coinvariants τ (radical (r+1) R) (Mirabolic.theta ψ r).
```

It is the unnormalized localization carrier for
`phiMinus T ψ r : P_(r+2) → P_(r+1)` upon a supplied p-adic
specialization. This module neither introduces `P_0` nor applies
Phi-minus to `P_1`. A supplied `T` and determinant characters are
unneeded by this purely algebraic coefficient unit; no canonical
topology or normalized absolute value is selected.

## Surjectivity and the tensor equivalence

`leftRadicalSource_one_surjective` proves that the actual `a_1` is
onto. Given a source radical element `w`, let its source column be
`radicalCoordinates w`. Extend this column to length `k+r+2` by
zeros in coordinates below `k+1`, and use the source column in
coordinates `k+1+j`. The published `leftOrbitRadicalElement` belongs
to the actual identity intersection. `leftRadicalCoefficient_one`
says that its source column is exactly the tail just prescribed.
Finite-index extensionality and `radicalElement_coordinates`
therefore give `a_1(u)=w`. This construction uses no division,
rank positivity beyond the explicit shifts, or choice of a vector
in a representation.

`leftPhiOrbitRepresentation_one_tmul` applies the complete
coefficient pair formula and `MixedProductTensor.external_tmul`:

```text
leftPhiOrbitRepresentation 1 u (v ⊗ w)
    = v ⊗ τ(a_1(u).val) w.
```

The published `leftOrbitTheta_one` identifies `θ_1` with
`(theta ψ r).comp a_1` as unit-valued homomorphisms.
`leftPhiTensorForward` descends
`TensorProduct.map LinearMap.id (mk τ _ _)` through the relations of
`C_1`. Its relation proof first handles pure tensors by the displayed
action formula, the source quotient relation and the character
identity. Tensor induction proves the relation on arbitrary tensors.
Consequently its representative formula is

```text
leftPhiTensorForward [v ⊗ w] = v ⊗ [w].
```

`leftPhiCoefficientMk_one_source` proves that source-radical
relations already hold in `C_1`. For a source radical element `u`,
surjectivity supplies `a` with `a_1(a)=u`. Applying the actual
coefficient quotient relation at `a`, then the pure tensor action
and character identities, gives

```text
[v ⊗ τ(u.val) w] = (theta ψ r u : ℂ) • [v ⊗ w].
```

The implementation uses explicit congruences and a three-step
calculation; it does not assume an inverse to the radical source
map. `leftPhiTensorBilinear` descends the second slot of the
quotient-valued bilinear tensor map using this relation. Tensor
lifting of its flipped bilinear map defines `leftPhiTensorBackward`,
whose formula is

```text
leftPhiTensorBackward (v ⊗ [w]) = [v ⊗ w].
```

The two maps compose to the identity on the displayed generators.
For `V ⊗ Q_τ`, quotient-map surjectivity and tensor extensionality
suffice; for `C_1`, quotient-map extensionality followed by tensor
extensionality suffices. `LinearEquiv.ofLinearMap` packages the
result as

```text
leftPhiTensorEquiv : C_1 ≃ₗ[ℂ] V ⊗[ℂ] Q_τ.
```

Both forward and inverse representative formulas are recorded as
simp lemmas. This is an equivalence of actual modules. No action
of an orbit section, Haar ratio, scalar normalization or induced
representation comparison is asserted.

## Naturality and cycle vanishing

For arbitrary intertwiners `f : ρ.IntertwiningMap ρ'` and
`g : τ.IntertwiningMap τ'`, `leftPhiCoefficientMap f g i` is the
quotient map obtained by `mapLinear` from the pullback of
`MixedProductTensor.externalMap f g` along the actual `c_i`.
It sends `[v ⊗ w]` to `[f(v) ⊗ g(w)]`.

`leftPhiTensorEquiv_naturality` proves, for every `z : C_1`,

```text
E_(ρ',τ') (leftPhiCoefficientMap f g 1 z)
    = TensorProduct.map f.toLinearMap
        (mapLinear (radical (r+1) R) (theta ψ r) g) (E_(ρ,τ) z).
```

It reduces an arbitrary quotient class to a representative, then
uses tensor induction. The pure tensor equation is definitional;
linearity gives the addition case. The equivalences are fixed
before the arbitrary intertwiners are chosen, and the two new
carrier universes are independent.

For the cycle, `leftPhiCoefficientMk_zero` applies the published
`leftOrbitTheta_zero_equivariant_eq_zero` to the entire external
tensor representation and its actual quotient map. Quotient
relations supply the required equivariance. That published theorem
uses a radical translation invisible to the *entire* coefficient
pair whose ambient character is nontrivial; complex scalar
cancellation then forces every such linear map to vanish.
Finally, surjectivity of the quotient map shows that every element
of `C_0` equals zero. This is the named theorem
`leftPhiCoefficientQuotient_zero_subsingleton`.

## Import and mathematical dependency audit

The two direct project imports are
`Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters`
and `Langlands.Representation.Mirabolic.MixedProducts`. The complete
65-module project closure is listed below. Every imported Lean and
Markdown file is nonempty and byte-identical to the published
Library and its manifest at commit
`7ad6e7323f2d14f5ccf8d30daa428878acda72c4` (130 checked files).
Every imported pair remains unchanged. No pending normalization,
generic comparison statement, proof draft or host comparison is
imported.

The actual mathematical project inputs are the radical coordinates,
actual identity-orbit coefficient formulas, positive-character
identity and cycle vanishing lemma, external tensor construction
and intertwiner maps, and the character quotient's universal
property, representative relation and extensionality. The new
proofs use these with finite-index arithmetic, tensor lifting,
tensor induction and elementary linear algebra. The transitive
matrix calculations and character nontriviality underpin the
published formulas. Induction, smoothness, category and filtration
modules in the closure supply definitions and algebraic interfaces;
no mixed representation comparison, exactness conclusion or
consumer theorem is used. Whittaker modules supply only algebraic
character infrastructure. Proposition definitions supply no
unproved conclusions.

The following condition audit covers direct and transitive inputs.

| Condition | Actual dependency finding |
| --- | --- |
| Six host mixed-minus conclusions | No host conclusion or proof is imported. The unit proves only coefficient module assertions; the normalized natural representation comparisons, boundary maps and final conjunction remain separate. |
| Plus functors, adjunction, BZ77 §4.13(d) | No plus functor, adjunction or submodule-detection conclusion supplies an input. The matrix subgroup `plusSubgroup` appearing in the orbit definitions is the permitted elementary group. |
| General Leibniz and derivative formulas | No general Leibniz proof, segment derivative formula, Ze80 §3.5 or §9.6 formula, or unproved BZ77 derivative result supplies an input. |
| Segment head, socle and Jacquet formulas | No individual special-head or segment-socle existence, linked/unlinked or juxtaposed reverse-product conclusion, quotient homomorphism, or full/head/socle/special Jacquet formula supplies an input. |
| Product, commutation and gluing consumers | No segment product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, or Ze80 4.2 or 9.7 criterion is used. |
| Special-head criterion and generic uniqueness | Neither the special-head product criterion nor generic segment-product uniqueness is used. |
| Ordered existence and exhaustion | No ordered multisegment-socle existence, socle or special-head exhaustion, ordered strong-head existence, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered, square-integrable conclusions | No segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable classification or exhaustion, regular exhaustion, or Ze80 9.3 assertion supplies an input. |
| Two-supercuspidal consumers | Neither nonadjacent product irreducibility, product structure nor its full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) supplies an input. |
| Supercuspidal and single-block finiteness | No supercuspidal coinvariant-finiteness statement, all-character single-block conclusion, arbitrary-character finiteness theorem or consequence supplies an input. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal finiteness conclusion, consequence or prohibited mirabolic finite-length route supplies an input. |
| Generality | All natural k,r including zero and independent ring and four carrier universes are retained. The entire coefficient and source radical are used. No chosen unit vector, finite-dimensional, admissible, finite-length, generic or theorem-valued premise occurs. The character parameter is the supplied bundle. |
| Published inputs and target preservation | Every imported pair is unchanged and public. Pending statements, drafts and citations are not theorem premises. No host statement/import pair is modified. |
| Separate owners and user controls | This focused coefficient construction does not duplicate a restriction sequence, exactness proof or generic compact-induction comparison. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and all current suspensions remain binding; no peer message waives them. |

A source scan of this entry and its entire project closure finds no
occurrence in Lean code of the host's 38 excluded task identifiers
or 24 named consumer declarations, and no proof holes, new axioms
or unsafe evaluation commands. This syntactic scan supplements
the mathematical dependency audit above. Development compilation
and declaration inspection are not independent acceptance or
publication.

## Complete project import closure

Both direct roots and all their transitive project imports are
included, excluding the present module. Mathlib is supplied by the
pinned environment and remains unchanged.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
