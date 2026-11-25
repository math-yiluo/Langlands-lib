# Determinant-corrected shifts and reframes of actual Deligne data

This module constructs a right action of determinant-corrected pairs of a
linear automorphism and an integer shift on the actual admissible Deligne
isomorphism classes. Admissibility of each new representative is proved from
arithmetic subgroup membership. The quotient relation is preserved by the
constructed functors on genuine morphisms of all four sheaf data.

The source motivation is V. G. Drinfel'd, *Coverings of p-adic symmetric
regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4): the cyclically
graded flat coefficient lattice, invertible tangent components, homogeneous
locally generating map, rational degree-zero frame and conditions (a)–(c).
The registered source is `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The paired constructions and proofs are derived infrastructure for those
source data. Drinfeld does not separately state this corrected-pair subgroup
or its action.

## Hypotheses and conventions

All carriers have a common universe `u`. The coefficient ring `O` is
commutative, `F` is a field with an `O`-algebra structure, and
`hπ : algebraMap O F π ≠ 0`. The sheaf constructions have nonzero dimension
parameter `d`. Framed-lattice calculations work on any `TopCat X`; complete
four-data constructions use a scheme `S` with
`φ : O →+* Γ(S, ⊤)`. The corrected determinant homomorphism, subgroup and its
membership criterion do not require nonzero `d`. No coefficient-injectivity,
flatness of `F` over `O`, discrete valuation, local-field or nilpotence
hypothesis is used in these identities.

The constructed integer shift by `k : ℤ` makes new degree `i` old degree
`i+k` and uses the actual rational homogeneous Pi path to construct its frame.
Reframing by `g` replaces the frame `r` by `r ∘ g`. The product convention is
`(g*h)(v) = g(h(v))`; therefore applying `(g,k)` and then `(h,l)` gives
`(g*h,k+l)`. The final `MulAction` uses the opposite subgroup to encode this
right action as a left action.

## Actual commutation and functors

`FramedLatticePiSheaf.shiftInt_reframe` identifies the actual framed objects
obtained by either order of the two operations. Both keep the same total
lattice and give the same shifted homogeneous components. Their frames are
the constant-sheaf image of `g`, followed by the old frame and the constructed
integer Pi path, with only the parenthesization changed. Unfolding the
definitions and congruence prove the equality.

`SheafPreDatum.shiftInt_reframe` lifts this to the complete four-data
structure. Both sides have the same shifted tangent sheaf, total `u`,
Pi-compatibility, reindexed homogeneous maps and local-generation proof.
The proof unfolds the two constructions and uses congruence.

`SheafPreDatum.shiftReframe` is `(D.shiftInt hπ k).reframe g`.
`shiftReframeFunctor` composes the existing genuine shift and reframe
functors. `shiftReframeIso` transports an actual isomorphism by this composite;
the result preserves the lattice, tangent grading, frame and `u`.

`SheafPreDatum.IsoClass.shiftReframe` composes the previously constructed
preliminary-class maps, with `shiftReframe_mk` identifying its representative.
Quotient induction and actual commutation prove
`IsoClass.shiftInt_reframe`. The existing class identity and addition laws
then give `shiftReframe_one_zero` and `shiftReframe_mul_add`:

```text
shiftReframe hπ 1 0 q = q
shiftReframe hπ h l (shiftReframe hπ g k q)
  = shiftReframe hπ (g*h) (k+l) q.
```

## Literal determinant correction and admissibility

For every integer `i`, integer shift `k` and point `x`,
`FramedLatticePiSheaf.normalizedFrameDeterminant_shiftInt_reframe` proves

```text
norm((M.shiftInt k).reframe g, i, x)
  = scale(det(g) * pi^k, norm(M, i+k, x)).
```

Here `norm` is the existing actual normalized stalk determinant lattice, and
`scale` is multiplication on the already formed top exterior module. Thus
the source normalization remains literal `pi^(-i)` after exterior power.
The proof composes the existing reframe and integer-shift formulas and the
theorem multiplying consecutive scalar operations. It introduces no new
determinant model.

Suppose an actual unit `a : Oˣ` satisfies

```text
algebraMap O F pi ^ k * LinearMap.det g.toLinearMap
  = algebraMap O F (a : O).
```

`normalizedFrameDeterminant_shiftInt_reframe_of_unit` uses commutativity of
the field multiplication and the existing integral-unit scaling theorem to
identify the result with the old normalized lattice at degree `i+k`.

`constantOnPiZeroLoci_shiftReframe_iff` composes the previously proved
invariance under reframing and simultaneous grading translation. This
preserves condition (a) for the actual restricted coefficient sheaves.
`piQuotientResidueMap_shiftReframe` is definitional equality of the actual
total maps at every point. It gives
`residueFibreInjective_shiftReframe_iff`, preserving condition (b).

For condition (c),
`determinantNormalized_shiftReframe_iff_of_unit` identifies the new tangent
Pi-zero locus and component determinant at degree `i` with the old ones at
degree `i+k`. It rewrites the normalized frame determinant using the proved
unit correction. The resulting all-integer condition is equivalent to the
old one by substituting `i = j-k` in one direction and using `j = i+k` in the
other. It retains the point's Pi-zero-locus hypothesis throughout.
`admissible_shiftReframe_iff_of_unit` combines these three equivalences for
the existing stalkwise admissibility predicate.

## Arithmetic subgroup and genuine admissible action

`shiftReframeDeterminantHom hπ` is the group homomorphism

```text
GL(F^d) × Multiplicative Z → F-units
(g,k) ↦ (unit(pi))^k * LinearEquiv.det g.
```

The identity law uses the zero integer power. The product law uses the
integer power addition theorem, multiplicativity of the actual determinant
and commutative arithmetic in `Fˣ`.

`shiftReframeSubgroup hπ` is the inverse image under this homomorphism of the
image of `Oˣ → Fˣ`. Consequently identity, product and inverse closure come
from actual group homomorphisms and subgroup operations.
`mem_shiftReframeSubgroup_iff` identifies membership exactly with existence
of the displayed integral-unit equation. Its proof passes between equality
of units and equality of their values. In particular membership requires
arithmetic data, with no condition about the effect on a sheaf or a supplied
admissibility witness.

`SheafPreDatum.admissible_shiftReframe_iff` extracts this unit witness and
applies the preceding three-condition equivalence. `SheafDatum.shiftReframe`
therefore constructs an actual admissible representative from an admissible
input and a corrected pair. `shiftReframe_val` identifies its underlying
preliminary datum.

`SheafDatum.IsoClass.toPreliminary_injective` proves that the existing
forgetful map on classes is injective. Double quotient induction reduces
the claim to the two quotients' identical relation: existence of a genuine
isomorphism of the underlying four data.

`SheafDatum.IsoClass.shiftReframe` descends the corrected representative
construction with `Quotient.map`, using `SheafPreDatum.shiftReframeIso` to
transport the genuine relation.
`toPreliminary_shiftReframe` proves its compatibility with the preliminary
class map by quotient induction. Injectivity of `toPreliminary` now
transfers the preliminary identity and product laws to the admissible
classes, giving `shiftReframe_one` and `shiftReframe_mul`.

The two cancellation lemmas use this product law and the corrected
subgroup's inverse identities. `shiftReframeEquiv` packages each corrected
operation with the inverse corrected pair as its inverse bijection.
`shiftReframeRightAction` packages the identity and product laws into
`MulAction (shiftReframeSubgroup hπ)ᵐᵒᵖ` on the actual admissible classes.

## Remaining boundaries

The action proved here is for the specified arithmetic subgroup of
`GL(F^d) × Multiplicative Z`. Constructing a normalized pair from every
linear automorphism in the discrete-valuation setting, proving the trivial
action of scalar linear automorphisms and descending to a full projective
action are done in `DeligneValuedReframe`, `DeligneScalarClass` and
`DeligneProjectiveAction`. The action uses the existing stalkwise
determinant predicate; an independent exterior-subsheaf comparison is not
made here (`DeligneDeterminantSubsheaf` proves it). Arbitrary base change of the combined construction, comparison with
formal-module moduli, and representability are outside this module.
