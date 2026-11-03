# Unipotence of dynamic unipotent subgroups from two general unipotence inputs

This internal unit reduces the published proposition
`DynamicUnipotentUnipotenceStatement` to two separately published general
unipotence propositions. It proves the implication; it proves neither input and
does not assert an unconditional proof of the target.

## Statement

`DynamicUnipotentUnipotenceReductionStatement.{u}` is the Prop-valued
implication

`UnitriangularUnipotentStatement.{u} → UnipotentClosedSubgroupStatement.{u} →
DynamicUnipotentUnipotenceStatement.{u}`,

with all three propositions at the same arbitrary universe `u`. The inputs are
the existing statements:

- `UnitriangularUnipotentStatement`: over every field `k`, every standard upper
  unitriangular group scheme `GeneralLinear.blockUnipotentScheme (Fin N) k`
  with weights `i ↦ -i` is unipotent.
- `UnipotentClosedSubgroupStatement`: over every field `k`, if `H` is affine and
  locally of finite type over `Spec k`, `w : W ⟶ H` is a closed subgroup and `H`
  is unipotent, then `W` is unipotent.

The conclusion is the unchanged target: for every field `k : Type u`, every
group scheme `G` over `Spec k` that is affine and locally of finite type, every
homomorphism `χ : Gm ⟶ G`, and every homomorphism `j : H ⟶ G` representing
`Dynamic.unipotent χ`, the group `H` is unipotent. Unipotence is throughout the
representation-theoretic `IsUnipotent` of `Reductive/Basic.lean`: every nonzero
finite-dimensional matrix representation over `k` has a nonzero fixed vector.

## Proof

`dynamicUnipotentUnipotenceReduction` proves the statement. After introducing
the two inputs and the data of the target, affineness of `G.X.left` follows from
the affine structure morphism over the affine base `Spec k`
(`isAffine_of_isAffineHom`). The published affine representability results then
supply the canonical representative `Dynamic.Affine.unipotentHom χ` of
`Dynamic.unipotent χ`, with `Dynamic.Affine.isRepresentedBy_unipotentHom` and
the closedness theorem `Dynamic.Affine.isClosedSubgroup_unipotentHom`.

The published theorem `Dynamic.isUnipotent_of_unitriangular_inputs` in
`Dynamic/UnipotentStructure.lean` takes exactly the two inputs and proves that
this closed representative is unipotent: it uses the existing closed embedding
of a closed dynamic identity-limit representative into a standard upper
unitriangular group (`exists_closed_unitriangularEmbedding`), the first input for
the target of that embedding, and the second input for its closed subgroup.

Finally, two representatives of the same subgroup functor are isomorphic by
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`, which gives an actual
isomorphism `H ≅ Dynamic.Affine.unipotentScheme χ` of group schemes over
`Spec k`. The published `IsUnipotent.of_iso` transports unipotence along it, so
the supplied `H` is unipotent. No closedness of the supplied `j` is needed.

## Provenance

The target is Conrad–Gabber–Prasad, *Pseudo-reductive Groups* (2nd edition,
2015), Lemma 2.1.5, printed pp.50–51 (PDF pp.76–77), specialized to a field as
explained in the target's Markdown. CGP's proof embeds `G` into some `GL_n` and
reduces to Example 2.1.1, where `U_{GL_n}(λ)` is a unipotent group of upper
triangular matrices in a suitable basis. The Library's
`exists_closed_unitriangularEmbedding` formalizes that embedding step for the
dynamic subgroup itself; the two inputs record the remaining facts that the
unitriangular groups are unipotent and that unipotence passes to closed
subgroups (for the fixed-vector definition, Milne, *Algebraic Groups* (2017),
Theorem 14.5 and Corollary 14.7, printed pp.281–282 = PDF pp.297–298). These
inputs remain explicit premises here. The new content is only the assembly of these
published results with the transport along an isomorphism of representatives;
it introduces no external assertion or axiom. The field is arbitrary, with no
perfectness, algebraic closedness or characteristic restriction.
