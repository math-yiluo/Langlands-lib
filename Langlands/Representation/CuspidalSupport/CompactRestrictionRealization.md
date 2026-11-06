# Realization of a constituent with compact restriction to an open normal subgroup

Author: Worker 1498. Module
`Langlands.Representation.CuspidalSupport.CompactRestrictionRealization`,
namespace `Langlands.CuspidalSupport`.

This module is an ancillary generic step for Renard, *Représentations des
groupes réductifs p-adiques* (French version dated 9 July 2026), VI.3.6,
Lemma, printed pp.147–148 / PDF pp.153–154 (registered as
`renard-2026-representations-groupes-reductifs-padiques`). It extracts the
group-independent part of the argument. Here `H` plays the role of Renard's
`⁰G`. The group-specific inputs are explicit premises: the finite index of
`H ⊔ Z(G)`, and the compactness of the restriction of the constituent to `H`.
The module does not prove those inputs for any particular group.

## Declarations

`exists_compact_openSubgroup_le U` holds for a nonarchimedean group `G` that
is a locally compact space. It gives every open subgroup `U` an open subgroup
`K ≤ U` whose underlying set is compact. It specializes the published
`compactOpenSubgroupBasis` to the neighbourhood `U` of the identity.

`constituent_of_compactRestriction H A D hAa hDi hDc hDA` works under these
hypotheses:

- `G` is a group with a topology for which it is a `NonarchimedeanGroup`, a
  `T2Space` and a `LocallyCompactSpace`.
- `H : OpenSubgroup G` is normal (`[H.toSubgroup.Normal]`), and
  `[(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]`.
- `A D : SmoothRep.{0, uG, uV} ℂ G` satisfy `A.IsAdmissible` and
  `D.IsIrreducible`.
- `hDc : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup
  H.toSubgroup D).representation` says that every coefficient of the
  restriction of `D` to `H`, against a smooth algebraic-dual vector, has compact
  support on `H`.
- `hDA : SmoothRep.IsSubquotient D A`.

The conclusion is `SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient
D A`. So there is an injective intertwiner `D → A` and a surjective
intertwiner `A → D`. They are not claimed to split each other.

## Implemented proof

The proof follows the assembly of the published product-Levi theorem
`leviCuspidalConstituentTheorem` (module `ConstituentProof`) and its
block-isolation step `leviCuspidalBlockIsolationTheorem`. The GL-specific
inputs are replaced by the generic hypotheses above.

1. **Admissibility of `D`.** Compact open subgroups are cofinal
   (`exists_compact_openSubgroup_le`). So the published
   `SmoothRep.isAdmissible_of_subquotient_of_compactOpenCofinal` makes the
   actual subquotient `D` of the admissible `A` admissible.
2. **Finite restriction.** Schur's lemma for admissible irreducible
   representations (`admissibleSchur_centralCharacter`) makes the centre act
   on `D` by scalars. With the finite index of `H ⊔ Z(G)`, the published
   Clifford theorem `FiniteIndexRestriction.finite_irreducible_restriction`
   gives a finite family `V : Fin m → Subrepresentation` of irreducible
   subrepresentations of `D|H` that spans `D`.
3. **Block isolation.** `H` is open, so it is locally compact
   (`IsOpen.locallyCompactSpace`), Hausdorff and totally disconnected. Give it
   its Borel σ-algebra and a Haar measure `μ`. The published complement
   theorem
   `CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation`
   then gives intrinsic complementarity of isotypic and annihilator parts for
   every compact class of `H`. Compact open subgroups of `H` are cofinal here
   by `Hecke.TestFunction.commonCompactOpenBiInvariance`. The published
   `CompactCoefficientClass.finiteFamilyBlockIsolation_of_isCompl` gets its
   input from `hDc` and the family `V`. It returns complementary
   `G`-subrepresentations `S`, `Q` of `A` with these properties:
   - `S|H` is semisimple.
   - Each irreducible subrepresentation of `S|H` is equivalent to some `V i`.
   - `D` is not a subquotient of `Q`.
4. **Transfer to `S`.** `irreducibleSubquotient_of_isCompl` places `D` as an
   actual subquotient of `S`. `S` is admissible through its injective
   inclusion (`isAdmissible_of_injective`).
5. **Constituent induction.** Each `V i` is nonzero, because an irreducible
   representation is nontrivial. Atoms of the subrepresentation lattice of
   `S|H` are irreducible (`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`).
   Inverting the equivalences from step 3 therefore gives the type coverage
   required by the published `constituent_of_finite_types`. That lemma then
   produces the injective and the surjective intertwiner for `S`.
6. **Back to `A`.** `constituent_of_isCompl` composes them with the inclusion
   of `S` and with the projection of `A` onto `S` along `Q`.

## Relation to the source

Renard's proof (PDF pp.153–154) has three steps:

- It uses the decomposition VI.3.5 to assume that `π` lies in the block
  `M(G)[τ]`, and deduces finite length from admissibility.
- It forms the finite-dimensional space `S = Hom_{⁰G}(τ, π)`, with the action
  of the free abelian group `Λ = G/⁰G`.
- It concludes with a simultaneous-eigenvalue argument, `S^Λ ≠ 0`.

This implementation follows another route:

- VI.3.5 is replaced by the compact-coefficient isotypic splitting over `H`
  (step 3). It isolates the finitely many `H`-types of the constituent
  directly.
- The `Λ`-eigenvalue argument is replaced by the published finite-index
  constituent induction `constituent_of_finite_types`. That induction uses
  central shifts and finite-index semisimplicity ascent (Bernstein–Zelevinsky
  1976, Proposition 3.30), which is why it needs `H ⊔ Z(G)` of finite index.
  The finite family of step 2 needs the same finiteness, as in Renard VI.3.2(ii).

No source theorem beyond the listed published Lean results is used.
