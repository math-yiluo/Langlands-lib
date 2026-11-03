# Closed representability of the scheme-theoretic derived subgroup

The theorem `Langlands.GroupScheme.derivedSubgroupRepresentability` proves the
published proposition `Langlands.GroupScheme.DerivedSubgroupRepresentabilityStatement`
from `Langlands.GroupScheme.Derived.StructureStatement`, at universe `u`. For every
field `k : Type u` and every actual group scheme `G` over `Spec k` with
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, it constructs an actual
group scheme `D` and a homomorphism `d : D ⟶ G` such that `D` is affine and locally of
finite type over `Spec k` and `IsDerivedSubgroup d` holds. That is, `d` is a closed
immersion and its range functor equals `derivedSubgroup G` on every test scheme over
`Spec k`, including nonaffine and nonreduced test schemes.

The construction of `D` uses neither that `k` is a field nor the finite-type
hypothesis. The finite-type hypothesis is used only to show that `D` is locally of
finite type. The theorem itself is stated and proved only in the published field scope.

## Helper declarations

The namespace `Langlands.GroupScheme.DerivedRepresentability` contains three helpers.

- `mem_range_comp_iso_iff`: for a homomorphism `i : H ⟶ G` and an isomorphism
  `φ : G ≅ G'`, a point `x` of `G` lies in the range of `i` exactly when `x ≫ φ` lies
  in the range of `i ≫ φ`. The proof composes with `φ⁻¹`.
- `Admissible G`: the type of pairs `(H, i)` with `i : H ⟶ G` a closed subgroup
  (`IsClosedSubgroup i`) whose range contains every commutator on every test scheme.
  These pairs index the intersection that defines `derivedSubgroup G`.
- `derivedSubgroup_eq_intersection`: `derivedSubgroup G` equals the published
  pointwise intersection `SubgroupFunctor.intersection` of the ranges of all
  admissible pairs. Both sides unfold to the same membership condition.

## Proof of the main theorem

1. Because `G.X.hom` is affine and `Spec k` is affine, the scheme `G.X.left` is affine
   (`isAffine_of_isAffineHom`). The published `AffineCoordinates.groupSchemeIso G`
   then gives an isomorphism `φ` from the corepresented group scheme
   `Corepresented.groupScheme (AffineCoordinates.functor G)
   (AffineCoordinates.corepresentation G)` to `G`. That group scheme is `Spec B` for
   the coordinate algebra `B = AffineCoordinates.algebra G`.
2. For each admissible pair `a = (H, i)`, the composite `i ≫ φ⁻¹` is a closed immersion
   (`IsClosedSubgroup.comp_iso`). The published `Corepresented.exists_ideal_range`
   gives an ideal `I a` of `B`, and `Corepresented.isAffineCutOutBy_range` shows that
   `I a` cuts out the range of `i ≫ φ⁻¹` on affine test schemes. The ideals are chosen
   with `choose`.
3. The published `Corepresented.intersectionScheme` and `intersectionHom` from
   `CorepresentedIntersection` give the closed subgroup cut out by the sum of the ideals
   `I a`. `D` is that group scheme and `d = intersectionHom ≫ φ`.
   `isClosedSubgroup_intersectionHom` and `IsClosedSubgroup.comp_iso` show that `d` is a
   closed subgroup.
4. `isRepresentedBy_intersectionHom` and the published
   `SubgroupFunctor.IsRepresentedBy.comp_iso` show that the range of `d` is the preimage
   under `φ⁻¹` of the intersection of the ranges of the composites `i ≫ φ⁻¹`. By
   `mem_range_comp_iso_iff`, applied to `φ⁻¹`, a point `x` of `G` lies in this preimage
   exactly when it lies in the range of every admissible `i`. By
   `derivedSubgroup_eq_intersection`, this is membership in `derivedSubgroup G`.
5. Over the base, `D.X.hom` is the composite `d.hom.hom.left ≫ G.X.hom` (`Over.w`). A
   closed immersion is affine and locally of finite type, and `G.X.hom` has both
   properties by hypothesis. So `D.X.hom` is affine and locally of finite type.

The index type `Admissible G` lies in `Type (u + 1)`. The published intersection
construction allows an index in any universe, and the sum of ideals is a supremum in the
complete lattice of ideals of `B`. So the large intersection needs no size argument.

## Comparison with the source

The statement's Markdown cites J. S. Milne, *Algebraic Groups* (2017), Definition 6.16
and the remarks after Corollary 6.19 (printed pp.129–130 / PDF pp.145–146). Milne
defines the derived group as the intersection of the normal algebraic subgroups `N`
with `G/N` commutative. For affine `G`, the remark after Corollary 6.19 describes its
coordinate ring as `O(G)/I`, where `I` is the intersection of the kernels `I_n` of the
algebra maps `O(G) → O(G^{2n})` given by products of `n` commutators. This Lean proof
takes a different route. It works with the published intersection definition of
`derivedSubgroup` and uses only one fact: every closed subgroup of an affine group
scheme is cut out by an ideal of the coordinate ring. An intersection of closed
subgroups is then cut out by the sum of their ideals. Nothing here describes `D` beyond
its range functor. In particular, the proof asserts nothing about smoothness,
connectedness, field base change or rational points of `D`.
