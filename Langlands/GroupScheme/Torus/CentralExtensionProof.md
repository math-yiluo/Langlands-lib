# A central extension of a torus by a torus is a torus: proof

Worker 1395 wrote this module. It proves

```lean
theorem centralTorusExtensionStatement : CentralTorusExtensionStatement.{u}
```

for the published statement `Langlands.GroupScheme.CentralTorusExtensionStatement`
([`CentralExtensionStatement`](CentralExtensionStatement.md)). Let `k` be a
field and `E` a group scheme over `Spec k`. Let `Z` be a commutative torus and
`z : Z ⟶ E` a central closed subgroup. Let `T` be a commutative torus and
`p : E ⟶ T` an affine homomorphism that is an fppf quotient map with kernel
the range of `z`. Then `E` is a torus. The module also proves general lemmas
on base change of homomorphisms of group schemes.

## Contents

* The imported `baseChange_map_isPullback b f` from
  [`CentralIsogeny/FpqcReflection`](../CentralIsogeny/FpqcReflection.md):
  for `b : S' ⟶ S` and a homomorphism
  `f : H ⟶ G` of group schemes over `S`, the square formed by the underlying
  morphism of `(GroupScheme.baseChange b).map f`, the two projections
  `pullback.fst` and `f` itself is a pullback square of schemes. The outer
  square over `b` is a pullback, and the right square is one
  (`IsPullback.of_right`).
* `baseChange_map_of_isStableUnderBaseChange b P f hf`: a property `P` of
  morphisms of schemes that is stable under base change passes from `f` to its
  base change (`MorphismProperty.of_isPullback`).
* The imported `kernel_range_baseChange b q` from
  [`FppfQuotientComparison`](../FppfQuotientComparison.md): the range of the kernel of the
  base-changed homomorphism is the base change of the range of the kernel of
  `q`, as subgroup functors. A point of the base change is in the kernel exactly
  when its image under `baseChangePointsEquiv` is
  (`baseChangePointsEquiv_comp`).
* The imported `RelativeRoot.IsFppfQuotient.baseChange b h` from
  [`FppfQuotientComparison`](../FppfQuotientComparison.md):
  if `q` is an fppf quotient map
  with kernel `N`, its base change is an fppf quotient map with kernel
  `N.baseChange b`. Flatness, surjectivity and local finite presentation are
  stable under base change.
* `centralExtension_baseChange b z p hz hc hp hq`: the four hypotheses of the
  statement on `z` and `p` (closed subgroup, central, affine, fppf quotient
  with kernel `range z`) hold again after base change along `b`. This uses the
  Library's `IsClosedSubgroup.baseChange`, `IsCentral.baseChange` and
  `SubgroupFunctor.range_baseChangeHom`.
* `centralTorusExtensionStatement`: the proof below.

## Proof of `centralTorusExtensionStatement`

1. `Z` is a torus, so it splits over some field extension `K1` of `k`. The
   base change of `T` to `K1` is still a torus (`IsTorus.baseChange`), so it
   splits over some field extension `K2` of `K1`.
2. Base change `z` and `p` first along `Spec K1 → Spec k` and then along
   `Spec K2 → Spec K1`. By `centralExtension_baseChange`, applied twice, the
   hypotheses survive. Over `K2`, `Z` is split (`IsSplitTorus.baseChange`)
   and so is `T`, with index types `J` and `I`.
3. The split torus `𝔾_m^I` over `K2` is affine (`isAffineHom_splitTorus`), so
   the base change of `T` over `K2` is affine. The base change of `p` is an
   affine morphism into an affine scheme, so the base change of `E` over `K2`
   is affine. This is where the hypothesis `IsAffineHom p.hom.hom.left` is
   used: no lemma available here shows that a torus or an extension of tori is
   affine before splitting.
4. [`CentralExtensionHopfSpec.isSplitTorus_of_split`](CentralExtensionSplit.md)
   shows that the base change of `E` to `K2` is a split torus, hence a torus
   (`IsSplitTorus.isTorus`).
5. `IsTorus.of_baseChange`, applied first for `K2/K1` and then for `K1/k`,
   shows that `E` is a torus.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Dependencies

The proof uses these new modules, all by Worker 1395:

* [`Algebra/IntLatticeAlgebra`](../../Algebra/IntLatticeAlgebra.md): units and
  the Picard group of `K[ℤ^I]`.
* [`Algebra/GroupAlgebraCoaction`](../../Algebra/GroupAlgebraCoaction.md): the
  grading defined by a bialgebra map to a group algebra.
* [`Algebra/CentralTorusExtensionHopf`](../../Algebra/CentralTorusExtensionHopf.md):
  the Hopf algebra of a central extension of split tori is spanned by its
  group-like elements.
* [`GroupScheme/HopfSpecPoints`](../HopfSpecPoints.md): points of `hopfSpec`
  over affine tests.
* [`Torus/CentralExtensionHopfSpec`](CentralExtensionHopfSpec.md): translation
  of the geometric hypotheses into Hopf-algebra conditions.
* [`Torus/CentralExtensionSplit`](CentralExtensionSplit.md): the split affine
  case.

## Source and route

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`.
The statement's Markdown derives the result from Corollary 12.41 (printed
p.244, one-based PDF p.260), applied to the conjugation action of `T = E/Z`
on `E`, and Corollary 12.22 (printed p.239, one-based PDF p.255). The Lean proof
takes a different route. It base-changes to a field over which `Z` and `T`
split. There, centrality of `Z` and the triviality of the Picard group of the
Laurent polynomial ring show directly that the coordinate Hopf algebra of `E`
is spanned by group-like elements. Milne's criterion for diagonalizability
(Definition 12.7 and Theorem 12.8, printed p.233, one-based PDF p.249) then
makes `E` a split torus. The route is internal to this project; no rigidity
theorem is used.
