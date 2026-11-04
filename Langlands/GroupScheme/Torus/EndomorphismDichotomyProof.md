# Proof of the actual torus endomorphism dichotomy

Worker 1369 implemented the mathematical proof in the published module
`Langlands.GroupScheme.Torus.EndomorphismDichotomy`. Worker 1435 supplies this
exact proof entry and its explanation. Worker 1368 proposed the existing target
interface.

The proof entry checks the published theorem
`Langlands.GroupScheme.torusEndomorphismDichotomy.{u}` at the exact type
`Langlands.GroupScheme.TorusEndomorphismDichotomyStatement.{u}` with an anonymous
`example`. Consumers use the existing theorem directly; no duplicate public
alias is added. There are no additional parameters or hypotheses.

For every algebraically closed field `k : Type u`, actual commutative group
scheme `T` over `Spec k` satisfying the existing `IsTorus T.toGrp`, and actual
endomorphism `f : T ⟶ T`, it proves

```lean
Surjective (CommGroupScheme.groupHom f).hom.hom.left ∨
  ∃ ν : Gm (Spec (CommRingCat.of k)) ⟶ T,
    IsClosedSubgroup (CommGroupScheme.groupHom ν) ∧ ν ≫ f = 0
```

Here the first branch is surjectivity of the actual underlying scheme map.
The second exhibits an actual closed immersion from `Gm` whose composite with
`f` is the zero group-scheme morphism, and therefore is trivial on every test
scheme. The universe and characteristic are arbitrary, and rank zero is
included.

The imported proof first uses unconditional separably closed coalgebra spanning
through `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites` to split
the given torus over the algebraically closed field. Thus splitting is proved
from the stated hypotheses. It conjugates the endomorphism to a standard split
torus and uses its actual integral character map. An injective character map
induces a faithfully flat, surjective diagonalizable morphism. If the character
map is noninjective, Smith normal form and Orzech's theorem supply a surjective
integer functional annihilating its image. The functional induces an actual
closed immersion of `Gm`. All-test point extensionality proves the zero
composite, and the splitting isomorphism transports the resulting cocharacter
back to `T`. In rank zero the character map is injective, so the first branch
applies.

This module reuses that proof without modifying the target, its imports, or
the construction. The detailed implemented argument is documented in
[EndomorphismDichotomy.md](EndomorphismDichotomy.md). The original-source
provenance of the derived target remains in the unchanged
[EndomorphismDichotomyStatement.md](EndomorphismDichotomyStatement.md).
