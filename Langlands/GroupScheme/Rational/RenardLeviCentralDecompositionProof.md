# Compatible Levi central decompositions on the actual real torus spaces

Author: Worker 568.

The theorem `Langlands.GroupScheme.renardLeviCentralDecomposition.{u}` proves
exactly the published proposition
`Langlands.GroupScheme.RenardLeviCentralDecompositionStatement.{u}`.
It applies over every field `k : Type u` to connected reductive group schemes
`G` and `M`, a morphism `j : M ⟶ G`, their actual split components `aG` and
`aM`, and an actual morphism `f : AG ⟶ AM` with
`CommGroupScheme.groupHom f ≫ aM ≫ j = aG`.
All conclusions concern the published full real character and cocharacter
tensor spaces and their existing pairing.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, V.3.6, printed p.111 / PDF p.117, gives the
restriction square and the character and dual cocharacter decompositions.
Its restriction input is the Lemma and proof in V.2.6, printed pp.107–108 /
PDF pp.113–114. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These passages were read for this proof.

The arbitrary-field compatible-diagram formulation is the derived algebraic
scope of the existing statement. This theorem proves all of that statement's
conjuncts. The compatible component diagram remains a hypothesis; constructing
it for every Levi occurring in the source remains a separate geometric
obligation. No parabolic realization, root or coroot realization, invariant
inner product, or assertion from V.3.7–V.3.13 is added here.

## Real restriction bijections and the central character section

The private helper `restrictReal_bijective` applies the published theorem
`characterRestriction` to each split component. The resulting integral
injection and finite-index image give `rationalCharacterRestrictRatEquiv`.
Extending this rational equivalence to the reals and using
`Langlands.LinearAlgebra.rationalRealTensorEquiv` on both sides produces a
real linear equivalence. On an elementary tensor `r ⊗ χ`, its forward map is
exactly `r ⊗ characterRestrict a χ`, so it equals the published
`rationalCharacterRestrictReal a`. This proves both required horizontal
bijections without assuming a scalar-extension comparison.

The private helper `restrictReal_comp` derives contravariant composition
by tensor extensionality from `characterRestrict_comp`. In the main proof,
write

```text
rG = rationalCharacterRestrictReal aG,
g  = rationalCharacterRestrictReal (aM ≫ j),
r  = rationalCharacterRestrictReal (CommGroupScheme.groupHom f).
```

Composition and the supplied diagram give `r.comp g = rG`. Let `eG` be the
linear equivalence with forward map `rG`, and set `s = g.comp eG.symm`.
The inverse identities give `s.comp rG = g` and `r.comp s = id`.
Surjectivity of `eG.symm` gives `s.range = g.range`.

The published lemma
`Langlands.LinearAlgebra.isCompl_ker_range_of_bijective_comp`, applied to
`r` and `s`, proves that the literal kernel `r.ker` complements `s.range`.
The published `kerProdEquivOfBijectiveComp` constructs an equivalence
`r.ker × Vstar AG ≃ₗ[ℝ] Vstar AM`. Swapping its input factors and using
commutativity of addition gives the required equivalence with the exact
forward formula `(x,y) ↦ s x + y`.

## The cocharacter retraction and the pairing annihilator

Splitness of `AG` follows from `IsSplitComponent aG`. The published theorem
`RealTorusSpace.isPerfPair_of_isSplitTorus` identifies `V AG` with the dual
of `Vstar AG` through `(pair AG).flip`.
The private construction `transposeSection` therefore defines a linear map
`q : V AM →ₗ[ℝ] V AG` by composing `(pair AM).flip`, `s.dualMap`, and the
inverse of that identification. The private evaluation lemma states exactly

```text
pair AG x (q v) = pair AM (s x) v.
```

The published naturality identity `pair_cocharacterMapReal`, together with
`r.comp s = id`, implies `q.comp (cocharacterMapReal f) = id`.
Consequently the actual cocharacter postcomposition map is injective.
The evaluation lemma and nondegeneracy of the pairing on `AG` also prove

```text
q.ker = cocharacterAnnihilator s.range.
```

Here the right side is the existing annihilator for the actual pairing on
`AM`: membership means pairing to zero with every character in `s.range`.
Thus the relative cocharacter summand is exactly the one in the target.
Applying the same published kernel/range complement and product equivalence
to `q` and `cocharacterMapReal f`, then rewriting this kernel equality and
swapping the input factors, proves the second complement and the equivalence
with forward formula `(x,y) ↦ cocharacterMapReal f x + y`.

The proof uses no additional perfect-pairing, finite-dimensionality,
characteristic, or desired decomposition premise. Its internal constructions
use only the already published restriction theorem, scalar-extension
constructions, actual torus duality and elementary linear algebra. The
published target and its imports are unchanged.
