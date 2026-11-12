# Renard VI.3.2(ii): proof of finite semisimple restriction to the norm kernel

Authors: Worker 4361, reusing the shared draft of Worker 101 with Worker 1292
(task `5c063810-e264-4d0d-95b4-0da35bdfedf5`).

`Langlands.CuspidalSupport.rationalNormKernelFiniteRestriction` proves exactly the
published proposition
`Langlands.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, uV}`
(module [`RationalNormKernelFiniteRestrictionStatement`](RationalNormKernelFiniteRestrictionStatement.md)),
at independent arbitrary universes `u` and `uV`, with no hypotheses.

For every nonarchimedean local field `F : Type u` of either characteristic, every
connected reductive `G` over `Spec F` with the canonical topology
`rationalPointTopology F G.X` on its rational points, and every irreducible
`π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G)`, put
`H := Plancherel.rationalCommonNormKernel G` and
`ρH := π.representation.comp H.subtype`. The theorem gives all three clauses:
`ρH` is semisimple, `ρH.asModule` has finite composition length over
`MonoidAlgebra ℂ H`, and finitely many irreducible subrepresentations of `ρH` span
the carrier of `π`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Proposition VI.3.2(ii), printed pp.143–144 /
PDF pp.149–150. The finite quotient used by the source is Proposition V.2.6, printed
p.108 / PDF p.114. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
No project errata record was found for it.

## Declarations

### `isFiniteLength_of_finite_irreducible_family`

For a representation `ρ` of a monoid `Γ` over a field `k`, a finite index type `I`
and a family `W : I → Subrepresentation ρ`, suppose every
`(W i).toRepresentation` is irreducible and `⨆ i, (W i).toSubmodule = ⊤`. Then
`IsFiniteLength (MonoidAlgebra k Γ) ρ.asModule`.

Proof. Mathlib's order isomorphism
`Subrepresentation.subrepresentationSubmoduleOrderIso` sends each `W i` to a
submodule `e (W i)` of `ρ.asModule`. The published
`Langlands.Subrepresentation.toSubmodule_iSup` turns the spanning hypothesis into
`⨆ i, W i = ⊤`, so `⨆ i, e (W i) = ⊤`. Each `e (W i)` is a simple module. The
subtype inclusion of `W i` is an intertwining map. Through
`Representation.IntertwiningMap.equivLinearMapAsModule`, its codomain restriction
is a bijective `MonoidAlgebra k Γ`-linear map from the module of
`(W i).toRepresentation` onto `e (W i)`. Mathlib's
`Representation.irreducible_iff_isSimpleModule_asModule` makes the first module
simple, and simplicity transfers along the bijection. Simple modules are
Noetherian and Artinian. A finite supremum of such submodules has both chain
conditions (`isNoetherian_iSup`, `isArtinian_iSup`). Since that supremum is `⊤`,
Mathlib's `isFiniteLength_iff_isNoetherian_isArtinian` gives finite length.

This is composition length over the monoid algebra. No finite dimension over `k`
is assumed or concluded.

### `rationalCommonNormKernel_sup_center_finiteIndex F G hG`

For every such `F` and connected reductive `G`, the subgroup
`Plancherel.rationalCommonNormKernel G ⊔ Subgroup.center (GroupScheme.rationalPoints G)`
has finite index in the rational-point group.

The shared helper in
[RationalNormKernelCentralFiniteIndex](RationalNormKernelCentralFiniteIndex.md)
proves this as follows.

1. The published `GroupScheme.splitComponentStatement` (Renard V.2.1) gives an
   actual split component `s : T.toGrp ⟶ G` with `hs : IsSplitComponent s`.
2. The published
   `Plancherel.RenardCartan.finiteIndex_splitValuationImage_of_injective`
   applies to the injectivity conjunct of
   `GroupScheme.characterRestriction F G hG T s hs`, giving
   `(RenardCartan.splitValuationImage s).FiniteIndex`.
3. The published `Plancherel.finite_rationalCentralQuotient`, applied to the
   centrality `hs.1.2`, gives finiteness of the quotient of the point group by
   `rationalCommonNormKernel G ⊔ (rationalPoints.map s).range`. Mathlib's
   `Subgroup.finiteIndex_of_finite_quotient` turns this into finite index.
4. `IsCentralSplitTorus.range_le_center` puts the range of `s` on rational points
   inside the centre of the point group. Hence the first join lies below
   `rationalCommonNormKernel G ⊔ Subgroup.center`, and
   `Subgroup.finiteIndex_of_le` gives finite index of the larger subgroup.

No equality between rational points of the scheme centre and the point-group
centre is needed.

This argument uses the published character-restriction and finite-index results
directly and introduces no separate proof of `SplitComponentLatticeStatement`.

### `rationalNormKernelFiniteRestriction`

The exact target. After introducing `F`, `G`, `hG`, the derived instances and the
canonical topology exactly as the statement does, take `π` and `hπ`.

- **Scalar centre.** The published `exists_scalar_rationalPoint_center F G hG π hπ`
  (module [`RationalPointCentralCharacter`](RationalPointCentralCharacter.md))
  shows that every element of `Subgroup.center (GroupScheme.rationalPoints G)`
  acts on `π` by a complex scalar. That proof uses second countability of the
  canonical point topology and countable-dimensional Schur. It needs no
  admissibility.
- **Finite index.** The previous theorem provides the instance
  `(H ⊔ Subgroup.center (GroupScheme.rationalPoints G)).FiniteIndex`.
  Normality of `H` is the published instance
  `Plancherel.rationalCommonNormKernel_normal`.
- **Clauses 1 and 3.** The published Clifford theorem
  `FiniteIndexRestriction.finite_irreducible_restriction π.representation H hπ`
  gets these two inputs. It returns semisimplicity of
  `π.representation.comp H.subtype` and `m : ℕ` with
  `W : Fin m → Subrepresentation ρH`, each `(W i).toRepresentation` irreducible
  and `⨆ i, (W i).toSubmodule = ⊤`.
- **Clause 2.** `isFiniteLength_of_finite_irreducible_family` applied to this
  family gives `IsFiniteLength (MonoidAlgebra ℂ H) ρH.asModule`.

The theorem has no hypotheses beyond the statement's own irreducibility premise.
None of the following is a hypothesis: a central character, scalar central
action, finite index of `H` or of any join or valuation image, admissibility,
finite generation, a chosen split component, semisimplicity, finite length or a
witness family. Each input is proved here or comes from published theorems.

## Comparison with the source proof

Renard fixes a finite set `Γ` of representatives of `G/Z(G)⁰G`, finite by V.2.6.
Schur's lemma makes `Z(G)` act by the central character. The restriction is then
finitely generated and has an irreducible quotient `σ`. The map
`⊕_{γ ∈ Γ} f ∘ π(γ)` embeds it into a finite sum of conjugates of `σ`, and
Lemma A.VII(iii) gives semisimplicity and finite length.

The Lean route uses the same two inputs, the scalar centre and the finiteness of
`G/(⁰G Z(G))`. The finiteness is derived through finite index of the actual
split-component valuation image, the integral form of V.2.6. The Clifford step
comes from the published general theorem. That theorem works with the normal
finite-index subgroup `H ⊔ Subgroup.center`. It embeds the restriction into a finite
product of simple quotients by the translates of a maximal proper
subrepresentation, which is a dual form of Renard's embedding. The scalar centre
then identifies the `H`-invariant and `(H ⊔ Subgroup.center)`-invariant
subspaces (`supCenterOrderIso`), so the conclusions pass to `H`. Finite length comes
from the finite spanning family by the helper above, not from a sub-object
criterion. These helpers and the finite-index theorem are internal deductions of
this proof route, not separately numbered results of Renard.

## Scope

This module proves only VI.3.2(ii) with its finite spanning-family consequence.
It does not prove VI.3.2(i) (the single `G`-orbit), VI.3.2(iii) (the equivalent
conditions on two restrictions), the norm-kernel inertia decomposition or the
VI.3.3.1 construction. It changes no imported Lean or Markdown file.

The finite-index helper `rationalCommonNormKernel_sup_center_finiteIndex` is
imported from [RationalNormKernelCentralFiniteIndex](RationalNormKernelCentralFiniteIndex.md).
The independently reviewed finite-restriction and twist-equivalence contributions
use this same proposition, so integration keeps one declaration in the shared helper module.
