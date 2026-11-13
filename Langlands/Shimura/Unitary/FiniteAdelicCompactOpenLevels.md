# Compact open levels of finite adelic similitude groups

Author: Worker 19.

Several published constructions assume that a level exists. The CM small-level
index and tower take `[Nonempty σ.SmallLevelCategory]` as a hypothesis. The
prime-to cohomology of `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`
takes `[Nonempty (CompactOpenLevel (σ.PrimeToPoints m)ᵐᵒᵖ)]`. Until now the
Library did not prove either of these. This module proves both, for a rational
algebra with involution `σ : AlgebraInvolution ℚ A` with `A` finite over `ℚ`.
For the small levels it also needs `A` nontrivial. For Harris's central
simple unitary data `D` it proves them with no further hypothesis, as
instances.

The proof is topological. The finite adelic similitude group `σ(A_f)` is
Hausdorff, locally compact and totally disconnected, so it is locally
profinite. Van Dantzig's theorem then gives a compact open subgroup inside
every identity neighbourhood. The published `congruenceShrink` turns such a
level into a sufficiently small one.

## Sources

- Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties* (2001), source `harris-taylor-2001-geometry-cohomology-simple-shimura`,
  SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
  Chapter III.1, printed p.90 (one-based PDF p.98). The Shimura varieties are
  indexed by open compact subgroups `U` of `G(𝔸^∞)`, and the source uses
  sufficiently small ones. It treats their existence as standard and does not
  prove it.
- Van Dantzig's theorem is the published
  `Langlands.Topology.LocallyProfiniteProof.vanDantzig`. Its statement module
  `Langlands.Topology.LocallyProfiniteStatements` cites Renard,
  *Représentations des groupes réductifs p-adiques*, II.1.1.

The argument is the standard one, and it is internal to this module. The
topological facts about `σ(S)` and the adeles are elementary consequences of
published constructions, listed below.

## Setting

Declarations are in namespace `Langlands.Shimura` and its sub-namespaces
`Langlands.Shimura.AlgebraInvolution` and
`Langlands.Shimura.CentralSimpleUnitaryData`. `σ.Points S` is the published group of
similitudes of `σ` over a commutative `R`-algebra `S`: the pairs `(g, c)` in
`(S ⊗[R] A)ˣ × Sˣ` with `g σ(g) = c`. Its topology is the subspace topology,
where `S ⊗[R] A` carries the module topology over `S` and units carry their
usual topology (`Langlands.Shimura.Unitary.Adelic`). `σ.FiniteAdelicPoints` is
`σ.Points (FiniteAdeles ℚ)`. `σ.PrimeToPoints p` is
`σ.Points (PrimeToFiniteAdeles p)`. `CompactOpenLevel G` is a compact open
subgroup of `G`. The Harris levels of the CM tower are compact open levels of
the opposite group `σ(A_f)ᵐᵒᵖ`.

## Declarations

### Opposite levels

- `CompactOpenLevel.opOfCompact H hH`: for a compact open subgroup `H` of a
  topological group `G`, the compact open level of `Gᵐᵒᵖ` with subgroup
  `H.op`. It is open as the preimage of `H` under `MulOpposite.unop`, and
  compact as the preimage of `H` under the homeomorphism `Gᵐᵒᵖ ≃ₜ G`.
  `CompactOpenLevel.mem_opOfCompact` states that `g` lies in it exactly when
  `unop g ∈ H`.

### Adelic coefficient rings

Here `K` is a number field.

- `t2Space_finiteAdeles K`: `FiniteAdeles K` is Hausdorff, as a restricted
  product of Hausdorff spaces.
- `t2Space_primeToFiniteAdeles p`, `locallyCompactSpace_primeToFiniteAdeles p`,
  `totallyDisconnectedSpace_primeToFiniteAdeles p`: the prime-to-`p` finite
  adeles of `ℚ` are Hausdorff, locally compact and totally disconnected. Local
  compactness holds because the completed integers are open and compact
  (`isCompact_adicCompletionIntegers`). Total disconnectedness holds because
  the coercion to the full product `∏_v ℚ_v` is continuous and injective. The
  product is totally disconnected because each completion has an ultrametric
  norm.

Local compactness and total disconnectedness of `FiniteAdeles K` are the
published `finiteAdeles_locallyCompactSpace` and
`Langlands.Global.finiteAdeles_totallyDisconnectedSpace`. This module uses
them and does not prove them again.

### Similitudes over a general coefficient ring

Here `A` is finite and free over `R`, and `S` is a topological commutative
`R`-algebra that is a topological ring. A basis of `A` over `R` gives the
published continuous linear equivalence `coordinateEquiv : S ⊗[R] A ≃L[S] (ι → S)`,
so `S ⊗[R] A` is homeomorphic to a finite power of `S`.

- `isClosed_baseChange_similitudes σ S`: for `S` Hausdorff, the similitudes
  form a closed subset of `(S ⊗[R] A)ˣ × Sˣ`. The subset is defined by the
  equation `g σ(g) = c`. Both sides are continuous: the base-changed involution
  is `S`-linear, hence continuous for the module topology, and so is the
  algebra map `S → S ⊗[R] A`. The target is Hausdorff.
- `points_t2Space σ S`: for `S` Hausdorff, `σ.Points S` is Hausdorff.
- `points_locallyCompactSpace σ S`: for `S` Hausdorff and locally compact,
  `σ.Points S` is locally compact. Units of a locally compact Hausdorff ring
  with continuous multiplication are locally compact. The similitudes are a
  closed subset of a product of two such unit groups.
- `points_totallyDisconnectedSpace σ S`: for `S` totally disconnected,
  `σ.Points S` is totally disconnected. Each unit group injects continuously
  into its ring.
- `isLocallyProfinite_points σ S`: under all three hypotheses on `S`,
  `σ.Points S` is locally profinite.
- `exists_compact_openSubgroup_subset_points σ S hU`: every identity
  neighbourhood `U` of `σ.Points S` contains a compact open subgroup. This is
  `vanDantzig` applied to the locally profinite group `σ.Points S`.
- `exists_compactOpenLevel_op_subset σ S hU`: every identity neighbourhood of
  `(σ.Points S)ᵐᵒᵖ` contains the subgroup of a compact open level. Pull the
  neighbourhood back along `MulOpposite.op` and apply `opOfCompact`.
- `nonempty_compactOpenLevel_op σ S`: such a level exists (take `U` to be the
  whole group).

### The rational finite adelic and prime-to groups

Here `R = ℚ` and `A` is finite over `ℚ`, hence free.

- Instances `finiteAdelicPoints_t2Space`,
  `finiteAdelicPoints_locallyCompactSpace` and
  `finiteAdelicPoints_totallyDisconnectedSpace`: `σ(A_f)` is Hausdorff, locally
  compact and totally disconnected.
- `isLocallyProfinite_finiteAdelicPoints σ`: `σ(A_f)` is locally profinite.
- `exists_finiteAdelic_compactOpenLevel_subset σ hU`: every identity
  neighbourhood of `σ(A_f)ᵐᵒᵖ` contains the subgroup of a compact open level.
- Instance `nonempty_finiteAdelic_compactOpenLevel`: a compact open level of
  `σ(A_f)ᵐᵒᵖ` exists.
- `exists_smallLevel_subset σ hU`: for `A` nontrivial, every identity
  neighbourhood of `σ(A_f)ᵐᵒᵖ` contains the subgroup of an object of
  `σ.SmallLevelCategory`. Take a compact open level inside the neighbourhood,
  then a sufficiently small level inside it (`exists_levelSufficientlySmall_le`).
  So the sufficiently small levels form a neighbourhood basis of the identity.
- Instance `nonempty_smallLevelCategory_of_nontrivial`: for `A` nontrivial,
  `σ.SmallLevelCategory` is nonempty.
- Instance `nonempty_primeTo_compactOpenLevel σ p`: a compact open level of
  `(σ.PrimeToPoints p)ᵐᵒᵖ` exists, for every natural number `p`.

### Harris's central simple unitary data

Here `D : CentralSimpleUnitaryData E K A n` is the published unitary input of
module `Langlands.Shimura.Unitary.CMData`: a CM extension `K / E` of number fields, a central simple
`K`-algebra `A` of dimension `n²` and an involution of the second kind. Its
rational involution is `D.rationalInvolution : AlgebraInvolution ℚ A`. The
datum stores finiteness of `A` over `K` and simplicity of `A` as fields, not as
instances, so the instances above do not apply to it directly.

- `finite_rat D`: `A` is finite over `ℚ`, because `A` is finite over `K` and
  `K` is a number field.
- Instances `nonempty_finiteAdelic_compactOpenLevel D`,
  `nonempty_smallLevelCategory D` and `nonempty_primeTo_compactOpenLevel D p`:
  compact open levels of `D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ` and of
  `(D.rationalInvolution.PrimeToPoints p)ᵐᵒᵖ` exist, and
  `D.rationalInvolution.SmallLevelCategory` is nonempty. A simple ring is
  nontrivial, so the hypothesis `[Nontrivial A]` holds.

In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, `SmallCMLevel D`
is an abbreviation for `D.rationalInvolution.SmallLevelCategory`. Instance
search therefore finds `Nonempty (SmallCMLevel D)` without further
hypotheses. The published instances that assume it then apply
unconditionally. Examples are the cofilteredness of `OrderedSmallCMLevel D`
and the instance `orderedSmallCMLevelForget_op_final`. That instance says that
the opposite functor `(orderedSmallCMLevelForget D).op` is final, which is the
form used for colimits over shrinking levels. Arrows in the level categories
run from smaller levels to larger ones, so without `.op` the published result
is that the forgetful functor is initial (instance
`orderedSmallLevelForget_initial` of the rational involution). The
`[Nonempty (CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)]`
hypotheses of `HarrisTaylorCMPrimeToCohomology` are also found. These uses
were checked by `inferInstance` in a scratch file that is not submitted.

The module does not choose a canonical level, such as the units of a maximal
order. It proves existence only, which is all that the hypotheses above
require. Code and prose are by Worker 19. The pinned environment is Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
