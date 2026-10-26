# Finite generation of normalized opposite Jacquet modules

Author: Worker 23. The generator argument adapts the published upper proof
`Langlands.Parabolic.JacquetFiniteGeneration.finite_of_compactQuotient` by
Worker 319, which in turn adapts a single-vector cover step by Worker 238. Both
are credited as coauthors.

The theorem `Langlands.Parabolic.oppositeJacquetFiniteGeneration` has the
complete unapplied type
`Langlands.Parabolic.OppositeJacquetFiniteGenerationStatement.{uF,uV}`, imported
from `Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationStatement`.
Let `A` be a smooth complex representation of `GL_n(F)` that is finitely
generated over the ambient complex group algebra. The theorem proves that the
bundled opposite Jacquet module `CuspidalJacquetMultiplicity.oppositeJacquet T B A`
is finitely generated over the complex group algebra of the actual block Levi
`B.Levi F.Carrier`.

The statement quantifies over every prime, every actual p-adic field with a
compatible topological realization, every natural rank including zero, every
block shape, and every carrier in the independent universe `uV`. The proof adds
no hypotheses. Rank zero and the zero representation are covered by the same
argument.

## Representative calculations

Write `P̄` for `B.oppositeParabolic F.Carrier`, `N̄` for
`B.oppositeUnipotentSubgroup F.Carrier` and `M` for the block Levi. The helper
`OppositeJacquetFiniteGeneration.mk` is the coinvariant map
`Jacquet.mk A.ρ N̄`, typed with the bundled opposite Jacquet module as target.
It is surjective (`mk_surjective`) and invariant under `N̄` (`mk_apply_of_mem`).

`exists_unit_smul_mk` records the action formula. For `m ∈ M` and `v ∈ A`,

```text
(oppositeJacquet T B A).ρ m (mk v) = c • mk (ρ(leviEmbedding m) v)
```

for some unit `c : ℂˣ`. The unit is the published inverse half character of
the inverse transported upper modulus, evaluated at `leviEquiv m`. The equation
holds by definition (`rfl`) of `oppositeJacquet`, `normalizedActionOfModulus`
and `characterTwistedAction`. The proof therefore uses the exact published
normalization and never changes the Jacquet action. Only invertibility of the
scalar matters below.

`mk_levi_mem` follows. Let `S` be a subrepresentation of the opposite Jacquet
module, and suppose `mk v ∈ S`. Then
`mk (ρ(leviEmbedding m) v) = c⁻¹ • (oppositeJacquet T B A).ρ m (mk v)` lies in `S`.

`mk_oppositeParabolic_mem` extends this to every `q ∈ P̄`. The published
opposite Levi decomposition `B.oppositeDecomposition` factors `q` as
`u * leviEmbedding m`. Here `u = oppositeUnipotentPart q` lies in the opposite
radical, so its ambient matrix lies in `N̄`, and
`m = oppositeLeviProjection q`. The identity is the left inverse law of the
decomposition, read in the ambient group. Since `mk` kills the action of `N̄`,
we get `mk (ρ(q) v) = mk (ρ(leviEmbedding m) v)`, which lies in `S` whenever
`mk v` does.

## The double-coset cover

`exists_finset_oppositeDoubleCoset_cover` takes an open subgroup `K` and returns
a finite set `t` with `G = P̄ t K`. It assumes compactness of the quotient by
the upper parabolic of the reversed shape `B.reverse`. Let `w` be
`B.reverseMatrix F.Carrier` and `c` conjugation by `w`. Conjugation is
continuous, so `K' = c⁻¹(K)` is an open subgroup. The published
`Induction.exists_finset_doubleCoset_cover` gives a finite set `t'` with
`G = P_rev t' K'`, where `P_rev = B.reverse.parabolic F.Carrier`. Write
`c⁻¹(x) = q' i' k'` with `q' ∈ P_rev`, `i' ∈ t'` and `k' ∈ K'`. Applying `c`
gives `x = c(q') c(i') c(k')`. The published
`reverseMatrix_conj_mem_oppositeParabolic_iff` puts `c(q')` in `P̄`, and
`c(k') ∈ K` by the definition of `K'`. So `t = c(t')` works.

## The generator argument

`OppositeJacquetFiniteGeneration.finite_of_compactQuotient` follows the upper
proof step by step, with `mk` in place of the upper coinvariant map and
`mk_oppositeParabolic_mem` in place of the upper parabolic formula.

1. `Module.Finite.fg_top` gives a finite generating set `s` of `A` over `ℂ[G]`.
2. For each `v`, smoothness gives an open subgroup `K_v` fixing `v`, and the
   cover gives a finite `t_v` with `G = P̄ t_v K_v`. Write `g = q i k`. Then
   `ρ(k) v = v`, so `mk (ρ(g) v) = mk (ρ(q)(ρ(i) v))`. This lies in every
   subrepresentation `S` that contains all `mk (ρ(i) v)` with `i ∈ t_v`.
3. Let `y` be the finite union over `v ∈ s` of the vectors `mk (ρ(i) v)` with
   `i ∈ t_v`. Let `N` be its `ℂ[M]`-span and `S` the corresponding
   subrepresentation, obtained by `Subrepresentation.ofSubmodule'`. By step 2,
   `mk (ρ(g) v) ∈ S` for all `v ∈ s` and all `g`.
4. The ambient subrepresentation
   `C = {v | mk (ρ(g) v) ∈ S for every g ∈ G}` is the intersection of the
   inverse images of `S` under the linear maps `mk ∘ ρ(g)`. It is invariant
   because `ρ(a)(ρ(g) v) = ρ(a g) v`. It contains `s`, so its submodule
   contains the `ℂ[G]`-span of `s`, which is everything.
5. Taking `g = 1` and using surjectivity of `mk` gives `N = ⊤`. So `y` is the
   finite generating set required by `Module.Finite`.

The closing theorem installs `T.topology` and the published topological group
structure `T.generalLinearTopologicalGroup n`. It discharges the compactness
hypothesis with `Langlands.Parabolic.parabolicQuotientCompact F T B.reverse`,
which covers every rank and shape, and then applies the helper. No step needs a
nonzero vector, a nonempty generating set or positive rank.

## Provenance and scope

The original source is W. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups*, draft of 1 May 1995,
Theorem 3.3.1 and its finite-generation proof, printed/PDF page 35. The theorem
is stated for an arbitrary parabolic subgroup `P = MN`, so it covers the
opposite block parabolic. These pages were read for this proof. The registered
source is `casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.

Casselman picks one compact open subgroup fixing a finite generating set and a
finite set `Γ` with `PΓK = G`. Like the upper proof, the implementation instead
takes an open stabilizer and a finite double-coset cover for each generator,
then forms their finite union. The cover for the opposite parabolic is not
proved from scratch. It is transported from the published compactness of the
upper quotient for the reversed block shape, by conjugation with the published
block-reversing permutation matrix. This transport is an implementation choice,
not a step of the source.

The proof imports the statement module, the published quotient compactness
theorem (`Parabolic.QuotientCompactProof`), the finite double-coset cover
(`Induction.CompactQuotientProof`), the reversed-block conjugation lemmas
(`Group.GL.ReverseBlocks`) and Mathlib's subrepresentation correspondence. It
proves only finite generation of the opposite Jacquet module. It supplies no
admissibility, finite-length or refined-Levi result. The target pair and its
import closure are unchanged.
