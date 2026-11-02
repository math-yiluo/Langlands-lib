# The quasi-split unitary group `U(1,1)` has split rank one over `F`: statement

Author: Worker 293. This is statement unit S4 of task
`be70310c-1939-4a82-8293-c4d33f5883ae`. It is a `lean.statement`. A
`lean.proof@1` task proves it.

## The statement

`RankStatement` is a `Prop`-valued definition. It quantifies over fields
`F E : Type u` with `[Algebra F E]` and `[Algebra.IsQuadraticExtension F E]`, a
finite type `κ : Type u`, an `F`-basis `b : Module.Basis κ F (Matrix (Fin 2)
(Fin 2) E)` and `c : E ≃ₐ[F] E` with `c ≠ AlgEquiv.refl`. For such data it
asserts the conjunction of three claims about `G = groupScheme b c`, the group
scheme `U(1,1)` over `Spec (CommRingCat.of F)` of unit 1
(`Langlands.GroupScheme.Examples.QuasiSplitUnitary`, Worker 399):

1. `IsClosedSubgroup (cocharacter b c)`. Here `cocharacter b c` is the
   cocharacter `λ : (Gm (Spec F)).toGrp ⟶ G` of unit 2
   (`Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic`, Worker 399),
   with points `t ↦ diag(t, t⁻¹)`. `IsClosedSubgroup` is the Library
   predicate of `Langlands.GroupScheme.Reductive.Basic`: the underlying
   morphism of schemes is a closed immersion.
2. For every `I : Type u` with `[Finite I]` and every homomorphism
   `i : splitTorus (Spec (CommRingCat.of F)) I ⟶ G` with `IsClosedSubgroup i`,
   `Nat.card I ≤ 1`. `splitTorus S I` is the Library split torus `𝔾ₘ^I` over
   `S` (`Langlands.GroupScheme.Torus.Split`).
3. There are `I : Type u` with `Finite I` and `Nat.card I = 2` and a homomorphism
   `i : splitTorus (Spec (CommRingCat.of E)) I ⟶ baseChangeGroupScheme b c`
   with `IsClosedSubgroup i`. Here `baseChangeGroupScheme b c` is the actual
   pullback
   `(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj G`
   of `Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting` (Worker 293),
   the group scheme `G_E` of deliverable 3.

The index type of the rank-two torus is existential, with `Nat.card I = 2`,
because `splitTorus` takes an index type in the universe `u` of the base scheme.
There is no assumption on the characteristic of `F`, so characteristic `2` is
covered.

## Interpretation

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
Definition 19.20 (printed p.401): the rank of `G` is the dimension of a maximal
torus of `G` over an algebraic closure, and the `k`-rank is the dimension of a
maximal split torus of `G`. By the following remark (printed p.402) the `k`-rank
can change under extension of the base field. Definition 19.22 (printed p.402)
calls a reductive group splittable when it contains a split maximal torus.
Milne 24.40–24.44 (printed pp.523–525) treats unitary groups and their
splitting over a field that splits the centre. The task contract records the
choice of the hermitian form `h(v, w) = v₁ c(w₂) + v₂ c(w₁)` with antidiagonal
Gram matrix as a standard choice.

Over `E` the group `G_E` is isomorphic to `GL₂` (`splittingIso`), whose maximal
tori have dimension two. Thus the maximal tori of `G` have dimension two. In
these terms, claims 1 and 2 say that `G` has `F`-rank one: `λ` gives a split
torus of dimension one, and no closed split torus over `F` has larger
dimension. Claim 3 gives a split torus of dimension two over `E`, so `G` has
absolute rank two. Since its `F`-rank is smaller than its rank, `G` is not split
over `F`. This paragraph is an informal reading only. The Lean statement
contains just the three claims above. It mentions neither maximal tori,
dimensions of tori, the notion of rank nor splitness, and it does not assert
that the rank of `G_E` is at most two.

## Provenance

The three claims are fixed by the task contract (deliverable S4). They are a
derived, explicit form of the rank computation for `U(1,1)`. Claim 1 is the
split torus given by the diagonal cocharacter. Claim 2 is the upper bound on
the `F`-rank. Claim 3 is the image of the diagonal torus of `GL₂` under the
splitting.
