# Statement: the Hasse principle for reductive groups over `ℚ` with simply connected derived group

Worker 75.

`Langlands.GroupScheme.RationalReductiveHassePrincipleStatement : Prop` is a
statement-only, `Prop`-valued definition with no universe parameters. This
module does not prove it, and it adds no other definitions, theorems or
axioms. It imports:

- [`SimplyConnected.Basic`](../SimplyConnected/Basic.md), for
  `IsSimplyConnected`; through its imports it also brings in
  `IsConnectedReductive` ([`Reductive.Basic`](../Reductive/Basic.md)).
- [`CocycleRelativeTrivialization`](../CocycleRelativeTrivialization.md), for
  `Cocycle.baseChange`. Through its imports it also brings in
  [`TorsorCocycle`](../TorsorCocycle.md), for `Cocycle` and `Cocycle.twist`,
  and the base-change functor `GroupScheme.baseChange`
  ([`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)).
- [`Torus.LatticeGalois`](../Torus/LatticeGalois.md), for `algebraBaseMap`.
- [`Derived.Basic`](../Derived/Basic.md), for `IsDerivedSubgroup`.
- [`Rational.RootSubgroupStructureStatement`](RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`.
- [`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md),
  for `Place` and `placeCompletion`.

## Lean statement

```lean
def RationalReductiveHassePrincipleStatement : Prop :=
  let HassePrinciple : GroupScheme (Spec (CommRingCat.of ℚ)) → Prop := fun H =>
    ∀ (L : Type) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [Algebra.IsSeparable ℚ L]
      (ξ₁ ξ₂ : Cocycle H (Over.mk (algebraBaseMap ℚ L))),
      (∀ i : Langlands.Global.Place ℚ,
        let b := algebraBaseMap ℚ (Langlands.Global.placeCompletion ℚ i)
        let r := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap ℚ L))
        ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap ℚ L)) ⟶
            ((baseChange b).obj H).X,
          ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion ℚ i)))}
            (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap ℚ L))),
            (ξ₂.baseChange b _ r).toFun x y = ((ξ₁.baseChange b _ r).twist f).toFun x y) →
      ∃ f : Over.mk (algebraBaseMap ℚ L) ⟶ H.X,
        ∀ {Z : Over (Spec (CommRingCat.of ℚ))} (x y : Z ⟶ Over.mk (algebraBaseMap ℚ L)),
          ξ₂.toFun x y = (ξ₁.twist f).toFun x y
  ∀ (G D T : GroupScheme (Spec (CommRingCat.of ℚ))) (d : D ⟶ G) (q : G ⟶ T),
    IsConnectedReductive G → IsDerivedSubgroup d → IsSimplyConnected D →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q →
    HassePrinciple T → HassePrinciple G
```

The declaration sits in namespace `Langlands.GroupScheme`. The local `let`
only names the predicate `HassePrinciple`, used twice.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. Here
  `S = Spec ℚ`.
- `IsConnectedReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)):
  `G` is smooth, affine and connected over `ℚ`, and its base change to an
  algebraic closure has trivial unipotent radical.
- `IsDerivedSubgroup d` ([`Derived.Basic`](../Derived/Basic.md)): `d` is a
  closed subgroup (its underlying morphism of schemes is a closed immersion)
  and its range functor equals `derivedSubgroup G`, the intersection, on
  every test scheme, of the ranges of all closed subgroups of `G` whose range
  contains all commutators.
- `IsSimplyConnected D`
  ([`SimplyConnected.Basic`](../SimplyConnected/Basic.md)): `D` is
  semisimple, and every central isogeny `H ⟶ D` from a semisimple group `H`
  over `ℚ` is an isomorphism.
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q`
  ([`Rational.RootSubgroupStructureStatement`](RootSubgroupStructureStatement.md)):
  the underlying morphism of schemes of `q` is flat, surjective and locally
  of finite presentation, and the range of the kernel inclusion `kernelι q`
  equals the range of `d` on every test scheme. So `T` is the fppf quotient
  `G / D`.
- **Cocycles** ([`TorsorCocycle`](../TorsorCocycle.md)). For `U : Over S`,
  `Cocycle H U` gives, for every test object `Z` over `S` and every pair
  `a b : Z ⟶ U`, a point `ξ.toFun a b : Z ⟶ H.X`, natural in `Z` and
  satisfying `ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`. For
  `f : U ⟶ H.X`, `(ξ.twist f).toFun a b = (a ≫ f)⁻¹ * ξ.toFun a b * (b ≫ f)`.
- `algebraBaseMap ℚ L` ([`Torus.LatticeGalois`](../Torus/LatticeGalois.md))
  is `Spec.map` of `algebraMap ℚ L`, so `Over.mk (algebraBaseMap ℚ L)` is
  `Spec L` as a scheme over `Spec ℚ`.
- **Places** ([`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md)).
  `Place ℚ` is `InfinitePlace ℚ ⊕ FinitePlace ℚ`: the archimedean place and
  the nonzero prime ideals of `ℤ` (the ring of integers of `ℚ`).
  `placeCompletion ℚ i` is the completion `ℚ_v` as a `ℚ`-algebra: Mathlib's
  completion at the archimedean place (a copy of `ℝ`), or the adic
  completion `ℚ_p` at a prime `p`.
- **Base change to a completion.** For `b = algebraBaseMap ℚ ℚ_v`,
  `(Over.pullback b).obj (Spec L)` is `Spec (ℚ_v ⊗_ℚ L)` over `Spec ℚ_v`; `r`
  is the counit of the adjunction `Over.map b ⊣ Over.pullback b` at
  `Spec L`, the projection to `Spec L`; and `ξ.baseChange b _ r`
  ([`CocycleRelativeTrivialization`](../CocycleRelativeTrivialization.md)) is
  the cocycle of `H_{ℚ_v}` on `Spec (ℚ_v ⊗_ℚ L)` obtained from `ξ` by
  composing pairs of points with `r`.

## Statement in words

Say that a group scheme `H` over `ℚ` satisfies the Hasse principle for `H^1`
(`HassePrinciple H`) if the following holds. For every finite separable
field extension `L` of `ℚ` and all cocycles `ξ₁`, `ξ₂` of `H` on the cover
`Spec L → Spec ℚ`: if, at every place `v` of `ℚ`, the base changes of `ξ₁`
and `ξ₂` to the cover `Spec (ℚ_v ⊗_ℚ L) → Spec ℚ_v` are cohomologous (one is
a twist of the other), then `ξ₁` and `ξ₂` are cohomologous on `Spec L`.

Let `G` be a connected reductive group over `ℚ`, `d : D ⟶ G` its derived
subgroup, and `q : G ⟶ T` an fppf quotient of `G` by `D`. If `D` is
semisimple and simply connected and `T` satisfies the Hasse principle for
`H^1`, then `G` satisfies the Hasse principle for `H^1`.

## Source

J. S. Milne, *Algebraic Groups: The theory of group schemes of finite type
over a field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page numbers
are printed page numbers; the PDF page is the printed page plus 16.

- Theorem 25.71, p. 565: "Let G be a reductive group over Q. If the derived
  group G′ of G is simply connected and the torus G/G′ satisfies the Hasse
  principle for H^1, then G satisfies the Hasse principle for H^1." Proof:
  "Let T = G/G′. The theorem follows from a diagram chase in" a diagram
  relating `T(ℚ)`, `H^1(ℚ, G′)`, `H^1(ℚ, G)`, `H^1(T)`, `G(ℝ)`, `T(ℝ)`,
  `H^1(ℝ, G′)`, `∏_v H^1(ℚ_v, G)` and `∏_v H^1(ℚ_v, T)`, "and its twists
  (in the sense of Serre 1997, I, 5.4 and 5.5)." The next sentence reads:
  "Theorems 25.70 and 25.71 can be extended to groups over number fields by
  using Shapiro's lemma (3.44)."
- p. 563: "A group G for which the map (169) is injective is said to
  satisfy the Hasse principle for H^1." The map (169), p. 562, is the
  canonical map `H^1(k, G) → ∏_v H^1(k_v, G)` of Theorem 25.64.
- "Global fields", p. 562: "We let V denote the set of primes (possibly
  infinite) of a global field k, and k_v the completion of k at a v ∈ V."
- Section 25g, p. 559: "In this section, we write H^1(k, G) for the flat
  cohomology group (2.72)." Example 2.72, p. 61: "The torsors under G_{R_0}
  over R_0 having an R-point are classified by the cohomology set
  H^1(R/R_0, G) of the complex G(R) → G(R ⊗_{R_0} R) →
  G(R ⊗_{R_0} R ⊗_{R_0} R)", for a faithfully flat `R_0`-algebra `R`.
  Proposition 2.69, p. 60, transfers affineness from `G` to its torsors.
- Definition 6.16, p. 129: "The derived group of G is the intersection of
  the normal algebraic subgroups N of G such that G/N is commutative. It is
  denoted DG (or G^der or G′)."
- 6.46, p. 135: "A connected group variety over a field k is said to be
  reductive if G_{k^a} is reductive, i.e., if its geometric unipotent
  radical R_u(G_{k^a}) is trivial."
- Conventions, p. 4: "After p. 162, all algebraic groups are affine."
  Chapter 25 opening, p. 544: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (in the project literature folder, registered as
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; the PDF page
is the printed page plus 11) has Theorem 25.71 on printed p. 568 with the
same wording, the same proof and the same following sentence.

Errata. The errata snapshot of 2026-11-02 for the 2017 book (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 4, 61, 129, 135, 544, 559, 562 or 565. Its p. 563 entry
concerns Theorems 25.66 to 25.69, not the sentence defining the Hasse
principle, and its p. 60 entry asks to define torsors over nonaffine bases
(the bases here are affine). The errata snapshot of 2026-11-04 for the 2022
reprint (source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed p. 568. Its entry headed "p.563. Section g" says: "I
sometimes write "cohomology group" for "cohomology set" (G is usually
noncommutative)"; so the Hasse principle is injectivity of a map of pointed
sets, not only triviality of its kernel.

## Derivation from the source (provenance: derived)

- **Base field.** The statement is over `ℚ`, as in Milne. The extension to
  number fields that Milne mentions after the proof is not stated.
- **Reductive group.** Milne's reductive groups are connected group
  varieties (6.46) and are affine (p. 4, p. 544). `IsConnectedReductive G`
  includes smoothness, affineness and connectedness.
- **Derived group.** `IsDerivedSubgroup d` exhibits `D` as the derived group
  of `G`; see [`Derived.Basic`](../Derived/Basic.md) for the comparison of
  `derivedSubgroup` with Milne's Definition 6.16 and Proposition 6.18. "The
  derived group G′ of G is simply connected" is `IsSimplyConnected D`, which
  includes semisimplicity of `D`.
- **The torus `G/G′`.** Milne's `G/G′` is the quotient of `G` by `G′`. The
  statement takes any group `T` with an fppf quotient map `q : G ⟶ T` whose
  kernel is `D`. Milne calls `G/G′` a torus; the statement does not assume
  that `T` is a torus, so it imposes no extra hypothesis.
- **Hasse principle for `H^1`.** `HassePrinciple H` is the injectivity of
  the map (169) for `H`, written with cocycles on finite separable covers of
  `Spec ℚ`, exactly as in the companion statement
  `NumberFieldHassePrincipleStatement` (Milne 25.64, a separate candidate).
  Every finite extension of `ℚ` is separable, so the separability instance
  is automatic. The two descriptions agree for affine `H` of finite type,
  in particular for `G` and for `T`, by these facts, which are standard and
  are not proved in this module. A torsor under `H` over `ℚ` (or over `ℚ_v`)
  is nonempty, affine and of finite type, so it has a point over a finite
  extension. By 2.72, cocycles on a faithfully flat cover
  `Spec R → Spec R_0`, up to twisting, correspond to torsors with an
  `R`-point, up to isomorphism. The cocycle `ξ.baseChange` describes the
  base-changed torsor. `ℚ_v ⊗_ℚ L` is a nonzero finite product of fields
  finite separable over `ℚ_v`. Hence, if (169) is injective, locally
  cohomologous cocycles describe torsors that are isomorphic locally, hence
  globally, so they are cohomologous; conversely two torsors with the same
  local classes have points over a common finite extension `L` (a
  compositum), and `HassePrinciple H` applied to their cocycles on `Spec L`
  shows that they are isomorphic.
- **Places.** `Place ℚ` lists the archimedean place and every prime once,
  with completions `ℝ` and `ℚ_p`; this is Milne's set `V` with the
  completions `k_v`.
- **No universe parameter.** `ℚ` and the extensions `L` are in `Type`.

Sanity check. If `G` is a torus, its derived group is trivial, the trivial
group is semisimple and simply connected, and `q` is an isomorphism; the
statement then says that the Hasse principle passes along an isomorphism.
If `G = GL_n`, then `D = SL_n` and `T = 𝔾_m` via the determinant; here both
`H^1(ℚ, GL_n)` and `H^1(ℚ, 𝔾_m)` are trivial by Hilbert's Theorem 90, so the
hypothesis and the conclusion both hold.

## Relation to the Library

- `Langlands.GroupScheme.NumberFieldHassePrincipleStatement` (module
  `Rational/NumberFieldHassePrincipleStatement`; Milne 25.64, submitted as a
  separate candidate and not yet in the Library) states the Hasse principle
  for simply connected, adjoint and orthogonal groups over number fields,
  with the same cocycle formulation.
- `CocenterQuotientExistenceStatement`
  ([`Derived.CocenterQuotientStatement`](../Derived/CocenterQuotientStatement.md))
  states that a connected reductive group over a field has an fppf quotient
  by its derived subgroup that is a torus.

## For the later proof (not part of this unit)

Milne's proof is a diagram chase in the diagram described above, in which the
arrow `T(ℚ) → T(ℝ)` is marked "dense image", and in its twists in the
sense of Serre, *Galois cohomology* (1997), I, 5.4 and 5.5.
