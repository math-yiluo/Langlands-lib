# Rosenlicht's criterion for split solvable groups: proof

`Langlands.GroupScheme.rosenlichtSplitSolvable` proves the published proposition
[`RosenlichtSplitSolvableStatement.{u}`](RosenlichtSplitStatement.md) exactly, in
every universe `u`. The statement's Lean/Markdown pair and everything it imports
are unchanged. The theorem uses no hypothesis beyond the statement's own, and no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

The statement: let `k : Type u` be a field, `S = Spec (CommRingCat.of k)`, and
`G : GroupScheme S` with `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and
`IsSolvableGroupScheme G`. Suppose some morphism of `S`-schemes
`φ : (splitTorus S (ULift.{u} (Fin n))).X ⟶ G.X` has dominant underlying
morphism `φ.left`. Then `IsSplitSolvableGroupScheme G`.

## Implemented proof

The module proves one new lemma and then composes it with published Library
theorems. All of those theorems are unconditional.

### The new lemma: making the parametrization pointed

`hasPointedSplitTorusDomination_of_dominant` takes a split torus `P` over `S`
(`IsSplitTorus P`) and a morphism `φ : P.X ⟶ G.X` of `S`-schemes with
`IsDominant φ.left`. It proves `HasPointedSplitTorusDomination G`
([`TorusDominationBaseChange`](Rational/TorusDominationBaseChange.md)), which
asks for a split torus and a dominant scheme morphism from it to `G` that sends
the identity point to the identity point. The statement's `φ` need not do this.
This is the first step of Milne's multiplicative-type case ("after composing φ
with a translation, we may suppose that φ(e) = e").

Let `g = 1 ≫ φ` be the image of the identity point of `P`, a `k`-point of `G`.
The proof uses the right translation automorphism
`G.rightTranslationIso g⁻¹` of the scheme `G.X`
([`FlagInvariantAffineOpenCoverReduction`](Absolute/FlagInvariantAffineOpenCoverReduction.md)).
The new parametrization is `φ ≫ (G.rightTranslationIso g⁻¹).hom`, with the same
split torus `P`.

- **Dominance.** The underlying morphism is `φ.left` followed by the underlying
  morphism of an isomorphism in `Over S`. That morphism is an isomorphism of
  schemes (the image of the isomorphism under `Over.forget`), hence dominant, and
  a composite of dominant morphisms is dominant.
- **Pointedness.** By `comp_rightTranslation`, `g ≫ G.rightTranslation g⁻¹` is
  the product of `g` with the constant point `G.constantPoint g⁻¹` at the
  terminal test object. By `constantPoint_self`
  ([`HomConjugacy`](HomConjugacy.md)) that constant point is `g⁻¹`, and
  `g * g⁻¹ = 1`.

### The main theorem

`rosenlichtSplitSolvable` applies the lemma to the split torus
`splitTorus S (ULift.{u} (Fin n))` (split by `isSplitTorus_splitTorus`,
[`Torus.Split`](Torus/Split.md)) and the statement's `φ`. Call the result
`hdom : HasPointedSplitTorusDomination G`. The proof then runs as follows.

1. **Connectedness.** `hdom.hasPointedTorusDomination.connectedSpace`
   ([`TorusDominationBaseChange`](Rational/TorusDominationBaseChange.md)) gives
   `ConnectedSpace G.X.left`. The underlying space of a torus is connected, and
   the dense image of a connected space is connected.
2. **Torus quotient with unipotent kernel.** The published reduction
   `splitTorusDominatedSolvableQuotient_of_solvableTorusQuotient`
   ([`SplitTorusDominatedSolvableQuotientReduction`](Rational/SplitTorusDominatedSolvableQuotientReduction.md))
   takes as its premise the published theorem `solvableTorusQuotient`
   ([`SolvableTorusQuotientProof`](Absolute/SolvableTorusQuotientProof.md)). It
   proves `SplitTorusDominatedSolvableQuotientStatement`
   ([statement](Rational/SplitTorusDominatedSolvableQuotientStatement.md)).
   Applied to the smooth, affine, connected, solvable `G` and `hdom`, it gives
   group schemes `U`, `D` over `S` and homomorphisms `i : U ⟶ G`, `q : G ⟶ D`
   with these properties: `i` is a closed subgroup (`IsClosedSubgroup i`); `U`
   is smooth, connected and unipotent; `q` is a represented fppf quotient by the
   range of `i` (`RelativeRoot.IsFppfQuotient`); and `D` is a torus
   (`IsTorus D`). Internally, the reduction applies `solvableTorusQuotient` to
   the base change of `G` to `AlgebraicClosure k`. It descends the resulting
   quotient map onto a split torus to `k`, using the pointed split-torus
   domination, and takes `U` to be the kernel of the descended map.
3. **The kernel is split unipotent.**
   `TorusKernelDomination.representative_isSplitUnipotent_of_stableVector`
   ([`TorusGeneratedSplitGeometricRadicalAssembly`](Rational/TorusGeneratedSplitGeometricRadicalAssembly.md))
   gives `RelativeRoot.IsSplitUnipotent U`. Its two premises are the published
   theorems `unipotentSplitTorusDomination`
   ([`SplitTorusDominationProof`](Rational/SplitTorusDominationProof.md)) and
   `RelativeRoot.splitUnipotentStableVectorSubgroup`
   ([`SplitUnipotentStableVectorProof`](Rational/SplitUnipotentStableVectorProof.md)).
   Its other arguments are the data from step 2 and `hdom`.
4. **The quotient torus is split.** The quotient map `q` is surjective (part of
   `IsFppfQuotient`), so its underlying morphism is dominant.
   `hdom.postcomp q`
   ([`SplitTorusDominationOperations`](Rational/SplitTorusDominationOperations.md))
   gives `HasPointedSplitTorusDomination D`. Then
   `HasPointedSplitTorusDomination.isSplitTorus`
   ([`SplitOfDomination`](Torus/SplitOfDomination.md)) gives `IsSplitTorus D`.
   This is Milne's multiplicative-type case: a torus that receives a pointed
   dominant map from a split torus is split.
5. **Assembling the series.**
   `IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient`
   ([`SplitSolvableSmoothExtension`](SplitSolvableSmoothExtension.md)) joins a
   split unipotent series of the closed smooth connected kernel `U` with the
   split series of the split torus `D`, and concludes
   `IsSplitSolvableGroupScheme G`. Its instance arguments are smoothness,
   affineness and connectedness of `G` and `U`. Smoothness and connectedness of
   `U` come from step 2. `IsAffineHom U.X.hom` holds because the structure
   morphism of `U` factors as the closed immersion `i` (affine) followed by the
   affine structure morphism of `G`.

## Relation to the original proof

The statement is Milne, *Algebraic Groups* (2017), Theorem 16.58 (Rosenlicht),
printed p.345 (source ID `milne-2017-algebraic-groups`). Milne first treats
three special cases: multiplicative type, commutative unipotent in
characteristic zero, and elementary unipotent in characteristic `p` (through the
module of additive polynomials and Proposition 14.50). He then argues by
induction on `dim G`. The derived group is again dominated by a split torus
(6.20a), which reduces the problem to commutative `G`; that case is split into
its multiplicative and unipotent parts (16.13) and, in characteristic `p`, by
the `p`-power map.

The Lean proof takes a different route. It does not use induction on dimension
or the derived group. In one step it splits `G` as an extension of a torus `D`
by the smooth connected unipotent kernel `U`, obtained by descending the torus
quotient of `G` over the algebraic closure (step 2). Splitness of `U` comes from the
published unipotent case of the criterion, `unipotentSplitTorusDomination`
(step 3). Only Milne's multiplicative-type argument appears directly, in the
translation lemma and in step 4.
