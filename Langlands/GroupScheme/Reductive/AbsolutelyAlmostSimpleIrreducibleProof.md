# Proof: absolute almost-simplicity is irreducibility of the absolute root system

This module proves the Library statement
`Langlands.GroupScheme.AbsolutelyAlmostSimpleIrreducibleStatement` (Conrad, *Reductive group
schemes*, Corollary 5.1.18, p. 150) at every universe `u`, as the theorem
`Langlands.GroupScheme.absolutelyAlmostSimpleIrreducible`. The proof uses no hypotheses beyond
those of the statement. It does not use the nontriviality hypothesis
`SubgroupFunctor.range (𝟙 G) ≠ ⊥`.

The direction `⇒` applies the published irreducibility of the relative root system to the base
change `G_{k̄}`. The direction `⇐` is a new criterion, `isAlmostSimple_of_isIrreducible`, over an
algebraically closed field, followed by descent of almost simplicity from `k̄` to `k`. The
criterion follows Conrad's argument for Proposition 5.1.17 (pp. 148–149): a normal smooth
connected subgroup splits the roots into two mutually orthogonal classes. The Lean route uses
the Library's normal-root dichotomy and a rank-one commutation computation, both described
below.

Throughout, `k : Type u` is a field and `G` is a group scheme over `Spec k` with affine structure
morphism (`[IsAffineHom G.X.hom]`). `T` is a commutative group scheme over `Spec k`. For a
homomorphism `t : T ⟶ G`, `relativeRoots t` and `roots t` are the Library's roots of `t` (the
same set), `relativeRootSpan t` is their rational span in `ℚ ⊗[ℤ] X*(T)`, and
`RelativeRoot.subgroup t α` is the root subgroup functor `U_α` of a character `α`. A root datum
`P` on `X*(T)`, `X_*(T)` realizes `i` when the Library's `IsRootDatumOf i P` holds: the pairing of
`P` is the lattice pairing of characters with cocharacters, the roots of `P` are the roots of
`i`, and every reflection of `P` is induced by a `k`-point of `G` normalizing `i`.

## Helper lemmas on commuting root groups

These three lemmas are in the namespace `RootPairNoncommutation`. They share the following
hypotheses: `hG : IsConnectedReductive G`, `hT : IsSplitTorus T.toGrp` (`T` is a split torus),
`hi : IsMaximalTorus i` for `i : T ⟶ G`, and `hP : IsRootDatumOf i P` for a root datum
`P : RootDatum J X*(T) X_*(T)` with `J : Type u`.

* `zpow_pairing_eq_one_of_commute hG hT hi hP r r' hcomm c hu`. Let `β = P.root r` and
  `β' = P.root r'`, and let `Z` be a scheme over `Spec k`. The hypothesis `hcomm` says that
  every `Z`-point of `U_β` commutes with every `Z`-point of `U_β'` and with every `Z`-point of
  `U_{-β'}`. Let `c` be a global function on `Z` such that `v = 1 + c` is a unit
  (`hu : IsUnit (1 + c)`). The conclusion is `v ^ ⟨β, β'^∨⟩ = 1`, where
  `⟨β, β'^∨⟩ = P.pairing r r'`.

  Proof. The Library's `exists_monic_rootRankOneRelations` gives monic root parametrizations
  `x_β`, `x_{β'}`, `x_{-β'}` and the rank-one relation for `β'`. That relation, at the
  coordinates `1` and `c`, writes the torus point `β'^∨(v)` as a product of points of `U_{β'}`
  and `U_{-β'}` and their inverses (Library lemma `solve_middle`). By `hcomm`, the point
  `x_β(1)` commutes with each factor, hence with `β'^∨(v)`. Conjugation by a torus point `s`
  sends `x_β(1)` to `x_β(β(s))`, and `β(β'^∨(v)) = v ^ ⟨β, β'^∨⟩`. So
  `x_β(1) = x_β(v ^ ⟨β, β'^∨⟩)`. Since `x_β` is a monomorphism, `v ^ ⟨β, β'^∨⟩ = 1`.

* `pairing_eq_zero_of_commute hG hT hi hP r r' hcomm`, with `[Infinite k]`. Here `hcomm` is
  the commutation hypothesis above for every scheme `Z` over `Spec k`. The conclusion is
  `P.pairing r r' = 0`. Take `Z = Spec k`. For every unit `u` of `k`, apply the previous lemma
  with `c = u - 1`, so that `u ^ ⟨β, β'^∨⟩ = 1`. The Library lemma
  `splitTorus.eq_zero_of_forall_units_zpow_eq_one` says that over an infinite field an integer
  exponent killing every unit is zero.

* `commute_of_mem_same_root hG hT hi hP r hx hy`. Any two `Z`-points `x`, `y` of `U_β`, for
  `β = P.root r`, commute. No positive multiple `n β` with `n ≥ 2` is a root (Library lemma
  `hasNoHigherRoots`), so the Library's `commute_of_no_strict_combinations` applies.

## Rational coroots

`coroot'_eq_corootFunctional hT hPZ P hP j r hjr`. Hypotheses: `[LocallyOfFiniteType G.X.hom]`,
`t : T ⟶ G` with `t.hom.hom.left` a monomorphism, `hT : IsSplitTorus T.toGrp`, a root datum `PZ`
on `X*(T)`, `X_*(T)` with `hPZ : IsRootDatumOf t PZ`, and a root pairing
`P : RootPairing J ℚ (relativeRootSpan t) W` whose roots are exactly the rational images of the
roots of `t` (`hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots t`). Let `j` and `r`
be indices with `toRat (PZ.root r) = P.root j` (`hjr`). The conclusion is that the coroot
functional `P.coroot' j` equals `RelativeRootSystem.corootFunctional t (PZ.coroot r)`, the
rational extension of pairing with the integral coroot `PZ.coroot r`.

Proof. The set of roots of `P` is the set of root vectors of `t`. It is finite
(`hT.finite_relativeRoots`) and spans `relativeRootSpan t`
(`rootSpan_eq_top_of_full_relativeRoot_image`). Both functionals take the value `2` on `P.root j`.
Both pre-reflections preserve this set: the reflection of `P` permutes its roots, and the
Library's reflection data of `PZ` (`hPZ.relativeRootReflectionData`, lemma
`mapsTo_preReflection`) sends root vectors to root vectors. Mathlib's
`Module.Dual.eq_of_preReflection_mapsTo` (Bourbaki, *Lie Groups and Lie Algebras*, Ch. VI §1
no. 1, Lemma 1) then gives equality.

Consequently, in the main criterion below, `P.pairing i j` is the integer `PZ.pairing (F i) (F j)`
cast to `ℚ`, where `F` sends each index of `P` to an index of `PZ` with the same root.

## Almost simplicity from an irreducible root system

`isAlmostSimple_of_isIrreducible hG t hsplit hmax P hP hirr`, with `[IsAlgClosed k]`.
Hypotheses: `hG : IsSemisimple G`, `t : T ⟶ G` with `hsplit : IsSplitSubtorus t` and
`hmax : IsMaximalTorus t`, a root pairing `P : RootPairing J ℚ (relativeRootSpan t) W` (`J`, `W`
in any universe) whose roots are exactly the rational images of the roots of `t` (`hP`), and
`hirr : P.IsIrreducible`. The conclusion is `IsAlmostSimple G`.

Proof. The Library's `rootDatumExistence` gives a root datum `PZ` with `IsRootDatumOf t PZ`.
Every index of `P` has the root of some index of `PZ` and conversely (`exists_root_eq_rationalRoot`).
By the previous section, rational pairings of `P` are the integral pairings of `PZ`.
Irreducibility makes `relativeRootSpan t` nontrivial. Since the roots of `P` span it, `P` has an
index `j₀`.

`IsAlmostSimple G` has three parts.

1. Semisimplicity is `hG`.
2. Noncommutativity. If all points of `G` commuted, then `pairing_eq_zero_of_commute` for the
   root of `j₀` with itself would give `2 = 0`. An algebraically closed field is infinite.
3. Normal subgroups. Let `h : H ⟶ G` be a closed subgroup (`IsClosedSubgroup h`) with `H`
   smooth and connected and `SubgroupFunctor.range h` normal. We show
   `SubgroupFunctor.range h = ⊥ ∨ SubgroupFunctor.range h = ⊤`. The Library's `semisimpleNormalRootDichotomy` says that each root
   group `U_α` lies in the image of `h` or centralizes it. Let `A` be the set of indices of `PZ`
   whose root group lies in the image.
   * The complement of `A` is stable under negation of roots. If `β ∉ A` but `-β ∈ A`, then
     `U_{-β}` commutes with `U_β` (since `U_β` centralizes the image, which contains `U_{-β}`)
     and with itself (`commute_of_mem_same_root`). So `pairing_eq_zero_of_commute` gives
     `⟨-β, β^∨⟩ = 0`, contradicting `⟨-β, β^∨⟩ = -2`.
   * Roots in `A` are orthogonal to roots outside `A`. For `α ∈ A` and `β ∉ A`, also `-β ∉ A`,
     so `U_α` (inside the image) commutes with `U_β` and `U_{-β}` (which centralize the image).
     So `⟨α, β^∨⟩ = 0` by `pairing_eq_zero_of_commute`.
   * If `A` is nonempty, let `s` be the corresponding nonempty set of indices of `P`. Every
     root outside the span of `P.root '' s` comes from an index outside `s`, so it is
     orthogonal to all roots in `s`. Mathlib's
     `RootPairing.span_root_image_eq_top_of_forall_orthogonal` (which uses `hirr`) then gives
     that the roots in `s` span everything. An index `j ∉ s` would have its coroot vanishing on
     this span, contradicting `⟨P.root j, P.coroot j⟩ = 2`. So every root group lies in the
     image of `h`, and the Library's root generation `semisimpleRootGeneration` gives
     `SubgroupFunctor.range h = ⊤`.
   * If `A` is empty, every root group centralizes the image of `h`. By
     `fixedSubgroup_eq_top_of_rootGeneration` the centralizer of the image is all of `G`, so
     `H` is commutative. `H` is semisimple (`IsSemisimple.of_normalSubgroup`), and a
     commutative semisimple group is trivial (`IsSemisimple.noncommutative_of_range_ne_bot`).
     So `SubgroupFunctor.range (𝟙 H) = ⊥`, hence `SubgroupFunctor.range h = ⊥`
     (`SubgroupFunctor.range_comp_eq_bot_iff`).

## The main theorem

`absolutelyAlmostSimpleIrreducible : AbsolutelyAlmostSimpleIrreducibleStatement.{u}`.

Let `k`, `G` with `hG : IsSemisimple G`, `T`, a maximal split torus `i` of `G_{k̄}`, `J`, and a
root pairing `P` with evaluation pairing and the roots of `i` be as in the statement. Then
`G_{k̄}` is semisimple (`IsSemisimple.baseChange_toAlgebraicClosure`). Every torus over `k̄` is
split (`toriAreSplit_of_isSepClosed`), so `i` is a maximal torus
(`IsMaximalSplitTorus.isMaximalTorus`).

* `⇒`. `IsAbsolutelyAlmostSimple G` contains `IsAlmostSimple G_{k̄}`. An almost simple group with
  a split maximal torus has a root (`IsAlmostSimple.relativeRoots_nonempty_of_split_maximalTorus`).
  The published `relativeRootSystemIrreducible` (Borel–Tits, Corollary 5.11), applied to
  `G_{k̄}` over the field `k̄`, then gives `P.IsIrreducible`.
* `⇐`. `isAlmostSimple_of_isIrreducible` over `k̄` gives `IsAlmostSimple G_{k̄}`. The Library's
  `IsAlmostSimple.of_fieldExtension` descends this to `IsAlmostSimple G`. Together they give
  `IsAbsolutelyAlmostSimple G`.

The evaluation hypothesis on `P` is not needed in the `⇐` direction; it is passed to
`relativeRootSystemIrreducible` in the `⇒` direction.

## Provenance

The main theorem proves the Library statement, which transcribes Conrad, *Reductive group
schemes* (2014), Corollary 5.1.18, p. 150. The criterion `isAlmostSimple_of_isIrreducible` is the
`⇐` direction of Conrad's Proposition 5.1.17 (pp. 148–149) in the special case of one irreducible
component. The helper lemmas are internal. They are the rank-one computation
`t x_α(c) t⁻¹ = x_α(α(t) c)` with `t = β^∨(v)`, and Bourbaki's uniqueness lemma for coroots
(Ch. VI §1 no. 1, Lemma 1), stated for the Library's objects.
