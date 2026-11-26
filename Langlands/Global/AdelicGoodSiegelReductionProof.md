# Good Siegel reduction for connected reductive groups over number fields: proof

This module proves the Library proposition
`Langlands.Global.AdelicSiegelFactors.AdelicGoodSiegelReductionStatement` (module
`Langlands.Global.AdelicSiegelFiniteVolume`) and derives from it the original
`Langlands.Global.AdelicSiegelFactors.AdelicSiegelReductionStatement` (module
`Langlands.Global.AdelicSiegelReductionStatement`). It also proves the compact-subgroup
statement `AdelicCompatibleIwasawaCompactStatement` (module
`Langlands.Global.AdelicCompatibleIwasawaCompact`) outright. All three theorems have no
hypotheses, are universe-polymorphic in `u`, and use every input in the same universe `u`.
Their axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Theorems

All three are in the namespace `Langlands.Global.AdelicSiegelFactors`.

```text
theorem adelicCompatibleIwasawaCompact : AdelicCompatibleIwasawaCompactStatement.{u}
theorem adelicGoodSiegelReduction : AdelicGoodSiegelReductionStatement.{u}
theorem adelicSiegelReduction : AdelicSiegelReductionStatement.{u}
```

### What `adelicGoodSiegelReduction` says

Let `F : Type u` be a number field. Let `G` be a group scheme over `Spec F` with
`IsAffineHom G.X.hom`, `LocallyOfFiniteType G.X.hom` and `IsConnectedReductive G`. Then
there exist a commutative group scheme `T`, a map `i : T → G`, a cocharacter `ν` of `T`, a
commutative group scheme `T₀` and a map `j : T₀ → T` with
`IsSiegelAlgebraicSetup F G T i ν T₀ j`. Concretely, `i` is a maximal split torus, `ν` is
generic, `P = Standard.parabolicScheme i ν ∅` is a minimal parabolic with rational Levi
`M = Standard.leviScheme i ν ∅` and geometric unipotent radical
`N = Standard.unipotentScheme i ν ∅`, the standard Levi subgroup functor equals the
centralizer of `T`, the relative roots of `T` on `P` (the nonzero weights on `Lie P`) are
the positive relative roots of `ν`, `j ≫ i` factors as a maximal split torus `T₀ → D` of
the derived subgroup `D` followed by `D → G`, and for some `Z₀ → T` whose composite with
`i` is a split component of `G`, the multiplication `T₀ × Z₀ → T` is scheme-surjective.
These are the clauses of the unchanged Library predicate.
Further, there exist compact factor data `C` (a compact set `Ω_N ⊆ N(𝔸_F)`, a compact set
`Ω_M ⊆ M(𝔸_F)¹` and a compact subgroup `K` of `G(𝔸_F)`) and a threshold `t : ℝ≥0ˣ` such
that

- `IsSiegelCover F G T i ν T₀ j C t`: `K` is maximal compact with `P(𝔸_F) K = G(𝔸_F)`
  (`IsParabolicIwasawaCompact`), and the principal rational points on the left times the
  ordered weak Siegel product `Ω_N Ω_M A_{T₀}(t) K` is exactly `G(𝔸_F)¹`. Here
  `A_{T₀}(t)` is the image under `positiveMap F G T i T₀ j` of the points `a` of the
  intrinsic positive torus with `t ≤ |α(a)|` for every simple relative root `α`, where
  `|·|` is the normalized idelic norm;
- `IsPositiveTorusCompatible F G T i ν T₀ j K`: every element of `K` lying in the image of
  `P(𝔸_F)` commutes with every element of the image of `positiveMap F G T i T₀ j`.

No hypothesis restricts `F` or `G` further: the theorem covers every number field, split,
nonsplit and anisotropic groups, and groups with empty relative root system, where the
chamber condition is vacuous.

## Proofs

### `adelicCompatibleIwasawaCompact`

The published `adelicCompatibleIwasawaCompactStatement_of_local` (module
`Langlands.Global.AdelicCompatibleIwasawaCompact`) derives
`AdelicCompatibleIwasawaCompactStatement` from three local statements. The proof applies
it to their published proofs:

- `InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement` (module
  `Langlands.Global.InfinitePlaceLeviIwasawaProof`): at every infinite place, for a
  rational parabolic and a rational Levi of it, a maximal compact subgroup with the
  parabolic Iwasawa decomposition whose intersection with the parabolic equals its
  intersection with the Levi, and whose pullback to the Levi is maximal compact;
- `FinitePlaceGroupPoints.parabolicIwasawaStatement` (module
  `Langlands.Global.FinitePlaceIwasawaProof`): at every finite place, a compact subgroup,
  maximal among compact subgroups, with the parabolic Iwasawa decomposition; the proof
  there takes the norm-one stabilizer of a special point of the Bruhat–Tits building;
- `IntegralIwasawaFamily.existenceStatement` (module
  `Langlands.Global.IntegralIwasawaFamilyProof`): a family of subgroups of the
  finite-completion points that are maximal compact with the parabolic Iwasawa
  decomposition at almost every finite place, contain almost all components of every
  finite adelic point, and are uniformly integral on every regular function.

Inside `adelicCompatibleIwasawaCompactStatement_of_local`, the local subgroups are patched
into the coordinate subgroup `K = ∏_v K_v` of `G(𝔸_F)`, which is maximal compact with
`P(𝔸_F) K = G(𝔸_F)`. Its positive-torus compatibility is
`isPositiveTorusCompatible_coordinateSubgroup` (module
`Langlands.Global.AdelicPositiveTorusCompatibility`). That proof compares components at
every place. At a finite place, the image of `positiveMap` has trivial component. At an
infinite place, a parabolic element of the local compact lies in the minimal Levi, and the
minimal Levi centralizes the split torus.

### `adelicGoodSiegelReduction`

Fix `F`, `G` and `hG : IsConnectedReductive G`.

1. The published `siegelAlgebraicSetupExistence` (module
   `Langlands.Global.AdelicSiegelSetupExistenceProof`) gives `T, i, ν, T₀, j` and
   `hS : IsSiegelAlgebraicSetup F G T i ν T₀ j`.
2. `adelicCompatibleIwasawaCompact`, applied to this setup, gives a subgroup `K` of
   `G(𝔸_F)` with `IsParabolicIwasawaCompact F G P (Standard.parabolicHom i ν ∅) K` and
   `IsPositiveTorusCompatible F G T i ν T₀ j K`.
3. The published `exists_isSiegelCover_of_chamber` (module
   `Langlands.Global.AdelicSiegelChamberReduction`) takes Springer's compactness theorem,
   the chamber form of the fundamental set theorem, the setup and any Iwasawa compact `K`.
   It returns compact factors `C` with `C.compactSubgroup = K` and a threshold `t` with
   `IsSiegelCover F G T i ν T₀ j C t`. The two theorems it needs are supplied by their
   published proofs:
   - `centralSplitCompactQuotient : CentralSplitCompactQuotientStatement` (module
     `Langlands.Global.AdelicSpringerCentralCompactnessProof`). Applied to the minimal
     Levi `M`, in which the lift of `T` is a central maximal split torus, it gives a
     compact set `Ω_M ⊆ M(𝔸_F)¹` meeting every coset `M(F) m`;
   - `adelicSiegelChamberReduction : AdelicSiegelChamberReductionStatement` (module
     `Langlands.Global.AdelicSiegelChamberReductionProof`), which gives the threshold `t`
     and the factorization `γ g = n m a k` with `a` in the weak chamber.

   The compact set `Ω_N` comes from the compactness of the unipotent rational quotient,
   which `exists_isSiegelCover_of_chamber` obtains from published proofs.
4. Since `C.compactSubgroup = K`, substituting `K` turns the compatibility of `K` from
   step 2 into the compatibility of `C.compactSubgroup`. The witnesses
   `T, i, ν, T₀, j, hS, C, t` together with the cover and the compatibility prove the
   target.

The point of step 3 is that `exists_isSiegelCover_of_chamber` keeps the given compact
subgroup, so the compatibility chosen in step 2 survives into the conclusion.

### `adelicSiegelReduction`

The published `adelicSiegelReductionStatement_of_good` (module
`Langlands.Global.AdelicSiegelFiniteVolume`) forgets the compatibility clause. Applied to
`adelicGoodSiegelReduction` it gives `AdelicSiegelReductionStatement`.

## Sources

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  registered as `getz-hahn-2024-automorphic-representations` (SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), §2.7, printed
  pp. 71–72 (PDF pp. 88–89): Theorem 2.7.1 (the Iwasawa decomposition with a maximal
  compact `K`), the setup preceding (2.25), the Siegel sets (2.25)–(2.26) and
  Theorem 2.7.2 (`G(F) S(t) = G(𝔸_F)¹`). The theorem `adelicSiegelReduction` is the
  Library form of Theorem 2.7.2, with rational points on the left as in the Library
  statement.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition` (folder SHA-256
  `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`), I.1.4, printed
  p. 4, conditions (i)–(ii): the choice of `K` behind the compatibility clause, as derived
  in `AdelicSiegelFiniteVolume.md`.

The proof in this module does not follow either text step by step. It composes the
Library theorems above, whose own Markdown pages describe their routes and sources.
