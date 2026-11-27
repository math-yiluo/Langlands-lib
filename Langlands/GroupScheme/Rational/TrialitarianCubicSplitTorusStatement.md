# Statement: a maximal torus split by the cubic field in an anisotropic trialitarian group

`Langlands.GroupScheme.TrialitarianCubicSplitMaximalTorusStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition with one universe parameter `u`, in the namespace
`Langlands.GroupScheme`. The module
`Langlands.GroupScheme.Rational.TrialitarianCubicSplitTorusStatement` does not prove it, and it
adds no other definitions, theorems or axioms. It imports:

- [`Reductive.AbsolutelyAlmostSimple`](../Reductive/AbsolutelyAlmostSimple.md), for
  `IsAbsolutelyAlmostSimple`.
- [`Reductive.TitsIndex`](../Reductive/TitsIndex.md), for `TitsIndexData`, its simple vertices
  `Vertex`, its Cartan pairings `cartan` and its star action `star`.
- [`SimplyConnected.Basic`](../SimplyConnected/Basic.md), for `IsSimplyConnected`.
- [`Rational.SplitTorus`](SplitTorus.md), for `IsAnisotropic`.
- Mathlib's `Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex`, for
  `NumberField.IsTotallyComplex`.

Through these imports the statement also uses the Library's `IsMaximalTorus`, `IsSplitTorus`,
the base-change functors `GroupScheme.baseChange` and `CommGroupScheme.baseChange`, and
`algebraBaseMap`.

## Lean statement

```lean
def TrialitarianCubicSplitMaximalTorusStatement : Prop :=
  ∀ (F K : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F] [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K], Module.finrank F K = 3 →
    ∀ (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom H.X.hom]
      [LocallyOfFiniteType H.X.hom] (d : TitsIndexData H) (q : d.Vertex ≃ Fin 4),
      IsSimplyConnected H → IsAbsolutelyAlmostSimple H → IsAnisotropic H →
      (∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b)) →
      (∀ a : d.Vertex, q a ≠ 1 →
        ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
      (∃ (S : CommGroupScheme (Spec (CommRingCat.of K)))
        (s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj H),
          IsMaximalTorus s ∧ IsSplitTorus S.toGrp) →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ H),
        IsMaximalTorus t ∧
          IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj T).toGrp
```

## Objects and predicates used

- **Fields.** `F` is a number field with `NumberField.IsTotallyComplex F` (every infinite place
  is complex), and `K` is a Galois extension of `F` of degree `3`, in the same universe.
- **The group.** `H` is a group scheme over `Spec F` (`GroupScheme S` is `Grp (Over S)`), with
  affine and locally finite-type structure morphism. `IsSimplyConnected H`
  ([`SimplyConnected.Basic`](../SimplyConnected/Basic.md)) includes semisimplicity and connected
  reductivity. `IsAbsolutelyAlmostSimple H` means that `H` is almost simple and stays so over
  the algebraic closure.
- **Anisotropy.** `IsAnisotropic H` ([`Rational.SplitTorus`](SplitTorus.md)) says that the split
  rank `splitRank H` is `0`: no closed subgroup of `H` over `F` is a nontrivial split torus.
- **The type.** `d : TitsIndexData H` is index data of `H` (a pinning over the separable closure
  of `F`, a maximal `F`-split torus and a compatible positivity); `d.cartan a b` is the integral
  pairing of the simple roots `a` and `b`, and `d.star σ` is the star action of `σ` in the
  absolute Galois group on the simple vertices. Under `q : d.Vertex ≃ Fin 4` the pairings are
  those of Mathlib's `CartanMatrix.D 4`, whose off-diagonal entries are `-1` exactly for the
  pairs `{0, 1}`, `{1, 2}`, `{1, 3}`. Vertex `1` is the centre and `0`, `2`, `3` are the leaves.
  The leaf hypothesis says that no leaf is fixed by the full star action.
- **Splitting over `K`.** The hypothesis on `K` asks for a commutative group scheme `S` over
  `Spec K`, a homomorphism `s` from `S` to the base change `H_K` of `H` along `Spec K → Spec F`
  with `IsMaximalTorus s`, and `IsSplitTorus S`: `H_K` has a split maximal torus.
- **Conclusion.** There is a commutative group scheme `T` over `Spec F` and a homomorphism
  `t : T ⟶ H` with `IsMaximalTorus t`, whose base change `T_K` along `Spec K → Spec F` is a
  split torus.

## Statement in words

Let `F` be a totally imaginary number field, `K/F` a Galois extension of degree three, and `H`
an anisotropic, simply connected, absolutely almost-simple group over `F` of type `D₄` whose
star action fixes no leaf of the Dynkin diagram. If `H` is split over `K`, then `H` has a
maximal torus defined over `F` that splits over `K`.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Pure and Applied
Mathematics 139, Academic Press, 1994, source ID
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`. Printed page `p` is page
`p + 10` of the PDF file, counting its first page as page `1`.

- §6.8, printed p. 371, "Groups of types ³,⁶D₄": for `K` a totally imaginary number field and
  `G = _ξ G₀` with `G₀` quasi-split, "Now suppose G is K-anisotropic. Let L denote the minimal
  Galois extension of K over which G₀ becomes an inner form. Then 𝒢 = Gal(L/K) is either
  cyclic of order 3, or the symmetric group S₃. Let us examine the first case. Since G₀ becomes
  a group of type ¹D₄ over L, by what we have already proved H¹(L, G₀) = 1; hence G ≃ G₀ is a
  split group over L."
- Printed p. 372: with `P` the parabolic `L`-subgroup of the simple roots `{α₂, α₃, α₄}`, `σ` a
  generator of `𝒢` and `C = P ∩ σ(P) ∩ σ²(P)`, the source shows that `C = HS` with `H` of type
  `A₂` and `S` an `L`-split two-dimensional `K`-torus, that `H = SL₁(D)` for a division algebra
  `D` of index `3` over `K` split by `L`, and concludes: "The latter implies that L can be
  embedded in D and consequently defines a maximal L-split K-torus S' = R⁽¹⁾_{L/K}(G_m) ⊂ H.
  Then T = SS' is a maximal K-torus of C and G which is anisotropic over K and split over L."

## Derivation from the source (provenance: derived)

The statement is the conclusion quoted from printed p. 372 in the cyclic case, written in the
Library's language; the source's `K`, `L` and `G` are `F`, `K` and `H` here.

- **Field and degree.** The source's base field is a totally imaginary number field, which is
  `NumberField.IsTotallyComplex F`. In the cyclic case the source's `L` is a Galois extension of
  degree `3`, which is `IsGalois F K` with `Module.finrank F K = 3`. The statement does not
  require `K` to be the minimal extension over which `H` becomes an inner form; the hypotheses
  force this. Indeed, the star action is trivial on the absolute Galois group of `K` because
  `H_K` is split, so it factors through `Gal(K/F)`, which is cyclic of order three. By the leaf
  hypothesis it is nontrivial, so it permutes the three leaves cyclically.
- **Group.** The source's group is simply connected, absolutely almost simple of type `³D₄` and
  `K`-anisotropic. As in the Library statement
  `TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement`
  ([`Rational.TotallyComplexQuasiSplitTrialitarian`](TotallyComplexQuasiSplitTrialitarian.md)),
  type `D₄` with a star action fixing no leaf is expressed by the Cartan comparison with
  `CartanMatrix.D 4` and the leaf hypothesis; this covers `³D₄` and `⁶D₄`, and the splitting
  hypothesis over the cubic Galois field leaves only `³D₄`.
- **Splitting over `K`.** The source derives "G is a split group over L" from the vanishing of
  `H¹(L, G₀)`. The statement takes the splitting of `H_K` as a hypothesis: a split maximal torus
  of `H_K`.
- **Conclusion.** "A maximal K-torus of … G … split over L" is a maximal torus `t : T ⟶ H`
  over `F` whose base change to `K` is a split torus. Anisotropy of `T`, also asserted in the
  source, follows from anisotropy of `H` and is not part of the conclusion.
