# Quadratic opposite minimal parabolics and cocycle reduction to their Levi subgroups

The module `Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeMinimalParabolicLevi`
contains two `Prop`-valued definitions in namespace `Langlands.GroupScheme`, both with one
universe parameter `u`:

- the predicate `IsQuadraticOppositeMinimalParabolicLevi`, and
- the statement `NumberFieldQuadraticOppositeMinimalParabolicLeviStatement.{u}`.

The module states the result and does not prove it. It adds no theorems or axioms.

## Imports

- [`CocycleBaseChangeTriviality`](../CocycleBaseChangeTriviality.md), for
  `Cocycle.baseChangePullback`, and through its imports `Cocycle`, `Cocycle.map` and
  `Cocycle.IsTrivial` from [`TorsorCocycle`](../TorsorCocycle.md).
- [`CocycleCohomology`](../CocycleCohomology.md), for `Cocycle.Cohomologous`.
- [`GaloisCocycle`](../GaloisCocycle.md), for the field cover `GaloisCocycle.cover`.
- [`Rational.UnipotentRadicalGalois`](UnipotentRadicalGalois.md), for the Galois translate
  `radicalGaloisHom` of a subgroup inclusion, and through its imports `algebraBaseMap` and
  `SubgroupFunctor.range`.
- [`Rational.MinimalParabolic`](MinimalParabolic.md), for `IsMinimalParabolicSubgroup`.
- [`Rational.LeviSubgroup`](LeviSubgroup.md), for `IsRationalLeviSubgroup`.
- [`Reductive.Semisimple`](../Reductive/Semisimple.md), for `IsSemisimple`.
- [`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md), for
  `Global.placeCompletion`.
- Mathlib's `NumberTheory.NumberField.InfinitePlace.TotallyRealComplex`, for
  `NumberField.IsTotallyComplex`.

`IsClosedSubgroup` (module [`Reductive.Basic`](../Reductive/Basic.md)) is available through
these imports.

## Lean definitions

```lean
variable {F : Type u} [Field F] (Q : Type u) [Field Q] [Algebra F Q]
  {G C : GroupScheme (Spec (CommRingCat.of F))}

def IsQuadraticOppositeMinimalParabolicLevi (t : C ⟶ G) : Prop :=
  Module.finrank F Q = 2 ∧ IsClosedSubgroup t ∧
  ∃ (σ : Q ≃ₐ[F] Q) (P : GroupScheme (Spec (CommRingCat.of Q)))
    (j : P ⟶ (GroupScheme.baseChange (algebraBaseMap F Q)).obj G)
    (l : (GroupScheme.baseChange (algebraBaseMap F Q)).obj C ⟶ P),
    σ ≠ 1 ∧ IsMinimalParabolicSubgroup j ∧ IsRationalLeviSubgroup l ∧
    l ≫ j = (GroupScheme.baseChange (algebraBaseMap F Q)).map t ∧
    SubgroupFunctor.range j ⊓ SubgroupFunctor.range (radicalGaloisHom j σ) =
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F Q)).map t)

def NumberFieldQuadraticOppositeMinimalParabolicLeviStatement : Prop :=
  ∀ (F Q : Type u) [Field F] [NumberField F] [Field Q] [Algebra F Q]
    [FiniteDimensional F Q] [IsGalois F Q] [IsTotallyComplex Q]
    (_ : Module.finrank F Q = 2) (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSemisimple G →
    ∃ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
      IsQuadraticOppositeMinimalParabolicLevi Q t ∧
      ∀ ξ : Cocycle G (GaloisCocycle.cover F Q),
        (∀ w : InfinitePlace F, w.IsReal →
          (ξ.baseChangePullback
            (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial) →
        ∃ δ : Cocycle C (GaloisCocycle.cover F Q), (δ.map t).Cohomologous ξ ∧
          ∀ w : InfinitePlace F, w.IsReal →
            (δ.baseChangePullback
              (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial
```

In `IsQuadraticOppositeMinimalParabolicLevi` the field `F` is implicit (it is read off from
the type of `t`) and `Q` is explicit.

## Objects and predicates used

- **Group schemes and base change.** `GroupScheme S` is `Grp (Over S)`. For a field
  extension `Q/F`, `algebraBaseMap F Q : Spec Q ⟶ Spec F` is `Spec` of `algebraMap F Q`, and
  `(GroupScheme.baseChange (algebraBaseMap F Q)).obj G` is the base change `G_Q`; `.map t` is
  the base change `t_Q : C_Q ⟶ G_Q` of a homomorphism.
- **Closed subgroups.** `IsClosedSubgroup t` ([`Reductive.Basic`](../Reductive/Basic.md)):
  the underlying morphism of schemes of `t` is a closed immersion.
- **Minimal parabolic subgroups.** `IsMinimalParabolicSubgroup j`
  ([`Rational.MinimalParabolic`](MinimalParabolic.md)) for `j : P ⟶ G_Q` says that `j` is a
  parabolic subgroup over `Q` (a smooth closed subgroup whose base change to an algebraic
  closure contains a Borel subgroup) and that every parabolic subgroup over `Q` whose subgroup
  functor is contained in that of `j` has the same subgroup functor.
- **Levi subgroups.** `IsRationalLeviSubgroup l` ([`Rational.LeviSubgroup`](LeviSubgroup.md))
  for `l : C_Q ⟶ P` says that `l` is a closed subgroup, `C_Q` is connected reductive, and for
  some represented unipotent radical `r : U ⟶ P` (whose base change to an algebraic closure is
  again the unipotent radical) the multiplication `C_Q × U → P` is an isomorphism of schemes.
  So `C_Q` is a Levi subgroup of `P`, the "reductive part of `P`" of the source.
- **Galois translate.** For `σ : Q ≃ₐ[F] Q`, `radicalGaloisHom j σ`
  ([`Rational.UnipotentRadicalGalois`](UnipotentRadicalGalois.md)) is the base change of `j`
  along `Spec σ`, composed with the canonical isomorphism between that base change of `G_Q`
  and `G_Q`. It is the inclusion of the conjugate subgroup `σ(P)` of `G_Q`; despite its name it
  applies to any subgroup inclusion.
- **Full subgroup functors.** `SubgroupFunctor.range f` assigns to every scheme `Z` over
  `Spec Q` the subgroup of points `Z ⟶ G_Q` that factor through `f`, and `⊓` is the
  intersection on every `Z`. The last equation of the predicate is the scheme-theoretic
  equality `C_Q = P ∩ σ(P)` of subgroup functors of `G_Q`.
- **Cocycles.** `GaloisCocycle.cover F Q` is `Spec Q` as a scheme over `Spec F`. A
  `Cocycle G U` assigns to every scheme `Z` over `Spec F` and pair of points `a b : Z ⟶ U` a
  point `ξ.toFun a b : Z ⟶ G`, naturally in `Z`, with the cocycle identity. For a Galois
  extension these are the ordinary Galois cocycles of `Gal(Q/F)` with values in `G(Q)`.
  `δ.map t` composes the values of `δ` with `t`; `(δ.map t).Cohomologous ξ` says that `ξ` is
  the twist of `δ.map t` by a point of `G` over the cover; `IsTrivial` means being the
  coboundary of a point of the coefficient group over the cover.
- **Real places.** `w : InfinitePlace F` with `w.IsReal` is a real place of `F`;
  `Global.placeCompletion F (.inl w)` is Mathlib's completion `w.Completion` as an
  `F`-algebra, a copy of `ℝ`. For `b = algebraBaseMap F F_w`, `ξ.baseChangePullback b` is the
  cocycle of `G_{F_w}` on the full pulled-back cover `Spec (F_w ⊗_F Q) → Spec F_w`. This is
  the same base change that `Cocycle.LocallyTrivial` (module
  [`Rational.NumberFieldHasseKernelReduction`](NumberFieldHasseKernelReduction.md)) uses at
  every place.

## Statement in words

**The predicate.** For a field extension `Q/F`, a homomorphism `t : C ⟶ G` of group schemes
over `F` is a *quadratic opposite minimal parabolic Levi subgroup* relative to `Q` when
`Q/F` has degree `2`, `t` is a closed subgroup, and there are a nonidentity automorphism `σ`
of `Q/F` and a minimal parabolic subgroup `P` of `G_Q` defined over `Q` such that `C_Q` is a
Levi subgroup of `P` (through `t_Q`) and `C_Q = P ∩ σ(P)` as subgroup functors of `G_Q`. When
`Q/F` is Galois, `σ` is the generator of `Gal(Q/F)`.

**The statement.** Let `F` be a number field, let `Q/F` be a Galois extension of degree `2`
with `Q` totally imaginary, and let `G` be a semisimple group over `F`. Then there is a
quadratic opposite minimal parabolic Levi subgroup `t : C ⟶ G` relative to `Q` with the
following property. Let `ξ` be a cocycle of `G` on the cover `Spec Q → Spec F` whose
pullback to `Spec (F_w ⊗_F Q) → Spec F_w` is trivial at every real place `w` of `F`. Then
there is a cocycle `δ` of `C` on the same cover whose pullback at every real place is
trivial, such that the image `t ∘ δ` of `δ` in `G` is cohomologous to `ξ`. The subgroup is
chosen once for all cocycles.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press, 1994),
source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`. Page numbers are printed
page numbers; the PDF page (counting from 1) is the printed page plus `10`. Printed p. 383:

> recall that 𝒫, a conjugacy class of the parabolic subgroups of G, is said to be reflexive
> if, for P in 𝒫, the opposite parabolic subgroup P⁻ also lies in 𝒫 (cf. Borel-Tits [1, §4].
> Also note that P⁻ ∩ P is the reductive part of P.) For example, all Borel subgroups
> constitute a reflexive class.
>
> LEMMA 6.17'. Let G be a semisimple algebraic group defined over an arbitrary infinite
> perfect field K and having a parabolic subgroup P₀ over a quadratic extension L of K such
> that its conjugacy class 𝒫 is reflexive. Then there exists a parabolic L-subgroup P of G,
> P ∈ 𝒫, such that C = P ∩ σ(P) is the reductive part of P, where σ is a generator of
> Gal(L/K).
>
> LEMMA 6.28'. Notation as in Lemma 6.17', assume in addition that K is a number field. If ξ
> is a cocycle in Z¹(L/K, G) representing an element of
> ker(H¹(K, G) → ∏_{v ∈ V_∞^K} H¹(K_v, G)), then there exists ξ' in Z¹(L/K, C) which is
> equivalent to ξ in Z¹(L/K, G) and represents an element of
> ker(H¹(K, C) → ∏_{v ∈ V_∞^K} H¹(K_v, C)).

The authors add that the proofs are "completely analogous" to those of Lemma 6.17 (printed
pp. 329–330) and Lemma 6.28 (printed pp. 369–370), using instead of the Bruhat decomposition
"a generalized decomposition (cf. Borel-Tits [1, §5])". No project errata note concerns
these lemmas; the erratum `notes/errata/platonov-rapinchuk-1994-e7-a7-subgroup.md` concerns
§6.8 on printed pp. 377 and 386.

## Comparison with the source (provenance: derived)

The statement is the conjunction of Lemma 6.17' and Lemma 6.28' for the conjugacy class of
the minimal parabolic subgroups of `G` over `Q`, specialized to a number field and a totally
imaginary quadratic extension, with the local conditions written on the actual pulled-back
covers.

- **Fields.** A number field is infinite and perfect. The source's `L/K` with generator `σ`
  is `Q/F` with `Module.finrank F Q = 2` and `IsGalois F Q`; the predicate asks for some
  `σ ≠ 1`, which for a quadratic Galois extension is the generator. `Q` is assumed totally
  imaginary (`IsTotallyComplex Q`), a restriction of Lemma 6.28'.
- **The class of minimal parabolic subgroups.** Take for `P₀` a minimal parabolic subgroup
  of `G_Q` over `Q` (one exists: `G_Q` is a parabolic subgroup of itself and contains a
  minimal one, by Borel–Tits). Its conjugacy class `𝒫` is reflexive: the parabolic subgroup
  opposite to `P₀` with respect to a Levi subgroup over `Q` is again a minimal parabolic
  subgroup over `Q`, and any two minimal parabolic subgroups over `Q` are conjugate under
  `G(Q)` (the Library's `MinimalParabolicConjugacyStatement`, proved in
  [`Rational.MinimalParabolicConjugacyProof`](MinimalParabolicConjugacyProof.md)). The same
  conjugacy shows that `σ(P₀)`, a minimal parabolic subgroup over `Q`, lies in `𝒫`. The
  subgroup `P ∈ 𝒫` given by Lemma 6.17' is defined over `Q` and geometrically conjugate to
  `P₀`, hence conjugate to it under `G(Q)` (Borel–Tits), so it is again a minimal parabolic
  subgroup over `Q`: this is `IsMinimalParabolicSubgroup j`.
- **The Levi subgroup.** "C = P ∩ σ(P) is the reductive part of P" is expressed by
  `C_Q = P ∩ σ(P)` as full subgroup functors of `G_Q` together with `IsRationalLeviSubgroup l`
  for `l : C_Q ⟶ P` with `l ≫ j = t_Q`. Since `σ` maps `P ∩ σ(P)` to itself (`σ² = 1`), this
  subgroup of `G_Q` descends to a closed subgroup `t : C ⟶ G` over `F`, the subgroup `C` of
  Lemma 6.28', whose cocycles `Z¹(L/K, C)` are cocycles of the `F`-group `C`. In
  characteristic `0` every group scheme of finite type over a field is smooth (Cartier), so
  the scheme-theoretic intersection agrees with the intersection of algebraic groups used by
  the source. Since `σ² = 1`, it does not matter whether `Spec σ` transports `P` to `σ(P)` or
  to `σ⁻¹(P)`. Lemma 6.28' takes `C` from Lemma 6.17'; accordingly the Lean statement chooses
  `C` before the cocycle `ξ`.
- **Cocycles.** "ξ' is equivalent to ξ in Z¹(L/K, G)" is `(δ.map t).Cohomologous ξ`, with
  `δ` on the same cover `Spec Q`.
- **Local conditions at the archimedean places.** The source's kernels range over all
  archimedean places; the Lean statement uses only the real places, on the full pullback of
  the cover. At a complex place `w` of `F`, `F_w ⊗_F Q ≅ ℂ × ℂ`, the pulled-back cover has a
  section and every cocycle on it is trivial, so these places impose no condition and need
  no conclusion. At a real place `w`, `F_w ⊗_F Q ≅ ℂ` is an algebraic closure of `F_w ≅ ℝ`
  because `Q` is totally imaginary, so triviality of the pullback of `ξ` (or `δ`) is
  triviality of its class in `H¹(F_w, G)` (or `H¹(F_w, C)`). The comparison between the
  Library's cocycles on covers and Galois cohomology classes only explains the formulation;
  this module does not prove it.
- **Scope.** The module combines Lemma 6.17' and Lemma 6.28' for the class of minimal
  parabolic subgroups; Lemma 6.17' is not stated separately, nor for other reflexive classes.
  Lemma 6.28' has a single assertion, which is conditional: triviality at the archimedean
  places is a hypothesis on `ξ` and a property of `ξ'`. If `F` has no real place, the
  real-place hypothesis and conclusion of the Lean statement are vacuous, so the statement
  then reduces every cocycle of `G` on the cover `Spec Q → Spec F` to a cocycle of `C`; this
  is a consequence of the conditional lemma, because at complex places every class is
  trivial. The unconditional reduction of every cocycle, with no local conditions and over an
  arbitrary field, is the first assertion of the unprimed Lemma 6.28 (printed pp. 369–370),
  which concerns a Borel subgroup `B` with `B ∩ σ(B)` a maximal torus; its analogue for
  minimal parabolic subgroups is not stated in this module when `F` has real places.
- **Universe.** `F`, `Q`, the group schemes and the completions live in universe `u`.

When `G_Q` is quasi-split, the minimal parabolic subgroups of `G_Q` over `Q` are its Borel
subgroups, their Levi subgroups are maximal tori, and the statement specializes to the
situation of `NumberFieldQuadraticOppositeBorelTorusStatement` (module
[`Rational.NumberFieldQuadraticOppositeBorelTorus`](NumberFieldQuadraticOppositeBorelTorus.md)),
Lemmas 6.17 and 6.28 of the source. This module does not prove that specialization.

## For a proof (not part of this module)

As in Lemma 6.17, density of the rational points of the variety of pairs of parabolic
subgroups of class `𝒫` of the Weil restriction `R_{Q/F}(G)`, together with openness of the
locus of opposite pairs, gives `P` with `σ(P)` opposite to `P`. As in Lemma 6.28, `σ(P)` is
then the parabolic subgroup opposite to `P` with respect to `C_Q`, and the open cell
`U_P × C_Q × U_P⁻ → G_Q` of Borel–Tits, §5, gives the reduction: if a twisted value of the
cocycle at `σ` lies in the cell with coordinates `(u, c, v)`, the cocycle identity gives
`σ(u) = v⁻¹` and `σ(c) = c⁻¹`, and twisting by `u` leaves `c`. Weak approximation for `G` over
`Q` at the places above the real places of `F`, and an open neighbourhood of `1` in
`C(Q_w)` whose cocycles are trivial (Proposition 3.3 of the source), control the real
places.
