# Quadratic opposite-Borel tori and cocycle reduction controlled at the real places

The module `Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeBorelTorus`
contains two `Prop`-valued definitions in namespace `Langlands.GroupScheme`, both with one
universe parameter `u`:

- the torus predicate `IsQuadraticOppositeBorelTorus`, and
- the statement `NumberFieldQuadraticOppositeBorelTorusStatement.{u}`.

The module states the result and does not prove it. It adds no theorems or axioms.

## Imports

- [`CocycleBaseChangeTriviality`](../CocycleBaseChangeTriviality.md), for
  `Cocycle.baseChangePullback`. Through its imports it also brings in `Cocycle`,
  `Cocycle.map` and `Cocycle.IsTrivial` from [`TorsorCocycle`](../TorsorCocycle.md).
- [`CocycleCohomology`](../CocycleCohomology.md), for `Cocycle.Cohomologous`.
- [`GaloisCocycle`](../GaloisCocycle.md), for the field cover `GaloisCocycle.cover`.
- [`Rational.UnipotentRadicalGalois`](UnipotentRadicalGalois.md), for the Galois translate
  `radicalGaloisHom` of a subgroup inclusion. Through its imports it also brings in
  `algebraBaseMap` and `galoisBaseMap` ([`Torus.LatticeGalois`](../Torus/LatticeGalois.md))
  and `SubgroupFunctor.range` ([`SubgroupFunctor`](../SubgroupFunctor.md)).
- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup` and
  `IsQuasiSplit`.
- [`Reductive.Semisimple`](../Reductive/Semisimple.md), for `IsSemisimple`.
- [`Torus.Maximal`](../Torus/Maximal.md), for `IsMaximalTorus`.
- [`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md), for
  `Global.placeCompletion`.
- Mathlib's `NumberTheory.NumberField.InfinitePlace.TotallyRealComplex`, for
  `NumberField.IsTotallyComplex`.

## Lean definitions

```lean
variable {F : Type u} [Field F] (Q : Type u) [Field Q] [Algebra F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

def IsQuadraticOppositeBorelTorus (t : T.toGrp ⟶ G) : Prop :=
  Module.finrank F Q = 2 ∧ IsMaximalTorus t ∧
  ∃ (σ : Q ≃ₐ[F] Q) (B : GroupScheme (Spec (CommRingCat.of Q)))
    (j : B ⟶ (GroupScheme.baseChange (algebraBaseMap F Q)).obj G),
    σ ≠ 1 ∧ IsGeometricBorelSubgroup j ∧
    SubgroupFunctor.range j ⊓ SubgroupFunctor.range (radicalGaloisHom j σ) =
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F Q)).map t)

def NumberFieldQuadraticOppositeBorelTorusStatement : Prop :=
  ∀ (F Q : Type u) [Field F] [NumberField F] [Field Q] [Algebra F Q]
    [FiniteDimensional F Q] [IsGalois F Q] [IsTotallyComplex Q]
    (_ : Module.finrank F Q = 2) (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSemisimple G → IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F Q)).obj G) →
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ G),
      IsQuadraticOppositeBorelTorus Q t ∧
      ∀ ξ : Cocycle G (GaloisCocycle.cover F Q),
        (∀ w : InfinitePlace F, w.IsReal →
          (ξ.baseChangePullback
            (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial) →
        ∃ δ : Cocycle T.toGrp (GaloisCocycle.cover F Q), (δ.map t).Cohomologous ξ ∧
          ∀ w : InfinitePlace F, w.IsReal →
            (δ.baseChangePullback
              (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial
```

In `IsQuadraticOppositeBorelTorus` the field `F` is implicit (it is read off from the type
of `t`) and `Q` is explicit.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`, and `CommGroupScheme S` the
  commutative ones; `T.toGrp` is the underlying group scheme. For a field extension `Q/F`,
  `algebraBaseMap F Q : Spec Q ⟶ Spec F` is `Spec` of `algebraMap F Q`, and
  `(GroupScheme.baseChange (algebraBaseMap F Q)).obj G` is the base change `G_Q`; `.map t`
  is the base change `t_Q : T_Q ⟶ G_Q` of a homomorphism.
- **Maximal tori.** `IsMaximalTorus t` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a
  torus, `t` is a closed subgroup, and `t` does not factor through a strictly larger closed
  torus of `G` over `F`. For a smooth affine group over a field this is equivalent to the
  maximality of `t` after any field extension, in particular over an algebraic closure
  (Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, Theorem 17.82,
  printed p. 379: "A torus T in G is maximal if and only if T_{k'} is maximal in G_{k'}");
  the Library proves this equivalence as
  `maximalTorusBaseChange` ([`Torus.MaximalBaseChangeProof`](../Torus/MaximalBaseChangeProof.md)).
- **Borel subgroups.** `IsGeometricBorelSubgroup j`
  ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)) for `j : B ⟶ G_Q` says that `j` is
  a Borel subgroup over `Q` (a smooth connected solvable closed subgroup, maximal among such)
  and that its base change to an algebraic closure of `Q` is again Borel. `IsQuasiSplit G_Q`
  says that `G_Q` is connected reductive and has such a Borel subgroup defined over `Q`.
- **Semisimple groups.** `IsSemisimple G` ([`Reductive.Semisimple`](../Reductive/Semisimple.md))
  says that `G` is connected reductive (smooth, affine, connected, with trivial geometric
  unipotent radical) with finite scheme-theoretic centre.
- **Galois translate.** For `σ : Q ≃ₐ[F] Q`, `radicalGaloisHom j σ`
  ([`Rational.UnipotentRadicalGalois`](UnipotentRadicalGalois.md)) is the base change of `j`
  along `Spec σ : Spec Q ⟶ Spec Q`, composed with the canonical isomorphism between that base
  change of `G_Q` and `G_Q` (both are base changes of `G` along maps `Spec Q ⟶ Spec F` that
  agree because `σ` fixes `F`). It is the inclusion of the conjugate subgroup `σ(B)` of
  `G_Q`. Despite its name it applies to any subgroup inclusion.
- **Full subgroup functors.** `SubgroupFunctor.range f` ([`SubgroupFunctor`](../SubgroupFunctor.md))
  assigns to every scheme `Z` over `Spec Q` the subgroup of points `Z ⟶ G_Q` that factor
  through `f`, and `⊓` is the intersection on every `Z`. The equation in the predicate
  therefore says: for every test scheme `Z` over `Q`, a point of `G_Q` with values in `Z`
  lies in both `B` and `σ(B)` exactly when it lies in `T_Q`. This is the scheme-theoretic
  equality `T_Q = B ∩ σ(B)` of subgroup functors of `G_Q`.
- **Cocycles.** `GaloisCocycle.cover F Q` ([`GaloisCocycle`](../GaloisCocycle.md)) is
  `Spec Q` as a scheme over `Spec F`. A `Cocycle G U` ([`TorsorCocycle`](../TorsorCocycle.md))
  assigns to every scheme `Z` over `Spec F` and pair of points `a b : Z ⟶ U` a point
  `ξ.toFun a b : Z ⟶ G`, naturally in `Z`, with `ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`.
  `δ.map t` composes the values of `δ` with `t`. `(δ.map t).Cohomologous ξ`
  ([`CocycleCohomology`](../CocycleCohomology.md)) says that there is `f : U ⟶ G` with
  `ξ.toFun a b = (a ≫ f)⁻¹ * (δ.map t).toFun a b * (b ≫ f)` for all `a`, `b`.
  `IsTrivial` means being of the form `(a ≫ f) * (b ≫ f)⁻¹`.
- **Real places and completions.** `w : InfinitePlace F` with `w.IsReal` is a real place of
  `F`. `Global.placeCompletion F (.inl w)`
  ([`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md)) is Mathlib's
  completion `w.Completion` as an `F`-algebra, a copy of `ℝ` for real `w`.
- **Full pullback to a completion.** For `b = algebraBaseMap F F_w`,
  `ξ.baseChangePullback b` ([`CocycleBaseChangeTriviality`](../CocycleBaseChangeTriviality.md))
  is the cocycle of `G_{F_w}` on the whole pulled-back cover
  `(Over.pullback b).obj (Spec Q) = Spec (F_w ⊗_F Q)` over `Spec F_w`, obtained by composing
  pairs of points with the projection to `Spec Q`. This is the same base change that
  `Cocycle.LocallyTrivial` uses at every place.

## Statement in words

**The predicate.** For a field extension `Q/F`, a homomorphism `t : T ⟶ G` of group schemes
over `F` is a *quadratic opposite-Borel torus* relative to `Q` when `Q/F` has degree `2`, `t`
is a maximal torus of `G` over `F`, and there are a nonidentity automorphism `σ` of `Q/F` and
a Borel subgroup `B` of `G_Q` defined over `Q` (and Borel over an algebraic closure) such that
`T_Q = B ∩ σ(B)` as subgroup functors of `G_Q`. When `Q/F` is Galois, `σ` is the generator of
`Gal(Q/F)`.

**The statement.** Let `F` be a number field, let `Q/F` be a Galois extension of degree `2`
with `Q` totally imaginary, and let `G` be a semisimple group over `F` that is quasi-split
over `Q`. Then there is a quadratic opposite-Borel torus `t : T ⟶ G` relative to `Q` with the
following property. Let `ξ` be a cocycle of `G` on the cover `Spec Q → Spec F` whose pullback
to the cover `Spec (F_w ⊗_F Q) → Spec F_w` is trivial at every real place `w` of `F`. Then
there is a cocycle `δ` of `T` on the same cover `Spec Q → Spec F` whose pullback at every real
place `w` is trivial, such that the image `t ∘ δ` of `δ` in `G` is cohomologous to `ξ`. The
torus is chosen once for all cocycles.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press, 1994),
source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`. The page numbers below
are printed page numbers; the PDF page (counting from 1) is the printed page plus `10`.

- **Lemma 6.17**, printed pp. 329–330: "Let G be a semisimple algebraic group defined over an
  arbitrary field K of characteristic 0 and containing a Borel subgroup over a quadratic
  extension L/K, and let σ be a generator of Gal(L/K). Then there exists a Borel L-subgroup B
  of G such that B ∩ B^σ is a maximal K-torus of G."
- **Lemma 6.28**, printed pp. 369–370: "Let G be a semisimple algebraic group defined over an
  arbitrary field K. Assume G contains a Borel subgroup B defined over a quadratic extension
  L/K, such that T = B ∩ σ(B) is a maximal K-torus of G (where σ is the generator of
  Gal(L/K)). Then any cocycle ξ in Z¹(L/K, G) is equivalent to some ξ' in Z¹(L/K, T).
  Moreover, if K is a number field and ξ in Z¹(L/K, G) represents an element of
  ker(H¹(K, G) → ∏_{v ∈ V_∞^K} H¹(K_v, G)), then also ξ' in Z¹(L/K, T) can be chosen to
  represent an element of ker(H¹(K, T) → ∏_{v ∈ V_∞^K} H¹(K_v, T))."

In the proof of Lemma 6.28 the authors let `S` be the set of real places `v` of `K` with
`L_w = LK_v ≠ K_v`, choose the new cocycle by approximation at the places of `S`, and note
that "L ⊂ K_v for v in V_∞^K \ S, and ξ' is automatically trivial in H¹(K_v, T)". No
project errata note concerns these two lemmas; the erratum
`notes/errata/platonov-rapinchuk-1994-e7-a7-subgroup.md` concerns §6.8 on printed pp. 377
and 386.

## Comparison with the source (provenance: derived)

The statement is the conjunction of Lemma 6.17 and Lemma 6.28, specialized to a number field
and a totally imaginary quadratic extension, with the local conditions written on the actual
pulled-back covers.

- **Fields.** A number field has characteristic `0`, as Lemma 6.17 requires. The source's
  `L/K` with generator `σ` of `Gal(L/K)` is `Q/F` with `Module.finrank F Q = 2` and
  `IsGalois F Q`; the predicate asks for some `σ ≠ 1`, which for a quadratic Galois extension
  is the generator. The extension is assumed totally imaginary (`IsTotallyComplex Q`), a
  restriction of Lemma 6.28, which allows any quadratic extension.
- **Group and Borel subgroup.** "Semisimple algebraic group" is `IsSemisimple G`.
  "Containing a Borel subgroup over L" is `IsQuasiSplit G_Q`, which supplies a geometric
  Borel subgroup defined over `Q`. The "Borel L-subgroup B" of the conclusion of Lemma 6.17
  is `j : B ⟶ G_Q` with `IsGeometricBorelSubgroup j`, and `B^σ = σ(B)` is
  `radicalGaloisHom j σ`. Since `σ² = 1`, it does not matter whether `Spec σ` transports `B`
  to `σ(B)` or to `σ⁻¹(B)`.
- **The torus.** "B ∩ B^σ is a maximal K-torus of G" is expressed by an `F`-torus `t : T ⟶ G`
  with `IsMaximalTorus t` and `T_Q = B ∩ σ(B)` as full subgroup functors of `G_Q`. In
  characteristic `0` every group scheme of finite type over a field is smooth (Cartier), so
  this scheme-theoretic intersection agrees with the intersection of algebraic groups used
  by the source. Maximality over `F` among closed `F`-tori is equivalent to maximality over
  an algebraic closure by Milne 17.82 (`maximalTorusBaseChange`), so `IsMaximalTorus t`
  matches the source's "maximal K-torus of G". Lemma 6.28 takes this torus as its hypothesis,
  and the torus in the conclusion is the one produced by Lemma 6.17; accordingly the Lean
  statement chooses `T` before the cocycle `ξ`.
- **Cocycles.** `Z¹(L/K, G)` is represented by the Library's cocycles of `G` on the cover
  `Spec Q → Spec F`; "ξ is equivalent to ξ'" with `ξ' ∈ Z¹(L/K, T)` viewed in `Z¹(L/K, G)`
  is `(δ.map t).Cohomologous ξ`. The new cocycle lives on the same cover `Spec Q`.
- **Local conditions at the archimedean places.** The source's kernels range over all
  archimedean places `v ∈ V_∞^K`; the Lean statement uses only real places, on the full
  pullback of the cover `Spec Q → Spec F`. The two formulations agree:
  - At a complex place `w` of `F`, `F_w ⊗_F Q ≅ ℂ × ℂ`, so the pulled-back cover
    `Spec (F_w ⊗_F Q) → Spec F_w` has a section `s`, and every cocycle `ζ` on it is trivial,
    with cochain `f(x) = ζ(x, s ∘ π ∘ x)`. These places impose no condition and need no
    conclusion. They are the places `v ∉ S` of the source's proof, where `L ⊂ K_v`.
  - At a real place `w`, `F_w ≅ ℝ`, and since `Q` is totally imaginary, `F_w ⊗_F Q ≅ ℂ` is a
    field, an algebraic closure of `F_w`. A cocycle on `Spec ℂ → Spec F_w` is a cocycle in
    `Z¹(Gal(ℂ/ℝ), ·)`, and `H¹(F_w, ·) = H¹(Gal(ℂ/ℝ), ·)`, so triviality of the pullback of
    `ξ` (or `δ`) on this cover is triviality of its class in `H¹(F_w, G)` (or
    `H¹(F_w, T)`). Every real place lies in the source's set `S`.

  The comparison between the Library's cocycles on covers and Galois cohomology classes is
  used only to explain the formulation; this module does not prove it.
- **What is not stated.** The first assertion of Lemma 6.28, without local conditions, is
  included only when `F` has no real place, where both local conditions are vacuous. Lemma
  6.17 is stated only together with Lemma 6.28 and only for number fields.
- **Universe.** `F`, `Q`, the group schemes and the completions `CommAlgCat.{u}` live in
  universe `u`.

## Relation to the Library

- `Cocycle.LocallyTrivial` (module
  [`Rational.NumberFieldHasseKernelReduction`](NumberFieldHasseKernelReduction.md)) uses the
  same pullback to a completion at every place; the hypothesis on `ξ` here is the part of
  that condition at the real places.
- `QuasiSplitCocycleTorusReductionStatement` (module
  [`Rational.QuasiSplitCocycleTorusReductionStatement`](QuasiSplitCocycleTorusReductionStatement.md))
  states Steinberg's reduction of cocycles of quasi-split semisimple groups to tori after a
  finite Galois refinement of the cover. The statement here keeps the cover `Spec Q`, fixes
  the torus `B ∩ σ(B)`, and controls the local behaviour at the real places.

## For a proof (not part of this module)

Lemma 6.17 is proved by density of the rational points of the variety of Borel subgroups of
the Weil restriction `R_{L/K}(G)` and an open condition on pairs of Borel subgroups. Lemma 6.28
uses that `σ(B)` is the Borel subgroup opposite to `B`, the open cell
`U × T × U⁻ → G` of the Bruhat decomposition, and weak approximation for `G` over `L` at the
places above the real places of `K`, together with an open neighbourhood of `1` in
`T(L_w)` whose cocycles are trivial (Proposition 3.3 of the source).
