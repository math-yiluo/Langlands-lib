# Statement: rational lifting of strongly regular values of the canonical class quotient

Author: Worker 4945.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.ClassFunctions.StronglyRegularRationalLiftingStatement.{u}`,
a `Prop`-valued `def` with one universe parameter `u`. It is property 3 of
`Langlands.GroupScheme.QuasiSplitSteinbergQuotientStatement` (module
`Rational/QuasiSplitSteinbergQuotientStatement`), with the existential quotient
`V` and map `ρ` fixed to the published canonical quotient
`ClassFunctions.quotient G` and its map `ClassFunctions.rho G` (module
`Rational/ClassFunctions`). It is the companion of the published
`ClassFunctions.StronglyRegularFibresStatement`, which is property 2 for the
same map.

## Lean statement

```lean
def StronglyRegularRationalLiftingStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → ∀ hqs : IsQuasiSplit G,
    letI : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
    ∀ (v : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ ClassFunctions.quotient G)
      (F : Type u) [Field F] [Algebra K F]
      (w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of F)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of F))}
          (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) =
            (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      toUnit _ ≫ v = w ≫ ClassFunctions.rho G →
      ∃ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X, x ≫ ClassFunctions.rho G = v
```

The module imports `Rational/ClassFunctions` and
`Rational/QuasiSplitSteinbergQuotientStatement`, the same imports as
`ClassFunctionsStronglyRegularFibresStatement`.

## Meaning

For a field `F` over `K` write `b_F : Spec F ⟶ Spec K` for the map induced by
`algebraMap K F`, `U_F = Over.mk b_F` for `Spec F` viewed over `Spec K`, and
`G_F = (baseChange b_F).obj G`. A morphism `U_F ⟶ G.X` is a point of `G` with
values in `F`, and `𝟙_ (Over (Spec K))` is `Spec K` itself, so a morphism out of
it is a `K`-rational point.

Let `K : Type u` be an arbitrary field, including finite and imperfect fields,
and `G` a group scheme over `Spec K` that is simply connected (`IsSimplyConnected`)
and quasi-split (`IsQuasiSplit`). Quasi-splitness makes `G` connected reductive,
so its structure morphism is affine (`hqs.isConnectedReductive.isAffineHom`);
this instance is what the canonical quotient `ClassFunctions.quotient G` (the
relative spectrum of the subalgebra of all-test conjugation-invariant regular
functions) and `ClassFunctions.rho G : G.X ⟶ ClassFunctions.quotient G` (the
spectrum of the inclusion of that subalgebra) need.

Let `v` be a `K`-rational point of `ClassFunctions.quotient G`. Suppose that over
some field `F` over `K` (in universe `u`) it becomes the image of a strongly
regular point: there are a point `w : U_F ⟶ G.X`, an `F`-torus `S` and a closed
subgroup inclusion `j : S ⟶ G_F` such that every point `c` of `G_F`, on every
test scheme `Z` over `Spec F` (reduced or not), that commutes with the
restriction of the `F`-rational counterpart
`(baseChangeBasePointsEquiv b_F G).symm w` factors through `S`, and
`toUnit U_F ≫ v = w ≫ ClassFunctions.rho G`. Then `v` is the image under
`ClassFunctions.rho G` of a `K`-rational point `x` of `G`.

The hypotheses on `F`, `w`, `S` and `j` are word for word those of property 3 of
`QuasiSplitSteinbergQuotientStatement`, and the conclusion is its conclusion with
`V := ClassFunctions.quotient G` and `ρ := ClassFunctions.rho G`. Hence a proof of
this proposition, together with a proof of
`ClassFunctions.StronglyRegularFibresStatement` and the published all-test
conjugation invariance `ClassFunctions.rho_conjugation`, supplies the three
properties of `QuasiSplitSteinbergQuotientStatement` with the witnesses
`ClassFunctions.quotient G` and `ClassFunctions.rho G`.

## Sources and provenance

Provenance: derived.

- R. Steinberg, *Regular elements of semi-simple algebraic groups*, Publ. Math.
  IHÉS 25 (1965), 49–80, source
  `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
  PDF page = printed page − 47.
  - Introduction, printed p.51 (PDF p.4): Steinberg introduces "a perfect
    subfield `k` of `K`" for the rationality results. Theorem 1.7 (same page):
    if `G` is simply connected, over `k` and contains a Borel subgroup over `k`,
    "each semisimple class over `k` contains an element over `k`".
  - 6.10 (printed p.64, PDF p.17): for simply connected `G` the fibres of the
    class-function map are the fibres of `ρ = (χ_1, …, χ_r)`, given by the
    fundamental characters.
  - 9.4 and 9.5 (printed pp.72–73, PDF pp.25–26): if `G` is over `k`, contains a
    Borel subgroup over `k` and has no simple component of type `A_n` (`n`
    even), the cross-section `N` can be constructed over `k`, and each regular
    class over `k` contains an element over `k`.
  - 9.7, 9.8 and 9.11–9.19 (printed pp.73–77, PDF pp.26–30): for type `A_n`
    (`n` even) the substitute `N' = N'' ∪ N'''`, whose pieces are over `k` and are
    mapped by `ρ` isomorphically onto the subvarieties `V''` (`f = 0`) and
    `V'''` (`f ≠ 0`) of `V` (9.19); 9.8 combines both kinds of components into
    Theorem 1.7.
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic
  groups II*, Tôhoku Math. J. 20 (1968), 443–497, source
  `borel-springer-1968-rationality-properties-ii`, SHA-256
  `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`.
  PDF page = printed page − 442.
  - 8.2 and 8.3 (printed pp.481–482, PDF pp.39–40): a connected reductive group
    with a maximal torus that is defined and split over `k` splits over `k`, and
    every such group splits over a finite separable extension of `k`.
  - 8.6 (printed pp.483–484, PDF pp.41–42): for a connected, semisimple, simply
    connected, quasi-split `k`-group, "any regular semi-simple conjugacy class
    of `G` which is defined over `k` contains an element of `G(k)`"; "Using 8.2,
    the proof given in loc. cit. carries over to arbitrary ground fields", since
    "any regular semi-simple conjugacy class intersects `N` in exactly one
    point, with multiplicity 1".

Derivation. In the sources, a point of `V` over `k` whose fibre is a regular
semisimple class defined over `k` is the image of an element of `G(k)`
(Steinberg 1.7 and 9.5 for perfect `k`; Borel–Springer 8.6 for arbitrary `k`).
The proposition is the corresponding statement for the actual canonical
quotient, restricted to `K`-points of the quotient that are images of strongly
regular points, i.e. points whose all-test centralizer lies in a closed torus.
Over an algebraic closure such a point is regular semisimple: it commutes with
itself, so it lies in the torus, and its centralizer is contained in a torus.
The translation from Steinberg's fundamental-character map to the canonical
equalizer quotient is the identification of the class-function algebra with the
published `ClassFunctions.algebra G` described in `Rational/ClassFunctions.md`.

The intended proof follows the cross-section route of the sources. Over a finite
Galois splitting field, Steinberg's ordered product `N` (outside type `A_n`, `n`
even) or the pieces `N''`, `N'''` (type `A_n`, `n` even) are mapped by the canonical
`ρ` isomorphically onto `V` or onto the strata `f = 0` and `f ≠ 0`; Galois
descent of these subschemes then lifts a `K`-point of the quotient to a
`K`-point of `G`. The descent is along a finite Galois extension, which exists
for every field by Borel–Springer 8.3, so perfectness is not needed. Nothing
in this module asserts that this route has been carried out.

## What is not stated

- No global `K`-rational section of `ClassFunctions.rho G` is asserted, in
  particular none when `G` has a simple component of type `A_n` with `n` even
  (compare Steinberg 9.6). The statement lifts individual `K`-points of the
  quotient.
- Only `K`-points of the quotient that are images of strongly regular points
  over some field are covered. Lifting of arbitrary `K`-points of the quotient
  (the full Theorem 1.7 for all semisimple classes) is not stated.
- Nothing is said about the geometry of `ClassFunctions.quotient G` (affine
  space, smoothness, categorical quotient) or about the fibres of
  `ClassFunctions.rho G`; property 2 is the separate
  `ClassFunctions.StronglyRegularFibresStatement`.
- The statement is not `QuasiSplitRegularClassRationalStatement` (Borel–Springer
  8.6 for Galois-stable classes) and does not assume it.
- Nothing is proved here.
