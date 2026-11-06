# Statement: Steinberg's class quotient of a simply connected quasi-split group

Author: Worker 1379.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.QuasiSplitSteinbergQuotientStatement.{u}`, a
`Prop`-valued `def` with one universe parameter `u`. It is the premise of the
conditional reduction `QuasiSplitRegularClassRationalReductionStatement`
(module `Rational/QuasiSplitRegularClassRationalReduction.lean`), which
derives `QuasiSplitRegularClassRationalStatement` (Borel–Springer 8.6 for
strongly regular classes) from it. It packages the three properties of
Steinberg's invariant map `ρ : G → V` (Steinberg 1965, 6.10) that this
derivation uses.

## Lean statement

```lean
def QuasiSplitSteinbergQuotientStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → IsQuasiSplit G →
    ∃ (V : Over (Spec (CommRingCat.of K))) (ρ : G.X ⟶ V),
      (∀ {Z : Over (Spec (CommRingCat.of K))} (g x : Z ⟶ G.X),
        (g * x * g⁻¹) ≫ ρ = x ≫ ρ) ∧
      (∀ (F : Type u) [Field F] [Algebra K F]
        (y w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
        (S : GroupScheme (Spec (CommRingCat.of F)))
        (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G),
        IsTorus S → IsClosedSubgroup j →
        (∀ {Z : Over (Spec (CommRingCat.of F))}
            (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X),
          c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) =
              (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) * c →
            ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
        y ≫ ρ = w ≫ ρ →
        ∃ (E : Type u) (_ : Field E) (_ : Algebra K E)
          (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))))
          (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
          g * (q ≫ y) * g⁻¹ = q ≫ w) ∧
      (∀ (v : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ V)
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
        toUnit _ ≫ v = w ≫ ρ →
        ∃ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X, x ≫ ρ = v)
```

The module imports `CocharacterTransport` (for `baseChangeBasePointsEquiv`),
`SimplyConnected.Basic`, `Reductive.QuasiSplit` and `Torus.Lattice`, the same
imports as `QuasiSplitRegularClassRationalStatement` without
`Mathlib.FieldTheory.Galois.Basic`.

## Meaning

For a field `F` over `K` write `b_F : Spec F ⟶ Spec K` for the map induced by
`algebraMap K F`, `U_F = Over.mk b_F` for `Spec F` viewed as an object over
`Spec K`, and `G_F = (baseChange b_F).obj G`. A morphism `U_F ⟶ G.X` is a
point of `G` with values in `F`.

Let `G` be a simply connected (`IsSimplyConnected`) and quasi-split
(`IsQuasiSplit`) group scheme over a field `K`. The statement provides an
object `V` of `Over (Spec K)`, that is, a `K`-scheme (no finiteness, affineness
or smoothness is required), and a `K`-morphism `ρ : G.X ⟶ V` with three
properties.

1. **Invariance.** For every object `Z` over `Spec K` and points
   `g, x : Z ⟶ G.X`, `ρ(g x g⁻¹) = ρ(x)`. So `ρ` is constant on conjugacy
   classes in the scheme-theoretic (all-test) sense.
2. **Strongly regular fibres are geometric classes.** Let `F` be a field over
   `K` (in universe `u`) and `y, w` points of `G` with values in `F`. Suppose
   `w` is strongly regular in the sense used by
   `QuasiSplitRegularClassRationalStatement`: there are an `F`-torus `S` and a
   closed subgroup inclusion `j : S ⟶ G_F` such that every point `c` of `G_F`,
   on any test scheme `Z` over `Spec F`, that commutes with the restriction of
   the `F`-rational counterpart `(baseChangeBasePointsEquiv b_F G).symm w`
   factors through `S`. If `ρ(y) = ρ(w)`, then `y` and `w` are conjugate over
   some field extension: there are a field `E` over `K` (in universe `u`), a
   morphism `q : U_E ⟶ U_F` over `Spec K` (a `K`-embedding `F → E`) and a
   point `g ∈ G(E)` with `g (q ≫ y) g⁻¹ = q ≫ w`. Nothing is assumed about
   `y`.
3. **Rationality.** Let `v : 𝟙_ ⟶ V` be a `K`-rational point of `V`. Suppose
   that over some field `F` over `K` the point `v` becomes the image of a
   strongly regular point: there is `w : U_F ⟶ G.X`, strongly regular as in
   2, with `toUnit U_F ≫ v = w ≫ ρ`. Then `v = ρ(x)` for some `K`-rational
   point `x : 𝟙_ ⟶ G.X` of `G`.

## Sources and provenance

Provenance: derived.

- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
  PDF page = printed page − 47.
  - 6.5 (printed p.63, PDF p.16): "For all `f` in `C[G]` and `x` in `G`, we
    have `f(x) = f(x_s)`."
  - 6.6 (printed p.63, PDF p.16): for `x`, `y` both semisimple or both
    regular, `x` and `y` are conjugate iff `χ(x) = χ(y)` for every character
    `χ`; "If `G` is simply connected, c) and d) need only hold for the
    fundamental characters and representations of `G`."
  - 6.10 (printed p.64, PDF p.17): "if `G` is simply connected the fibres are
    the inverse images of points for the map `ρ` from `G` to affine `r`-space
    `V` defined thus: `ρ(x) = (χ_1(x), χ_2(x), …, χ_r(x))`."
  - 6.11 (printed p.64, PDF p.17): each fibre is a union of classes, and "the
    semisimple elements of `F` form a single class".
  - 7.9 (printed p.68, PDF p.21): "Let `G` be simply connected and let `ρ` be
    the map 6.10 from `G` to affine `r`-space `V`. Then `ρ` maps `N`, as a
    variety, isomorphically onto `V`."
  - 8.1 (printed p.70, PDF p.23): for simply connected `G`, `x` is regular iff
    it is conjugate to an element of `N` iff the differentials `dχ_i` are
    independent at `x`.
  - 9.4 (printed p.72, PDF p.25): if `G` is over `k`, contains a Borel subgroup
    over `k` and has no simple component of type `A_n` (`n` even), then `N`
    can be constructed over `k`.
  - 9.6 (printed p.73, PDF p.26): for type `A_n` (`n` even) no global
    cross-section over `k` of the fibres of "the map `ρ` of 6.10 (which can be
    taken over `k` if `V` is suitably defined over `k`)" is known; 9.7 gives a
    substitute.
  - 9.19 (printed p.77, PDF p.30): "`ρ` maps `N''` and `N'''` isomorphically
    onto `V''` and `V'''`", the subvarieties of `V` where `f = 0` and
    `f ≠ 0`.
  - Steinberg works over a perfect field `k` (printed p.51, PDF p.4).
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic
  groups II* (1968), source `borel-springer-1968-rationality-properties-ii`,
  SHA-256
  `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`,
  8.6 (printed pp.483–484, PDF pp.41–42): "Let `G` be a connected,
  semi-simple simply connected `k`-group, which is quasi-split … Then any
  regular semi-simple conjugacy class of `G` which is defined over `k`
  contains an element of `G(k)`. Using 8.2, the proof given in loc. cit.
  carries over to arbitrary ground fields, if one observes that … any regular
  semi-simple conjugacy class intersects `N` in exactly one point, with
  multiplicity 1 (as follows from loc. cit., 8.1)."

Derivation. The intended witnesses are Steinberg's `V` and `ρ`: `ρ` is given by
the fundamental characters `χ_1, …, χ_r`. For quasi-split `G` the Galois group
permutes the fundamental characters, so `V` is the corresponding `K`-form of
affine `r`-space ("`V` suitably defined over `k`", 9.6) and `ρ` is defined
over `K`. The statement keeps `V` and `ρ` existential, so a prover may choose
any `K`-scheme and morphism with the three properties.

1. The `χ_i` are characters of representations, hence class functions. The
   identity `ρ(g x g⁻¹) = ρ(x)` holds on geometric points of the reduced
   scheme `G × G`, hence as an identity of morphisms, hence on every test
   object.
2. Work over an algebraic closure `F̄` of `F`. The point `w` commutes with
   itself, so it lies in the torus `S`; hence `w` is semisimple and its
   centralizer lies in a torus. Write `y = y_s y_u` (Jordan decomposition). By
   6.5, `ρ(y_s) = ρ(y) = ρ(w)`, and by 6.6 the semisimple elements `y_s` and
   `w` are conjugate. Then `y_u` centralizes `y_s`, whose centralizer is a
   conjugate of that of `w` and so lies in a torus. A unipotent element of a
   torus is `1`, so `y = y_s` is conjugate to `w` over `F̄`. In the statement
   the conjugacy is witnessed over some field `E` with an embedding `F → E`;
   `E = F̄` works.
3. Over a perfect field this is Steinberg's Theorem 1.7 restricted to strongly
   regular classes, through the cross-section `N` (7.9, 9.4) or its substitute
   `N'' ∪ N'''` (9.19). Over an arbitrary field it is Borel–Springer 8.6,
   applied as follows. By the argument in 2, the geometric points of the
   fibre `ρ⁻¹(v)` form the conjugacy class `C` of `w`, which is regular
   semisimple. By 8.1 the differentials of the `χ_i` are independent at
   regular elements, so the fibre is smooth over `K`. Hence `C` is defined
   over `K`, and Borel–Springer 8.6 gives `x ∈ C ∩ G(K)`; then
   `ρ(x) = ρ(w) = v`.

Property 3 is restricted to `K`-points of `V` that are images of strongly
regular points over some field. This is the case Borel–Springer 8.6 covers
over arbitrary fields, and it is the case the reduction uses.

`V` and `ρ` cannot be replaced by parameters subject only to properties 1 and
2. Over an imperfect field `K` of characteristic `p`, composing Steinberg's
`ρ` with a Frobenius-type map `t ↦ t^p` on `V` keeps 1 and 2. But the
composite also maps non-rational points of `V` to `K`-points, so 3 fails for
it.

## What is not stated

- No claim that `V` is (a form of) affine space, that `ρ` is a categorical
  quotient (Steinberg 6.16), or that `ρ` is smooth or flat.
- No `K`-rational cross-section `N` is claimed (Steinberg 9.6 knows none in
  type `A_n`, `n` even).
- Property 2 concerns only fibres through strongly regular points, and
  property 3 only `K`-points of `V` that are images of strongly regular
  points. The general Theorem 1.7 for arbitrary semisimple classes is not
  stated.
- Nothing is proved here; the existence is the obligation of a separate
  proof.
