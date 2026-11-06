# Statement: finite Galois conjugacy to a point with toral centralizer

Authors: Worker 1296 and Worker 1601.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.RegularConjugateFiniteGaloisStatement.{u}`, a
`Prop`-valued `def` with one universe parameter `u`. It is a twist-free
prerequisite of the proof of
`Langlands.GroupScheme.QuasiSplitSimplyConnectedRegularConjugateStatement`
(`Rational/QuasiSplitRegularConjugateStatement.lean`). There, a rational point
`x` of `G` is first found that is conjugate over some field `E` to the point
`z` of `G` over `Spec L` corresponding to the strongly regular point `y` of
the inner form. This statement then improves the field of conjugacy from `E`
to a finite Galois extension of `K` and shows that the centralizer of `x` lies
in a closed `K`-torus.

## Lean statement

```lean
def RegularConjugateFiniteGaloisStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G : GroupScheme (Spec (CommRingCat.of K))), IsConnectedReductive G →
    ∀ (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of L)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of L))}
        (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) =
          (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) * c →
        ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
    ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
      (E : Type u) [Field E] [Algebra K E]
      (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
      g * (toUnit _ ≫ x) * g⁻¹ = q ≫ z →
      ∃ (T : GroupScheme (Spec (CommRingCat.of K))) (i : T ⟶ G),
        IsTorus T ∧ IsClosedSubgroup i ∧
        (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ G.X),
          c * (toUnit Z ≫ x) = (toUnit Z ≫ x) * c → ∃ t : Z ⟶ T.X, t ≫ i.hom.hom = c) ∧
        ∃ (L' : Type u) (_ : Field L') (_ : Algebra K L')
          (_ : FiniteDimensional K L') (_ : IsGalois K L')
          (r : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (g' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶ G.X),
          g' * (toUnit _ ≫ x) * g'⁻¹ = r ≫ z
```

The module imports `Reductive.Basic`, `Torus.Lattice`, `CocharacterTransport`
and `Mathlib.FieldTheory.Galois.Basic`.

## Meaning

Write `b : Spec L → Spec K` for the morphism of the finite Galois extension
and `G_L` for the base change `(baseChange b).obj G`. Points of `G` over a
`K`-scheme `W` are morphisms `W ⟶ G.X` in `Over (Spec K)`, with the group law
of points; `g * w * g⁻¹` is conjugation of points. A field extension `F` of `K`
is viewed as the object `Over.mk (Spec F → Spec K)`, and a morphism of such
objects `Spec F ⟶ Spec L` over `Spec K` is the same as a `K`-embedding
`L → F`.

Hypotheses:

- `K` is an arbitrary field, `L/K` a finite Galois extension in the same
  universe, and `G` a connected reductive group over `K`
  (`IsConnectedReductive`: smooth, affine, connected, with trivial geometric
  unipotent radical).
- `z` is a point of `G` over `Spec L`. Its counterpart
  `(baseChangeBasePointsEquiv b G).symm z` is the corresponding `L`-rational
  point of `G_L`.
- `S` is a torus over `L` and `j : S ⟶ G_L` a closed subgroup that contains
  the scheme-theoretic centralizer of that `L`-rational point on all test
  schemes over `Spec L`: every point `c` of `G_L` over any `Z` that commutes
  with the constant point `toUnit Z ≫ z` factors through `j`.
- `x` is a `K`-rational point of `G`, and `E` is an arbitrary field
  extension of `K` with a morphism of covers `q : Spec E ⟶ Spec L` over
  `Spec K` (a `K`-embedding `L → E`). The point `g` of `G` over `Spec E`
  conjugates the constant point `toUnit _ ≫ x` to `q ≫ z`, the point `z`
  restricted along `q`.

The conclusion provides:

- a torus `T` over `K` and a closed subgroup `i : T ⟶ G` that contains the
  scheme-theoretic centralizer of `x` on all test schemes over `Spec K`; and
- a finite Galois extension `L'/K` in the same universe, a morphism of covers
  `r : Spec L' ⟶ Spec L` over `Spec K` (a `K`-embedding `L → L'`), and a
  point `g'` of `G` over `Spec L'` with `g' x g'⁻¹ = r ≫ z`.

So conjugacy of `x` and `z` over an arbitrary field, for example an
algebraically closed one, can be replaced by conjugacy over a finite Galois
extension of `K` containing `L`, and `x` is again strongly regular.

## Sources and provenance

Provenance: derived.

- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`,
  §10 (printed p.78, PDF p.31). After finding `x` over `k` in the class of the
  strongly regular `y`, Steinberg writes `y = i(a) x` and notes that the
  centralizer of `x` is "a torus because `x` is strongly regular, and over `k`
  because `x` is".

Derived content. Steinberg works over an algebraic closure. The statement
records two standard consequences in the finite-cover form used by the
target statement.

- The centralizer of `z` equals `S`: `z` lies in its own centralizer, hence
  in `S`, and `S` is commutative. Conjugation by `g` identifies the
  centralizer of `x` over `E` with `S` over `E`, so the centralizer of `x` is
  a `K`-form of a torus, hence a `K`-torus.
- The transporter of `x` to `z` over `L` is a torsor under the centralizer of
  `x` over `L`, which is a torus. It has the point `g` over `E`, so it is
  nonempty, of finite type and geometrically reduced over `L`. It therefore
  has a point over a finite separable extension of `L`, and over the Galois
  closure `L'` of that extension over `K`.

The hypothesis `IsConnectedReductive G` is the one available in the target
statement. The argument needs only that `G` is affine and smooth over `K`.

## What is not stated

- The existence of `x` itself, that is the Steinberg / Borel–Springer
  theorem that a rational regular semisimple class has a rational point, is
  not part of this statement; `x`, `E`, `q` and `g` are hypotheses.
- Nothing is proved here; the existence is the obligation of a separate
  exact-target proof.
