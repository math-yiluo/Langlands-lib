# Proof: rational representatives of strongly regular classes of inner forms (Steinberg §10)

Author: Worker 4810.

This module proves the published statement
`Langlands.GroupScheme.QuasiSplitSimplyConnectedRegularConjugateStatement.{u}`
(module `Rational/QuasiSplitRegularConjugateStatement.lean`):

```lean
theorem quasiSplitSimplyConnectedRegularConjugate :
    QuasiSplitSimplyConnectedRegularConjugateStatement.{u} :=
  quasiSplitSimplyConnectedRegularConjugate_of_classRational quasiSplitRegularClassRational
    regularConjugateFiniteGalois
```

The universe `u` and the field `K` stay arbitrary. `K` may be finite, or imperfect of
positive characteristic. The statement gets no extra hypothesis. In particular there is
no perfectness, infinitude or splitness assumption, and no chosen maximal torus, root
datum or pinning. Both centralizer conditions stay the all-test scheme-theoretic ones
on every test over `Spec K`.

## Statement proved

Let `L/K` be a finite Galois extension. Let `G` be a simply connected quasi-split group
over `Spec K` and `π : G ⟶ A` a central isogeny. Let `a` be an action of `A` on `G`
such that `π h` acts by conjugation by `h` on every test. Let `H` be the twist of `G`
by a natural cocycle `ξ` of `A` on the cover `Spec L → Spec K`. The twist is given by
natural local isomorphisms `e` with discrepancy `ξ`, so `H` is an inner form of `G`.
Let `y` be a `K`-rational point of `H` whose all-test centralizer lies in a closed
`K`-torus `S` of `H`.

Then there are:

- a `K`-rational point `x` of `G`;
- a closed `K`-torus `T` of `G` containing the all-test centralizer of `x`;
- a finite Galois extension `L'/K` and a morphism of covers `r : Spec L' ⟶ Spec L`
  over `K`;
- a point `g ∈ G(L')` such that `e` at `r` carries `g x g⁻¹` to `y`.

See the statement's Markdown for the precise meaning of each hypothesis.

## Proof

The proof applies one published implication to two published unconditional theorems.

1. `quasiSplitSimplyConnectedRegularConjugate_of_classRational` (module
   `Rational/QuasiSplitRegularConjugateReduction`, Worker 1601). Its hypotheses are
   `QuasiSplitRegularClassRationalStatement.{u}` and
   `RegularConjugateFiniteGaloisStatement.{u}`, and it concludes the target. The proof
   works as follows.
   - Let `z` be the point of `G` over the cover that `e` at the identity point
     carries to `y`.
   - Its centralizer in `G_L` lies in the closed `L`-torus obtained from `S` by base
     change and transport along `e`.
   - Each Galois conjugate `σ ≫ z` is conjugate to `z` over the algebraic closure of
     `L`. The conjugating element is a lift, along the surjective isogeny `π`, of the
     cocycle value `ξ(𝟙, σ)`.
   - The first hypothesis then gives a rational `x` geometrically conjugate to `z`.
   - The second hypothesis makes the centralizer of `x` a closed `K`-torus. It also
     realizes the conjugacy over a finite Galois `L'`.
   - Naturality of `e` at `r` translates this conjugacy back to `y`.
2. `quasiSplitRegularClassRational : QuasiSplitRegularClassRationalStatement.{u}`
   (module `Rational/QuasiSplitRegularClassRational`, Worker 4871, task
   `dd1d7a92-2f47-4d25-b340-c9e4a1ab4ed0`). This is Borel–Springer 8.6 for
   Galois-stable strongly regular classes. A strongly regular `L`-point of `G` whose
   class is stable under `Gal(L/K)` is geometrically conjugate to a `K`-rational point.
   It is proved through Steinberg's invariant quotient `ρ : G ⟶ V`, in four steps:
   - `z ≫ ρ` is Galois-fixed, so it descends to a `K`-point of `V`.
   - That point lifts to a `K`-point `x` of `G`.
   - `x` and `z` lie in one strongly regular fibre of `ρ`.
   - Such a fibre is a single geometric class, so `x` and `z` are conjugate.
3. `regularConjugateFiniteGalois : RegularConjugateFiniteGaloisStatement.{u}` (module
   `Rational/RegularConjugateFiniteGaloisProof`, Worker 1296). The proof runs as
   follows.
   - The centralizer of `x` is a closed subgroup that becomes isomorphic to a torus
     over a field, so it is a `K`-torus.
   - The transporter from `x` to `z` is smooth by fpqc descent, and it is affine and
     nonempty.
   - So it has a point over a finite Galois extension of `K`.

The supplied terms have exactly the hypothesis types of the implication. The theorem
therefore depends on no unproved statement. A `lean_check` of this module with the
declaration reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965), source
  `steinberg-1965-regular-elements-semisimple-groups`. Theorem 1.7 is on printed
  p.51 (PDF p.4). §10 is on printed p.78 (PDF p.31): the class of a strongly regular
  `y` of an inner twist is defined over `k`, so by 1.7 it contains an `x` over `k`.
  §11 is on printed p.79 (PDF p.32): Kneser's remark that cocycles modulo the centre
  suffice.
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic groups II*
  (1968), source `borel-springer-1968-rationality-properties-ii`, §8.6 (printed
  pp.483–484, PDF pp.41–42). It extends Theorem 1.7 for regular semisimple classes to
  arbitrary ground fields.

The implemented route follows Steinberg's §10, with two changes. It works on the finite
cover `Spec L → Spec K`, not with the twisted Galois action. It also replaces descent of
the conjugacy class by Galois descent of the single invariant value `z ≫ ρ`. Conjugacy
over an algebraic closure is replaced by conjugacy over a finite Galois `L'`. This uses
the smoothness of the transporter, which is a torsor under the centralizer torus.
