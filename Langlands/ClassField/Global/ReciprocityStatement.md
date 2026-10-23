# Local invariants of global classes and the reciprocity law

Let `E / F` be a finite Galois extension of number fields and let `G = Gal(E/F)`. This
module gives every class `x` in the actual group `H²(G, Eˣ)` (Library
`relativeCohomology F E 2`) a local invariant in `ℚ/ℤ` at each place of `F`. It then states
the reciprocity law: the local invariants of `x` sum to zero. It has two Prop-valued
statements, `CyclicCyclotomicReciprocity` for cyclic subextensions of cyclotomic extensions
and `GlobalReciprocity` for all finite Galois extensions.

The finite local invariants are not fixed in advance. They come from an arbitrary family `I`
of local invariant maps (`InvariantFamily`, module
`Langlands.ClassFieldTheory.Local.Invariants`). Both statements quantify over every `I` that
satisfies the class-formation axioms `RelativeClassFormation` and the normalization
`ArithmeticNormalization`. These are the hypotheses that the Library's global
fundamental-class statement places on `I`.

## Sources

- Milne, *Class Field Theory* v4.03 (`milne-2020-class-field-theory`), Chapter VII,
  Theorem 8.1(b), printed p.221 (PDF p.230): "Let L/K be a finite Galois extension of
  number fields. Then Σ invᵥ(α) = 0 for all α ∈ H²(L/K)." The text after Lemma 8.5, printed
  p.223 (PDF p.232), proves the case of cyclic cyclotomic extensions first and then deduces
  the general case (Lemma 8.6). Footnote 6 (printed p.222) defines cyclotomic: `L ⊂ K[ζ]` for
  some root of unity `ζ`.
- Artin–Tate, *Class Field Theory* (`artin-tate-2009-class-field-theory`), Chapter VII §3,
  printed pp.41–45 (PDF pp.50–54). The local components `c_p ∈ H²(G_p, K_p)` and the
  invariants `inv_p c = inv_p c_p` and `inv c = Σ_p inv_p c` are defined on printed pp.41–42.
  Theorem 6 (printed p.45) states that `inv c = 0` for `c ∈ H²(G, K*)`, and its Case 1 treats
  cyclic cyclotomic extensions of `ℚ`.
- The archimedean invariant: Milne Chapter IV §4, "The real numbers", printed p.139
  (PDF p.148), says `H²(ℂ/ℝ) ≅ Ĥ⁰(G, ℂˣ) = ℝˣ/Nm ℂˣ = {±}`. Its nonzero element is
  represented by the 2-cocycle with value `-1` at `(σ, σ)`, for `σ` complex conjugation, and
  value `1` elsewhere. Milne Chapter VIII §4, printed p.240 (PDF p.249), says that for real
  `v`, `invᵥ` is an isomorphism of `Br(Kᵥ)` onto `½ℤ/ℤ`.

## Definitions

### Lifting to `H²`

- `Reciprocity.H2Lift φ hφ : H² A →+ B` turns an additive map `φ` on 2-cocycles that
  vanishes on 2-coboundaries into an additive map on `H²`. It evaluates `φ` on a chosen
  cocycle representative (`Function.surjInv` of the surjection `H2π`). The choice does not
  matter: `H2Lift_H2π` says `H2Lift φ hφ (H2π x) = φ x` for every cocycle `x`. The module
  also proves `H2π_surjective`.

### Finite places

- `Reciprocity.finiteLocalInvariant v w I : H²(G, Eˣ) →+ ℚ/ℤ` is defined for a finite place
  `v` of `F` (a height-one prime of `𝓞 F`) and a finite place `w` of `E` with
  `w.asIdeal.LiesOver v.asIdeal`. It composes the Library map
  `unitsLocalMap v w 2 : H²(G, Eˣ) → H²(Gal(E_w/F_v), E_wˣ)` (restriction along
  `decompositionHom v w`, with the coefficient map `Eˣ → E_wˣ`) with the relative invariant
  map `(I p).relative` of `E_w / F_v`. Here `p = residuePrime v` and `F_v` is presented as
  the `PadicField` `padicField v`. This is Artin–Tate's `inv_p c_p` for `c` the image of `x`
  in the idèle cohomology. Shapiro's lemma identifies the semilocal component at `v` with
  `H²(G_w, E_w)`.

### Signs

- `Reciprocity.signClass z : ℚ/ℤ` is the class `1/2` when `z.re < 0` and `0` otherwise, for
  `z : ℂ`.
- Lemmas: `rationalClass_half_add_half` (`1/2 + 1/2 = 0` in `ℚ/ℤ`); `signClass_mul` says the
  sign class is multiplicative on nonzero real complex numbers (imaginary part `0`);
  `signClass_star_mul_self` says `signClass (z̄ z) = 0`.

### Infinite places

- `Reciprocity.conjugationValue c f : Eˣ` is the unit `f(c,c) · f(1,1)` for `c ∈ G` and a
  2-cochain `f`. Cochains take values in the additive module `Additive Eˣ`, and the sum
  `f(c,c) + f(1,1)` is read back multiplicatively. `conjugationValue_add` says it is
  multiplicative in `f`.
- `conjugationValue_fixed`: if `c * c = 1` and `f` is a 2-cocycle, then `c` fixes
  `f(c,c) · f(1,1)`. The proof applies the cocycle identity at `(c, c, c)` with
  `f(1, c) = f(1, 1)` and `f(c, 1) = c(f(1, 1))`.
- `isConj_of_mem_stabilizer`: a nontrivial `c ∈ G` that fixes the infinite place `w` is the
  complex conjugation of `w`, i.e. `ComplexEmbedding.IsConj w.embedding c`. The proof uses
  Mathlib's `InfinitePlace.mem_stabilizer_mk_iff`. `conjugation_mul_self` says such a `c`
  satisfies `c * c = 1`.
- `embedding_conjugationValue_im`: for that `c` and a 2-cocycle `f`, the complex number
  `w.embedding (f(c,c) · f(1,1))` is real.
- `Reciprocity.archimedeanCocycleHom w` is an additive map from 2-cocycles to `ℚ/ℤ`. If some
  nontrivial `c ∈ G` fixes `w`, it sends `f` to `signClass (w.embedding (f(c,c) · f(1,1)))`,
  with `c` chosen by `Classical.choose`. Otherwise it sends `f` to `0`. The choice does not
  matter, because the stabilizer then has the single nontrivial element `c`. Additivity
  follows from `signClass_mul`.
- `archimedeanCocycleHom_coboundary`: the map vanishes on 2-coboundaries. For
  `f(g,h) = g(b(h)) · b(gh)⁻¹ · b(g)`, the product `f(c,c) · f(1,1)` telescopes to
  `c(b(c)) · b(c)`. Its image under `w.embedding` is `z̄ z` with `z = w.embedding (b(c))`,
  a positive real number.
- `Reciprocity.archimedeanInvariant w : H²(G, Eˣ) →+ ℚ/ℤ` is
  `H2Lift (archimedeanCocycleHom w) archimedeanCocycleHom_coboundary`.

These definitions give the local invariant at an infinite place `v` of `F` below `w`. The
decomposition group `G_w` (the stabilizer of `w`) is trivial or `{1, c}`, with `c` the
complex conjugation of `w`. If `G_w` is trivial, then `H²(G_w, E_wˣ) = 0` and the
invariant is `0`. This covers `v` complex, and `v` real with `w` real. Otherwise `v` is real,
`w` is complex, and `w.embedding` identifies `E_w` with `ℂ`, with `c` acting by complex
conjugation. For the cyclic group `{1, c}`, the class of a 2-cocycle `f` in
`Ĥ⁰ = ℝˣ/Nm ℂˣ` is `f(1, c) · f(c, c) = f(1, 1) · f(c, c)`. This is the product of
`f(cⁱ, c)` over `i`, and coboundaries telescope to norms. Under `ℝˣ/ℝ_{>0} ≅ ½ℤ/ℤ` this
class is the sign class of `w.embedding (f(c,c) · f(1,1))`. On Milne's cocycle
(`f(c,c) = -1`, `f(1,1) = 1`) the value is `1/2`, as it must be. A normalized cocycle has
`f(1,1) = 1`, so the factor `f(1,1)` only matters for unnormalized representatives. The
group `½ℤ/ℤ` has a unique isomorphism to `{±}`, so no normalization convention enters at
the infinite places.

### The reciprocity predicate

- `Reciprocity.SumOfInvariantsVanishes I x` is a Prop, for a family `I` and a class
  `x ∈ H²(G, Eˣ)`. It says: for every choice `wf` of a finite place `wf v` of `E` above each
  finite place `v` of `F`, and every choice `wi` of an infinite place `wi v` of `E` above
  each infinite place `v` of `F` (Library `FinitePlacesAbove`, `InfinitePlacesAbove`):
  1. the function `v ↦ finiteLocalInvariant v (wf v) I x` has finite support;
  2. `∑ᶠ v, finiteLocalInvariant v (wf v) I x + ∑ v, archimedeanInvariant (wi v) x = 0`.

  The finite places of `F` are summed with `finsum` and the infinite places with a
  `Finset` sum over `InfinitePlace F`. The predicate quantifies over the choice of places
  above, so it fixes no particular choice. In the sources the choice is immaterial, since
  the completions and decomposition groups at the places above `v` are all isomorphic
  (Artin–Tate, printed p.41). This module does not prove that independence.

## Statements

- `CyclicCyclotomicReciprocity : Prop` (universe `u`). Fix a family
  `I : ∀ p [Fact p.Prime], InvariantFamily.{u,u} p` that satisfies
  `(I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization` for every prime `p`. Then
  for all number fields `F` and `E` in `Type u` with `E / F` Galois, `Gal(E/F)` cyclic, and
  an `F`-algebra embedding of `E` into Mathlib's `CyclotomicField m F` for some `m > 0`,
  every `x ∈ H²(Gal(E/F), Eˣ)` satisfies `SumOfInvariantsVanishes I x`.
- `GlobalReciprocity : Prop` (universe `u`). Under the same hypotheses on `I`, for all
  number fields `F` and `E` in `Type u` with `E / F` finite Galois, every
  `x ∈ H²(Gal(E/F), Eˣ)` satisfies `SumOfInvariantsVanishes I x`.

## Provenance and scope

`GlobalReciprocity` is Milne's Theorem VII.8.1(b) and Artin–Tate's Theorem 6 for number
fields. Two features are specific to this formalization.

- Abstract finite invariants. The source theorem is about the genuine local invariant maps.
  Here they are replaced by any family `I` that satisfies the axioms the Library uses for
  local class field theory. The genuine invariant maps satisfy these axioms. In a class
  formation, normalizing the invariants on unramified classes determines them on all
  classes, so no other family arises. This module does not prove that uniqueness. The
  quantification over `I` makes the result usable by the Library's global fundamental-class
  statement, which is stated for such `I`.
- `CyclicCyclotomicReciprocity` is the intermediate case in Milne's proof: Theorem 8.1(b)
  for cyclic cyclotomic extensions of an arbitrary number field (printed p.223). Artin–Tate's
  Case 1 is the same case over `ℚ`. Cyclotomic is expressed as "`E` embeds over `F` into
  `F(μ_m)`", following Milne's footnote 6.

The archimedean invariant is the explicit cocycle formula described above. It is not a
general archimedean local class field theory.
