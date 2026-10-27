# Essential finite presentation under base change (Stacks 0AUF): proof

This proof module imports the published statement
`Langlands.Algebra.EssFinitePresentationBaseChangeStatement` and the published
transport proof `Langlands.Algebra.EssFinitePresentationTransportProof`.
It changes neither of them, nor the predicate `Langlands.Algebra.EssFinitePresentation`,
nor any of their imports. Its closing theorem is
`Langlands.Algebra.essFinitePresentationBaseChange.{u, v, w}`. The complete type of that
theorem is `Langlands.Algebra.EssFinitePresentationBaseChangeStatement.{u, v, w}`, with
the statement's three independent universes and no further outer parameters or
hypotheses. The final example checks this complete type with the unapplied constant
`@essFinitePresentationBaseChange.{u, v, w}`.

Unfolded, the theorem says the following. Let `R : Type u`, `A : Type v`, and `B : Type w`
be arbitrary commutative rings with given `R`-algebra structures, and suppose
`EssFinitePresentation R A`. Then `EssFinitePresentation B (B ⊗[R] A)` holds. Here
`B ⊗[R] A` is Mathlib's tensor product with its left-factor `B`-algebra, whose map is
`b ↦ b ⊗ 1`.

## Reusable interface

- `Langlands.Algebra.essFinitePresentation_baseChange` takes `R` and `A` implicitly and `B`
  explicitly, along with commutative-ring structures on all three and `R`-algebra
  structures on `A` and `B`. Its explicit premise is `h : EssFinitePresentation R A`, and it
  concludes `EssFinitePresentation B (B ⊗[R] A)` for the left-factor `B`-algebra. The
  universes are the same as in the statement. A typical use is
  `essFinitePresentation_baseChange B h`.
- `Langlands.Algebra.essFinitePresentation_baseChange_of_algEquiv_localization` is the
  auxiliary step, with four independent universes: `R : Type u`, `Q : Type v`,
  `A : Type w`, and `B : Type z`. Given `[Algebra.FinitePresentation R Q]`, an arbitrary
  `M : Submonoid Q` and `e : Localization M ≃ₐ[R] A`, it concludes
  `EssFinitePresentation B (B ⊗[R] A)` for an arbitrary `R`-algebra `B`.

There are no assumptions on `B` beyond its commutative ring and `R`-algebra structures.
In particular, there is no local, Noetherian, flatness, injectivity, nontriviality, or
finite-presentation hypothesis. The submonoid `M` is arbitrary, so it may contain zero or
zero divisors, and zero rings are allowed throughout.

## Implemented proof

**Unpacking the witness.** `essFinitePresentation_baseChange` destructs `h` into `n`, an
ideal `I` of `MvPolynomial (Fin n) R` with `I.FG`, a submonoid
`M` of `Q = MvPolynomial (Fin n) R ⧸ I`, and `e : Localization M ≃ₐ[R] A`. Mathlib's
`Algebra.FinitePresentation.quotient` turns `I.FG` into
`Algebra.FinitePresentation R Q`, since the polynomial ring has its finite-presentation
instance. The proof then applies the auxiliary theorem with this `Q`, `M`, and `e`.

The auxiliary theorem is stated for an abstract finitely presented algebra `Q`. This is a
technical choice. With `Q` literally the quotient `MvPolynomial (Fin n) R ⧸ I`,
instance synthesis in pinned Mathlib fails for `CommRing (B ⊗[R] Localization M)`. With
an abstract `Q` the same instance is found.

**The auxiliary theorem.** Write `L = Localization M`, with its canonical `Q`-algebra and
`R`-algebra structures and the canonical scalar tower `R → Q → L`.

1. *Finite presentation after base change.* Mathlib's instance
   `Algebra.FinitePresentation.baseChange` (in `Mathlib.RingTheory.FiniteStability`) makes
   `B ⊗[R] Q` finitely presented over `B`. The proof finds this by instance search; it adds
   no hypothesis about `B`.
2. *The algebra map `B ⊗[R] Q → B ⊗[R] L`.* Let
   `φ = Algebra.TensorProduct.map (AlgHom.id B B) (IsScalarTower.toAlgHom R Q L)`, so
   `φ (b ⊗ q) = b ⊗ algebraMap Q L q`. This is a `B`-algebra homomorphism, and the proof
   equips `B ⊗[R] L` with the `B ⊗[R] Q`-algebra structure `φ.toAlgebra`. The scalar tower
   `B → B ⊗[R] Q → B ⊗[R] L` holds because `φ` commutes with the left-factor algebra maps,
   by `φ.commutes`. The compatibility equation required by Mathlib is

   ```text
   (algebraMap (B ⊗[R] Q) (B ⊗[R] L)).comp includeRight
     = includeRight.comp (algebraMap Q L),
   ```

   where `includeRight` is `q ↦ 1 ⊗ q`. It is checked pointwise as
   `φ (1 ⊗ q) = 1 ⊗ algebraMap Q L q`, which follows from `map_tmul`.
3. *Localization after base change.* With these data, Mathlib's
   `IsLocalization.tensorProduct_tensorProduct_right R B M L H`
   (in `Mathlib.RingTheory.Localization.BaseChange`) shows that `B ⊗[R] L` is the
   localization of `B ⊗[R] Q` at `M.map includeRight`, the submonoid of elements
   `1 ⊗ m` with `m ∈ M`.
4. *Essential finite presentation of `B ⊗[R] L`.* The published constructor
   `essFinitePresentation_of_isLocalization`, applied to `B`, `B ⊗[R] Q`, `B ⊗[R] L`, and
   the submonoid `M.map includeRight`, gives `EssFinitePresentation B (B ⊗[R] L)`. The
   constructor uses the tower from step 2, the finite presentation from step 1, and the
   localization from step 3.
5. *Transport to `B ⊗[R] A`.* Mathlib's `Algebra.TensorProduct.congr`, applied to the
   identity `B ≃ₐ[B] B` and `e`, gives a `B`-algebra equivalence
   `B ⊗[R] L ≃ₐ[B] B ⊗[R] A` sending `b ⊗ x` to `b ⊗ e x`. Its `B`-algebra structures are
   the left-factor ones on both sides. The published
   `essFinitePresentation_of_algEquiv` transports the result of step 4 along it.

The closing theorem `essFinitePresentationBaseChange` introduces the statement's binders
and applies `essFinitePresentation_baseChange`. The proof uses only the axioms
`propext`, `Classical.choice`, and `Quot.sound`. It uses no `sorry` or native computation.

The module does not prove essential-finite-type base change or composition closure, and
it does not identify any specific residue-field fibre. It reproves neither Mathlib's
finite-presentation and localization base-change results nor the published transport
lemmas. It never replaces the tensor product by an abstract pushout.

## Provenance

The original is the Stacks Project Authors, *The Stacks Project*, Commutative Algebra,
Section 10.54, Lemma 10.54.3 ([tag 0AUF](https://stacks.math.columbia.edu/tag/0AUF)). The
part proved here is its essential-finite-presentation assertion. The definition is
Definition 10.54.1 ([tag 00QM](https://stacks.math.columbia.edu/tag/00QM)), and Comment
#2262 fixes the convention that localization inverts an arbitrary multiplicatively
closed subset. The registered source is `stacks-algebra-flatness-criteria-2026-10-22`,
file `07DR.html`, folder SHA-256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.

The source omits the proof of Lemma 10.54.3 ("Proof. Omitted."). This module is therefore
an independent proof. It uses the published EFP transport API
(`essFinitePresentation_of_isLocalization`, `essFinitePresentation_of_algEquiv`) and
pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, specifically
`Mathlib.RingTheory.FiniteStability`, `Mathlib.RingTheory.Localization.BaseChange`, and
`Mathlib.RingTheory.TensorProduct.Maps`. No source-specific errata file was present.

Worker 254 implemented the Lean proof and this explanation. The suggested route, through
finite-presentation base change, tensor-localization base change, the published
localization constructor, and transport along `Algebra.TensorProduct.congr`, was given in
the task context. That context was written by the statement's author, Worker 708, from
Worker 336's target formulation and dependency routing.
