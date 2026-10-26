# Proof of finite étale closure of algebra equalizers

This module proves the published proposition
`Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraFiniteEtale` from
`Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraStatements`. The final
theorem is

```lean
theorem Langlands.AlgebraicGeometry.FiniteEtale.equalizerAlgebraFiniteEtale
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.Etale R A] [Algebra.Etale R B]
    (f g : A →ₐ[R] B) :
    EqualizerAlgebraFiniteEtale R A B f g
```

It keeps every parameter of the statement's telescope, in the same universe
`u`. So for arbitrary `R`-algebra maps between finite étale algebras, Mathlib's
subalgebra `AlgHom.equalizer f g` is a finite `R`-module and is étale over `R`.
The theorem assumes nothing about noetherianity, connectedness or
nontriviality of `R`, and nothing about the size or splitting of `A` and `B`.
Zero rings and empty index sets are not excluded at any step. The axioms used
are `propext`, `Classical.choice` and `Quot.sound`.

## Route

The proof follows NYLL's `Algebra.Etale.equalizer`. Finiteness and étaleness
travel together as the pair `Module.Finite R S ∧ Algebra.Etale R S`. No
finite-étale class is introduced. The helpers are in the namespace
`Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebra`.

1. **Constant rank, locally.** Both properties are local on `Spec R` for basic
   open covers (`finite_and_etale_of_exists_of_isPrime`). For every prime `p`,
   `exists_cover_rankAtStalk_eq` gives an `r ∉ p` such that the rank function of
   `Rᵣ ⊗[R] A` is constant. Mathlib's `AlgHom.tensorEqualizerEquiv` identifies
   `Rᵣ ⊗[R] equalizer f g` with the equalizer of the base-changed maps, because
   `Rᵣ` is flat. The pair is transported back along this equivalence
   (`finite_and_etale_of_equiv`). The same step is then applied to `B`. This
   reduces the theorem to `finite_and_etale_equalizer_of_rankAtStalk_eq`, where
   `A` and `B` have constant ranks `n` and `m`.
2. **Splitting and descent.** If `A` is not finite split, Mathlib's
   `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` gives a faithfully flat
   `R`-algebra `T` for which `T ⊗[R] A` is finite split. Base change preserves the
   constant ranks (`Module.rankAtStalk_baseChange`) and commutes with the
   equalizer. The pair descends along `T`
   (`finite_and_etale_of_tensorProduct_of_faithfullyFlat`, which uses Mathlib's
   `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and
   `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`). The same step is
   then applied to `B`. This reduces the theorem to
   `finite_and_etale_equalizer_of_isFiniteSplit`.
3. **Function algebras.** `A ≃ₐ[R] Fin n → R` and `B ≃ₐ[R] Fin m → R` are
   chosen. The equalizer is transported along them (`equalizerCongr`), which
   reduces the theorem to `finite_and_etale_equalizer_fun` for maps
   `f g : (E → R) →ₐ[R] (F → R)` with `E` and `F` finite.
4. **Locally coordinate maps.** A general `R`-algebra map `(E → R) → (F → R)` is
   not a coordinate map. It is one only locally on `Spec R`, so connectedness of
   `Spec R` is never assumed.
   - `eq_compRight_of_isLocalRing` shows that over a local ring every such map is
     `compRight R R σ` (precomposition by some `σ : F → E`). A local ring has no
     nontrivial idempotents, and the images of the standard idempotents
     `Pi.single j 1` determine `σ`. An empty `E` is handled separately
     (`eq_compRight_of_no_nontrivial_isIdempotentElem'`).
   - `exists_cover_eq_compRight` applies this at `R_p`. It identifies the
     localizations of `E → R` and `F → R` with `E → R_p` and `F → R_p` using
     Mathlib's `IsLocalizedModule.pi`. `exists_cover_eq_of_eq` then spreads the
     resulting equality of localized maps to some `Rᵣ` with `r ∉ p`. That lemma
     uses module finiteness and
     `Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule`.
   - `exists_cover_eq_compRight₂` does this for `f` and `g` at once, over
     `R_{rr'}`, using `Algebra.TensorProduct.cancelBaseChange`.
5. **Coequalizers.** On such an `Rᵣ`, the base-changed equalizer is identified
   with `Rᵣ ⊗[R] equalizer (compRight σ) (compRight τ)` by two applications of
   `AlgHom.tensorEqualizerEquiv` and `equalizerCongrOfEq`.
   `equalizerCompRightEquiv` identifies `equalizer (compRight σ) (compRight τ)`
   with the function algebra on the finite set `Function.Coequalizer σ τ`, so it
   is finite split (`isFiniteSplit_equalizer_compRight`). Mathlib's instances
   then make its base change finite split, and hence finite and étale. Locality
   (step 1) finishes `finite_and_etale_equalizer_fun`.

## Helper declarations

The following are all in `Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebra`.

- **Locality on `Spec R`:**
  - `ofLocalizationSpan_of_exists_of_isPrime` and
    `ofLocalizationSpan_of_exists_of_isPrime'` (the base-change form, which uses
    `IsLocalization.Away.tensorEquiv`).
  - `etale_of_exists_of_isPrime`, `finite_of_exists_of_isPrime` and
    `finite_and_etale_of_exists_of_isPrime`. These use Mathlib's
    `RingHom.Etale.ofLocalizationSpan` and `RingHom.finite_ofLocalizationSpan`.
- **Transport and descent:** `finite_and_etale_of_equiv` and
  `finite_and_etale_of_tensorProduct_of_faithfullyFlat`.
- **Spreading out:** `exists_cover_eq_of_eq` and `exists_cover_rankAtStalk_eq`.
  The second uses `Module.isLocallyConstant_rankAtStalk`.
- **Equalizer transport:** `equalizerCongr` and `equalizerCongrOfEq`.
- **Function algebras:**
  - `compRight`, `finite_coequalizer` (a local instance) and
    `equalizerCompRightEquiv`.
  - `isFiniteSplit_equalizer_compRight`.
  - `eq_compRight_of_no_nontrivial_isIdempotentElem` (and its primed form),
    `isIdempotentElem_iff_eq_zero_or_eq_one_of_isLocalRing` and
    `eq_compRight_of_isLocalRing`.
  - `exists_cover_eq_compRight` and `exists_cover_eq_compRight₂`.
- **Reduction steps and source theorem:**
  - `finite_and_etale_equalizer_fun`,
    `finite_and_etale_equalizer_of_isFiniteSplit` and
    `finite_and_etale_equalizer_of_rankAtStalk_eq`.
  - `finite_and_etale_equalizer`, the conjunction form of the source theorem.

The module also makes
`Module.FinitePresentation.of_finite_of_finitePresentation` a local instance, as
the source does. The module imports only the statement module and Mathlib. It
adds no global instances, no finite-étale class and no axioms.

## Source and provenance

The registered source is `external-lean-reuse-snapshots-2026-10-21`, SHA256
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The files are
under
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/`
at NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709`:

- **`Equalizer.lean`:** lines 45–516, from `AlgHom.exists_cover_eq_of_eq` to
  `Algebra.Etale.equalizer`. The source's `RingHom.eq_compRight_of_isLocalHom` is
  renamed `eq_compRight_of_isLocalRing` here. The source's
  `AlgHom.exists_cover_eq_compRight''` and its `₂` form are renamed
  `exists_cover_eq_compRight` and `exists_cover_eq_compRight₂`. The source's
  `RingHom.IsFiniteSplit` and `RingHom.compRight` are not needed and are omitted.
- **`Basic.lean`:** lines 44–149, the locality lemmas and `of_equiv`. The
  lemma `IsUnit.tmul` and the instance at line 51 are not used and are omitted.
- **`Descent.lean`:** lines 36–45.

The source bundles the two properties in a class `Algebra.FiniteEtale`. Here
every source lemma about that class is restated for the explicit conjunction.
For example, `Algebra.FiniteEtale.of_equiv` becomes `finite_and_etale_of_equiv`.
Source instance arguments become explicit hypotheses or local `have`s. Other
adaptations:

- Declarations are moved into a project namespace.
- Two `let`-bound base rings are disambiguated by naming the equalizer argument
  explicitly.
- One local `have` replaces a source instance (`isFiniteSplit_equalizer_compRight`).
- Two unused local definitions in the base-change locality lemma are dropped.

The mathematical route is unchanged.

The source files credit Christian Merten and are NYLL-maintained adaptations of
pi1 code under Apache-2.0. Attribution is documented in the registered supplement
`nyll-classfieldtheory-fbd320cd-supplement`, SHA256
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`; see `ATTRIBUTION.md`
and `UPSTREAM.json` in its `files/Nyll/EtaleFundamentalGroups/Pi1/` directory. The
Lean file keeps the Apache-2.0 notice and Merten's authorship, and cites the pi1
comparison sources at commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`. That
revision is not established as the historical NYLL import revision. The
project's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` retain the upstream
license and the notices for these three files. The adaptation to this Library is
by Worker 266.
