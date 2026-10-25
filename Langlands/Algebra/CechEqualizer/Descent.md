# Auxiliary lemmas for noetherian approximation of the Čech criterion

Authors: Worker 299 and Worker 424. Worker 299 authored the proof;
Worker 424 adapted its module dependencies for separate prerequisite
publication and rechecked the complete proof. This helper module supports the proof of
`Langlands.Algebra.SmoothEqualizerFibreCriterion`. It contains internal
formal deductions from Mathlib; no literature result is formalized here.

## Spectra and faithful flatness of a base change

- `mem_range_comap_tensorProduct`: for `R`-algebras `S` and `T` (all in one
  universe), a prime `x` of `S` lies in the image of
  `Spec (S ⊗[R] T) → Spec S` whenever its contraction to `R` lies in the
  image of `Spec T → Spec R`. The proof uses the scheme-theoretic fact that a
  pair of points with the same image in `Spec R` lifts to the fibre product
  (`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`), and
  identifies the fibre product of spectra with `Spec (S ⊗[R] T)` via
  `AlgebraicGeometry.pullbackSpecIso`.
- `exists_sum_eq_one_of_isOpen`: let `U ⊆ Spec R` be open and suppose every
  prime of the `R`-algebra `A` contracts into `U`. Then there are a finite
  set `s ⊆ R` and coefficients `c : R → A` such that every basic open set
  `D(x)`, `x ∈ s`, lies in `U`, and `∑_{x ∈ s} c x * x = 1` in `A`. Write the
  complement of `U` as the zero locus of an ideal `J`; the extension of `J`
  to `A` is the unit ideal (otherwise a maximal ideal containing it would
  contract outside `U`), and a finite linear combination expressing `1`
  supplies `s` and `c`.
- `faithfullyFlat_of_sum_eq_one`: with `B` flat over `R`, if finitely many
  `x ∈ s` with `D(x)` inside the image of `Spec B → Spec R` generate the unit
  ideal of `A`, then `A ⊗[R] B` is faithfully flat over `A`. Each prime `P`
  of `A` avoids some `x ∈ s`, so its contraction lies in the image of
  `Spec B`; the first lemma lifts `P` to `Spec (A ⊗[R] B)`, and Mathlib's
  `Module.FaithfullyFlat.of_comap_surjective` concludes.

## Maps between base changes

Here `R → A₀ → A` is a scalar tower and `B` is an `R`-algebra.

- `map_ofId_injective`: if `A₀ → A` is injective and `B` is flat over `R`,
  then `A₀ ⊗[R] B → A ⊗[R] B` is injective (it is `rTensor` of an injective
  map by a flat module).
- `cancelBaseChange_tmul_eq_smul`: the isomorphism
  `A ⊗[A₀] (A₀ ⊗[R] B) ≅ A ⊗[R] B` sends `a ⊗ z` to `a • ι z`, where
  `ι : A₀ ⊗[R] B → A ⊗[R] B` is the base-change map.
- `sum_tmul_mem_range`: a finite sum `∑ aᵢ ⊗ bᵢ` in `A ⊗[R] B` whose left
  coefficients come from `A₀` lies in the range of `ι`.
- `exists_algHom_comp_eq`: let `ι : D → E` be an injective `A₀`-algebra map
  and `Ψ : A₀ ⊗[R] B → E` an `A₀`-algebra map. If `B` is generated as an
  `R`-algebra by a set `G` and `Ψ (1 ⊗ g)` lies in the range of `ι` for every
  `g ∈ G`, then `Ψ` factors as `ι ∘ φ` for an `A₀`-algebra map `φ`. The range
  of `ι` is a subalgebra; induction over `Algebra.adjoin` shows that it
  contains all of `Ψ`'s values, and `φ` is `Ψ` corestricted to the range,
  composed with the inverse of `ι` onto its range.
