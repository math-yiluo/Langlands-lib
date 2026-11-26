# Lifting and rigidity along nilpotent thickenings of affine schemes

Module `Langlands.AlgebraicGeometry.AffineNilpotentThickening`, namespace
`Langlands.AlgebraicGeometry.AffineNilpotentThickening`.

Throughout, `R → R₀` is a surjective homomorphism of commutative rings whose kernel `K` is
nilpotent (`hsurj`, `hnil`), and `c = Spec R₀ ⟶ Spec R` is the corresponding closed
immersion.

## Algebra

- `bijective_of_sub_mem I hI φ h`: an `R`-linear endomorphism `φ` of an `R`-algebra `A`
  with `φ a - a ∈ I A` for every `a`, where `I` is a nilpotent ideal of `R`, is bijective.
  Put `δ = φ - id`. By `R`-linearity `δ` maps `I^n A` into `I^(n+1) A`, so `δ` is
  nilpotent in `Module.End R A`, and `φ = 1 + δ` is a unit there (Mathlib's
  `IsNilpotent.isUnit_one_add` and `Module.End.isUnit_iff`).
- `ker_includeLeft_le`: the kernel of `A → A ⊗[R] R₀`, `a ↦ a ⊗ 1`, lies in `K A`. The
  proof identifies `R₀` with `R ⧸ K` and uses Mathlib's
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`.
- `isNilpotent_ker_includeLeft`: hence that kernel is nilpotent.
- `isIso_of_restrict_eq`: an endomorphism `g` of `Spec A` over `Spec R` that restricts to
  the identity on `Spec (A ⊗[R] R₀)` is an isomorphism. Writing `g = Spec φ`, the
  hypotheses say that `φ` is an `R`-algebra map with `φ a - a` in the kernel of
  `A → A ⊗[R] R₀`, and `bijective_of_sub_mem` applies.

## Schemes

Let `U` be an affine scheme with `p : U ⟶ Spec R`, and let `W` be its fibre over `Spec R₀`,
given by a pullback square `hW : IsPullback a w p c` with `a : W ⟶ U`.

- `globalAlgebra p`: the `R`-algebra structure on `Γ(U, ⊤)` determined by `p`
  (`specMap_globalAlgebra`).
- `exists_fibreIso`: an isomorphism `e : W ≅ Spec (Γ(U, ⊤) ⊗[R] R₀)` with
  `e.hom ≫ Spec(includeLeft) ≫ U.isoSpec.inv = a`. It compares `hW` with the pullback
  square of spectra of the tensor product (Mathlib's `isPullback_SpecMap_of_isPushout` and
  `CommRingCat.isPushout_tensorProduct`), transported along `U.isoSpec`.
- `exists_lift`: if `f : Z ⟶ Spec R` is smooth, every morphism `z : W ⟶ Z` over `Spec R`
  extends to `y : U ⟶ Z` over `Spec R` with `a ≫ y = z`. This is the published
  `smoothThickeningLifting` for the surjection `Γ(U, ⊤) → Γ(U, ⊤) ⊗[R] R₀` with nilpotent
  kernel.
- `isIso_of_fibre`: an endomorphism `g` of `U` over `Spec R` with `a ≫ g = a` is an
  isomorphism (`isIso_of_restrict_eq` transported along `U.isoSpec`).
- `exists_iso_of_fibre`: two smooth affine schemes `U`, `U'` over `Spec R` with fibre
  squares `hW`, `hW'` over the same `w : W ⟶ Spec R₀` are isomorphic over `Spec R` by an
  isomorphism `h : U' ≅ U` with `a' ≫ h.hom = a`. Lifts `y : U' ⟶ U` and `y' : U ⟶ U'` of
  `a` and `a'` exist by `exists_lift`; both composites restrict to the identity on `W`, so
  they are isomorphisms by `isIso_of_fibre`, and `y` is an isomorphism.

## Provenance

Internal derived content. `exists_iso_of_fibre` is the uniqueness of smooth lifts of
affine schemes across nilpotent thickenings, as in Kai-Wen Lan, *Arithmetic
compactifications of PEL-type Shimura varieties*, Harvard thesis revised 14 March 2021,
Lemma 2.1.1.7 (printed p. 114, PDF p. 142), registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`. The proof here uses
the published infinitesimal lifting theorem `smoothThickeningLifting` and the linear
nilpotence argument above.
