/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Compactification.Dense

/-!

# Projective compactification of an affine piece

Let `U` be quasi-compact (e.g. affine) over a quasi-separated (e.g. Noetherian) base `S` and
let `ι : U ⟶ 𝔸(n; S)` be an immersion over `S`. Let `Ū` be the scheme-theoretic image of the
composite `κ : U ⟶ 𝔸(n; S) ⟶ ℙ(Option n; S)`. We record that

- `Ū ⟶ ℙ(Option n; S)` is a closed immersion, hence `Ū ⟶ S` is proper;
- `U ⟶ Ū` is a quasi-compact, scheme-theoretically dense open immersion;
- `U ⟶ Ū ⟶ S` is the given morphism `U ⟶ S`.

This is the compactification `AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`,
which is therefore dense.

## Main results

- `AlgebraicGeometry.AffineSpace.projectiveClosure_spec` — the properties listed above.
- `AlgebraicGeometry.Compactification.isDense_ofIsImmersionAffineSpace` — the compactification
  `Compactification.ofIsImmersionAffineSpace` is dense.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {U S : Scheme.{u}} {n : Type u} [Finite n]

/-- Projective compactification of an affine piece.

Let `U` be quasi-compact over a quasi-separated base `S` (e.g. `U` affine and `S`
Noetherian), let `ι : U ⟶ 𝔸(n; S)` be an immersion over `S` and let
`κ = ι ≫ (𝔸(n; S) ⟶ ℙ(Option n; S))`. Then the scheme-theoretic image `Ū = κ.image` is a
closed subscheme of `ℙ(Option n; S)`, `Ū ⟶ S` is proper, `U ⟶ Ū` is a quasi-compact,
scheme-theoretically dense open immersion, and `U ⟶ Ū ⟶ S` is the given morphism. -/
theorem AffineSpace.projectiveClosure_spec [CompactSpace U] [QuasiSeparatedSpace S]
    {f : U ⟶ S} (ι : U ⟶ 𝔸(n; S)) [IsImmersion ι] (hι : ι ≫ 𝔸(n; S) ↘ S = f) :
    IsClosedImmersion (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).imageι ∧
      IsProper ((ι ≫ AffineSpace.toRelativeProjectiveSpace n S).imageι ≫ ℙ(Option n; S) ↘ S) ∧
      IsOpenImmersion (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).toImage ∧
      QuasiCompact (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).toImage ∧
      IsSchemeTheoreticallyDominant (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).toImage ∧
      (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).toImage ≫
          (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).imageι ≫ ℙ(Option n; S) ↘ S = f := by
  have : QuasiCompact ((ι ≫ AffineSpace.toRelativeProjectiveSpace n S) ≫
      ℙ(Option n; S) ↘ S) := quasiCompact_of_compactSpace _
  have : QuasiCompact (ι ≫ AffineSpace.toRelativeProjectiveSpace n S) :=
    .of_comp _ (ℙ(Option n; S) ↘ S)
  have : QuasiCompact (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).toImage := by
    have : QuasiCompact ((ι ≫ AffineSpace.toRelativeProjectiveSpace n S).toImage ≫
        (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).imageι) := by
      rwa [Scheme.Hom.toImage_imageι]
    exact .of_comp _ (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).imageι
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc, Category.assoc,
    AffineSpace.toRelativeProjectiveSpace_over, hι]

/-- The compactification `Compactification.ofIsImmersionAffineSpace` is dense: its open
immersion is scheme-theoretically dominant. -/
theorem Compactification.isDense_ofIsImmersionAffineSpace {f : U ⟶ S} (ι : U ⟶ 𝔸(n; S))
    [IsImmersion ι] [QuasiCompact f] (hι : ι ≫ 𝔸(n; S) ↘ S = f) :
    (Compactification.ofIsImmersionAffineSpace ι hι).IsDense := by
  have : QuasiCompact (ι ≫ AffineSpace.toRelativeProjectiveSpace n S) := by
    have : QuasiCompact ((ι ≫ AffineSpace.toRelativeProjectiveSpace n S) ≫
        ℙ(Option n; S) ↘ S) := by
      rwa [Category.assoc, AffineSpace.toRelativeProjectiveSpace_over, hι]
    exact .of_comp _ (ℙ(Option n; S) ↘ S)
  exact inferInstanceAs
    (IsSchemeTheoreticallyDominant (ι ≫ AffineSpace.toRelativeProjectiveSpace n S).toImage)

end AlgebraicGeometry
