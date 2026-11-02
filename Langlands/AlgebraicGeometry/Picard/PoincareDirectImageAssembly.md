# Assembly of the higher direct images of the Poincaré bundle

Authors: Worker 975 and Worker 1165.

Module `Langlands.AlgebraicGeometry.Picard.PoincareDirectImageAssembly`, namespace
`Langlands.AbelianScheme.PoincareDirectImage`. It derives the Library proposition
`Langlands.AbelianScheme.AlgClosedFieldPoincareDirectImageStatement` from three Library
propositions, which the first two theorems take as hypotheses and do not prove:

- `Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement` (the algebra of
  (9.7)–(9.9));
- `Langlands.AbelianScheme.AlgClosedFieldDualSchemeRelativeDimensionStatement` (the dual is
  smooth of relative dimension `g`);
- `Langlands.AbelianScheme.AlgClosedFieldPoincareTangentSectionsStatement` (the
  first-order tangent condition).

Everything else is proved in the imported helper modules. There are no proof holes.

## Declarations

- `algClosedFieldPoincareDirectImage_of hAL hGEO hTAN hS` additionally takes the support
  hypothesis `hS` of `homology_of_perfectModel` as an explicit argument.
- `algClosedFieldPoincareDirectImage_of_prerequisites hAL hGEO hTAN` discharges `hS` with
  Worker 1165's `poincare_isZero_homology_localization_of_mem_originIdeal` (module
  `PoincareDirectImageAffineVanishing`). Its type is
  `AlgClosedFieldPoincareDirectImageStatement.{u}`.
- `algClosedFieldPoincareDirectImage_of_relativeDimension hGEO` supplies the Library proofs
  `Langlands.CommutativeAlgebra.regularLocalPunctualComplex` and
  `Langlands.AbelianScheme.algClosedFieldPoincareTangentSections` for the first and third
  hypotheses. Its only remaining hypothesis is
  `AlgClosedFieldDualSchemeRelativeDimensionStatement.{u}`, which is not yet proved in the
  Library.

## Proof

Let `K` be algebraically closed, `A` an abelian scheme of relative dimension `g` over
`Spec K`, `D` the chosen dual and `p : A ×_K D ⟶ D` the projection. Let `P` be the
Poincaré bundle.

1. `hGEO` gives `SmoothOfRelativeDimension g D.hom`, so `D ⟶ Spec K` is smooth and locally
   of finite type. Mathlib's `exists_isAffineOpen_mem_and_subset` gives an affine open `V`
   containing the origin.
2. The family `affineFamily hV` over `Spec Γ(D, V)` is smooth of relative dimension `g`
   and proper. The Library's `universalPerfectSections` gives a strictly perfect complex
   `Kc` over `Γ(D, V)`. It represents the derived sections of `affinePoincare hV`, and its
   scalar extensions represent the derived sections of every base change.
3. The support hypothesis holds by `poincare_isZero_homology_localization_of_mem_originIdeal`.
   Then `homology_of_perfectModel` (module `PoincareDirectImageLocal`) gives `Hⁿ(Kc) = 0`
   for `n ≠ g` and `H^g(Kc) ≅ Γ(D, V) ⧸ m`, where `m` is the ideal of the origin.
4. The higher direct images `Rⁿ p_* P` have finite closed support
   (`poincareDirectImage_hasFiniteClosedSupport`). So
   `nonempty_affineSections_higherDirectImage_iso_homology` identifies their sections over
   `V` with `Hⁿ(Kc)`. The pullback square used there is the defining square of
   `affineFamily hV`.
5. `Rⁿ p_* P` is supported at the origin (`poincareDirectImage_stalkSupport_subset`), and
   the origin is closed (`isClosed_originPoint`). For `n ≠ g`, `isZero_of_isZero_affineSections`
   shows `Rⁿ p_* P = 0`. For `n = g`, `nonempty_iso_pushforward_of_affineSections_iso` (with
   the origin as the section of `D ⟶ Spec K`) identifies `R^g p_* P` with the pushforward of
   the structure sheaf of `Spec K` along the origin. These are the two conjuncts of the target.

This follows the second proof of Theorem (9.1) in Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`),
(9.6)–(9.9), printed pp.128–130 (PDF pp.132–134). The source computes the stalk of
`R^g p_* P` at the origin. Here the support statements and the computation over an affine
neighbourhood replace the passage between stalks and sheaves.
