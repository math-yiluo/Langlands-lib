# Higher direct images of the Poincaré bundle over an algebraically closed field: proof

Author of this pair: Worker 3612. It assembles published Library results; the conditional
development it relies on (modules `PoincareDirectImageSupport`,
`PoincareDirectImageAffineVanishing`, `PoincareDirectImageLocal`,
`PoincareDirectImageLocalAlgebra`, `PoincareDirectImageAssembly` and the `Modules` helpers
listed below) was written by Workers 975 and 1165, and the relative-dimension input by
Worker 3643 (see its own Markdown).

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareDirectImageProof`,
namespace `Langlands.AbelianScheme`. The file contains one theorem,

```lean
theorem algClosedFieldPoincareDirectImage : AlgClosedFieldPoincareDirectImageStatement.{u}
```

whose type is exactly the published proposition
`Langlands.AbelianScheme.AlgClosedFieldPoincareDirectImageStatement` (module
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareDirectImageStatement`), at an
arbitrary universe `u` and with no further hypotheses. The statement pair is imported
unchanged.

## What is proved

For every algebraically closed field `K : Type u` (of any characteristic), every abelian
scheme `A` over `Spec K`, every `hA : HasDualScheme A` and every `g : ℕ` (including `g = 0`)
with `A.HasRelativeDimension g`: write `D = dualScheme A hA`,
`p = ((baseChange D.hom).obj A).X.hom : A ×_K D ⟶ D` and `P = poincareLineBundle A hA`. Then

1. `(higherDirectImage p n).obj P.obj` is a zero object of `D.left.Modules` for every
   `n ≠ g`, and
2. `(higherDirectImage p g).obj P.obj` is isomorphic to
   `(Scheme.Modules.pushforward (dualOrigin A hA).left).obj (structureSheaf (Spec K))`, the
   skyscraper module with value `K` at the origin of `D`.

`higherDirectImage p n` is the Library's right-derived functor
`(Scheme.Modules.pushforward p).rightDerived n` (module
`Langlands.AlgebraicGeometry.Modules.DerivedSections`); no other cohomology model is used.
The statement Markdown explains every object.

## Implemented proof

The proof is one application:

```lean
PoincareDirectImage.algClosedFieldPoincareDirectImage_of_relativeDimension
  algClosedFieldDualSchemeRelativeDimension
```

- `Langlands.AbelianScheme.PoincareDirectImage.algClosedFieldPoincareDirectImage_of_relativeDimension`
  (module `Langlands.AlgebraicGeometry.Picard.PoincareDirectImageAssembly`) has type
  `AlgClosedFieldDualSchemeRelativeDimensionStatement.{u} → AlgClosedFieldPoincareDirectImageStatement.{u}`.
- `Langlands.AbelianScheme.algClosedFieldDualSchemeRelativeDimension` (module
  `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionProof`) is the
  published proof of `AlgClosedFieldDualSchemeRelativeDimensionStatement.{u}`: over an
  algebraically closed field, the chosen dual of an abelian scheme of relative dimension `g`
  is smooth of relative dimension `g` over `Spec K`. It is itself unconditional: it combines
  the published proofs `mumfordBundlePicardZero` and
  `GroupScheme.algebraicallyClosedFieldAmpleExistence` with the local finite presentation of
  the chosen dual proved in `Picard.DualSchemeSubalgebraFactorization`.

### How the published assembly proves the statement

The assembly theorem takes the relative-dimension proposition as its only hypothesis; the two
other inputs of the underlying `algClosedFieldPoincareDirectImage_of_prerequisites` are the
Library proofs `Langlands.CommutativeAlgebra.regularLocalPunctualComplex` (the algebra of
(9.7)–(9.9)) and `Langlands.AbelianScheme.algClosedFieldPoincareTangentSections` (the
first-order tangent condition). Its proof, documented in `PoincareDirectImageAssembly.md`,
runs as follows.

1. The relative-dimension input makes `D ⟶ Spec K` smooth of relative dimension `g`, hence
   locally of finite type; choose an affine open `V ∋ 0` of `D`, with ring `B = Γ(D, V)`.
2. The Library's `universalPerfectSections` gives a strictly perfect complex `Kc` of
   `B`-modules representing the derived sections of the Poincaré bundle over `Spec B`,
   compatibly with every base change `B ⟶ T`.
3. Support (`PoincareDirectImageSupport`, `PoincareDirectImageAffineVanishing`): at a
   rational point `y ≠ 0` of `D` the restriction of `P` to the fibre is a nontrivial
   translation-invariant bundle, so all its cohomology vanishes
   (`algClosedFieldTranslationInvariantCohomologyVanishing`); by the Library's open-local
   rational-fibre vanishing theorem, every `Rⁿ p_* P` vanishes off the origin, and `Kc`
   becomes acyclic after inverting any function vanishing at the origin.
4. Local algebra at the origin (`PoincareDirectImageLocal`, `homology_of_perfectModel`): the
   stalk of `D` at the origin is regular of dimension `g`; the fibre at the origin has
   `h⁰ = 1` and no cohomology above `g`; the tangent condition excludes first-order
   thickenings. The punctual-complex theorem then gives `Hⁿ(Kc) = 0` for `n ≠ g` and
   `H^g(Kc) ≅ B ⧸ m₀`, where `m₀` is the ideal of the origin.
5. Sheaf level (`Modules/AffineHigherDirectImageSections`, `Modules/PointSupportedSkyscraper`,
   `Modules/PointSupportedPushforward`): since all `Rⁿ p_* P` have finite closed support, the
   Leray comparison `finiteClosedSupportLeray` identifies their sections over `V` with
   `Hⁿ(Kc)`. A module supported at the closed origin vanishes when these sections vanish,
   and is the pushforward of `𝒪_{Spec K}` along the origin when they are `B ⧸ m₀`. This
   gives the two conjuncts.

## Dependencies and admissibility

- Only published Library proofs are used; no statement enters as a hypothesis. The proof
  uses no `sorry`, no `admit` and no new axiom; inspection reports only `propext`,
  `Classical.choice` and `Quot.sound`.
- The import closure contains neither
  `Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement` nor
  `Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`, nor any module importing
  them, nor any consequence of the target.
- No ampleness, projectivity, polarization, characteristic, duality, Noetherian or existence
  hypothesis is added. The ample-existence and Mumford inputs used inside the published
  relative-dimension proof are published proofs, not assumptions.

## Source

Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`), Theorem (9.1), printed
p.126 (PDF p.130), direct-image half, over an algebraically closed field. The implemented
route is the source's second proof, steps (9.2) (support) and (9.6)–(9.9) (local algebra at
the origin), printed pp.126–130 (PDF pp.130–134); the Serre-duality step of (9.2) and the
Grothendieck-duality proof (9.4)–(9.5) are not used. In the source, `X^t` has dimension `g`
by Theorem (6.18); here this is the published relative-dimension proof.
