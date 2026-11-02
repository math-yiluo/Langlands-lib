# The dual-side Euler characteristic of a finite flat Mumford map

Authors: Worker 943 wrote the Lean file and the initial explanation; Worker 1089 checked
them against the Library, Mathlib and the source and revised the explanation.

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerStatement`,
namespace `Langlands.AbelianScheme`, with `open CategoryTheory AlgebraicGeometry`,
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules` and
`open Langlands.AlgebraicGeometry.Modules.DerivedSections`. The file defines one
universe-polymorphic proposition, `AlgClosedFieldMumfordDualEulerStatement.{u}`. It does
not prove it.

## Complete proposition

```lean
def AlgClosedFieldMumfordDualEulerStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : LineBundle A.X.left)
    (B : LineBundle (Spec (CommRingCat.of K)))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf (Spec (CommRingCat.of K)))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
    (f : A.X ⟶ dualScheme A hA),
    f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA →
      IsFinite f.left → Flat f.left →
    ∀ (g : ℕ), A.HasRelativeDimension g →
    ∀ (hQ : HasFiniteCohomology (mumfordProduct A).hom
        (tensorObj
          ((Scheme.Modules.pullback (mumfordAddition A)).obj
            (LineBundle.normalize preservation A.X.hom (unitSection A)
              (unitSection_comp A) L B evaluationB).obj.carrier)
          ((Scheme.Modules.pullback (Limits.pullback.snd A.X.hom A.X.hom)).obj M.obj)))
      (y : (dualScheme A hA).left),
      eulerCharacteristic (mumfordProduct A).hom
          (tensorObj
            ((Scheme.Modules.pullback (mumfordAddition A)).obj
              (LineBundle.normalize preservation A.X.hom (unitSection A)
                (unitSection_comp A) L B evaluationB).obj.carrier)
            ((Scheme.Modules.pullback (Limits.pullback.snd A.X.hom A.X.hom)).obj M.obj)) hQ =
        (-1) ^ g * (f.left.finrank y : ℤ)
```

Imports: `Langlands.AlgebraicGeometry.Picard.MumfordLineBundle`,
`Langlands.AlgebraicGeometry.Modules.EulerCharacteristic`,
`Mathlib.AlgebraicGeometry.Morphisms.FlatRank` and `Mathlib.FieldTheory.IsAlgClosed.Basic`.

## Meaning of the binders

All names are the published Library and Mathlib ones, used unchanged.

- `preservation` and `square` are the published propositions
  `pullbackTensorComparisonIsIsoStatement` and `MumfordBundlePicardZeroStatement`. They are
  taken as hypotheses, exactly as in the target
  `Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`, because the
  normalization `LineBundle.normalize` and the Mumford map `mumfordSchemeMapOfLineBundle`
  depend on them.
- `K` is an algebraically closed field in universe `u`, `A` a published `AbelianScheme` over
  `Spec K`, and `hA : HasDualScheme A` the chosen dual, with `dualScheme A hA`.
- `L` is an arbitrary line bundle on `A.X.left`; no ampleness is assumed. `B` and
  `evaluationB` trivialize `e^*L ⊗ B`, where `e = unitSection A`. Write
  `N := (LineBundle.normalize … L B evaluationB).obj.carrier`; by the Library's
  `LineBundle.normalize_forget` (which holds by `rfl`) its underlying line bundle is
  `LineBundle.tensor preservation L ((LineBundle.pullback π).obj B)`, with `π = A.X.hom`.
  Mathematically `N ≅ L`, since every line bundle on `Spec K` is trivial; the statement
  does not use this.
- `M` and `evaluation : N ⊗ M ≅ 𝒪_A` give an inverse of `N`.
- `f` is an arbitrary morphism over `Spec K` with `f = mumfordSchemeMapOfLineBundle …`, the
  actual Mumford map of the normalized family. `IsFinite f.left` and `Flat f.left` are the
  Mathlib morphism properties.
- `g` is the relative dimension, `A.HasRelativeDimension g`.
- `mumfordProduct A` is `Over.mk (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)`: the
  parameter-first self-product `A ×_K A` over `Spec K`, with `pullback.fst` the parameter
  coordinate and `pullback.snd` the `A`-coordinate. `mumfordAddition A` is the group law
  `m` on it. The coefficient is `Q := m^*N ⊗ snd^*M`, built with the Library's
  `tensorObj` and Mathlib's `Scheme.Modules.pullback`.
- `hQ` is an arbitrary proof of `HasFiniteCohomology (mumfordProduct A).hom Q`: every
  actual derived cohomology object `relativeCohomology (mumfordProduct A).hom n` of `Q` is
  a finite-dimensional `K`-vector space, and all of them vanish in sufficiently high
  degrees. `eulerCharacteristic` is the published alternating sum
  `∑ᶠ n, (-1)^n · dim_K` of these objects; its value does not depend on `hQ`.
- `f.left.finrank y` is Mathlib's `Scheme.Hom.finrank` of the underlying scheme morphism
  at `y`. Mathlib defines it through the chart `Spec R` of its chosen affine open cover of
  the dual that contains `y`: it is the rank at the prime of `y` (`Module.rankAtStalk`) of
  the global sections of the fibre product of `f.left` with this chart, an `R`-module; for
  finite `f` this is the coordinate ring of the preimage of the chart. Mathlib's documentation
  describes it as the rank of `f_* 𝒪_A` over `𝒪` at `y`, the degree of `f` at `y`; for a
  finite flat `f` it is locally constant (`Scheme.Hom.isLocallyConstant_finrank`, under
  locally finite presentation).

The conclusion is `χ(A ×_K A, m^*N ⊗ snd^*M) = (-1)^g · deg_y f` for every point `y` of the
dual, including non-closed points, and for every proof `hQ`. Every relative dimension `g`,
including `g = 0`, and every characteristic of `K` are included. The proposition imports
neither `Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement` nor any
proof of it.

## Source and correspondence

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), proof of the Riemann–Roch Theorem
(9.11), printed p.132 (PDF p.136). For a non-degenerate line bundle `L` on a
`g`-dimensional abelian variety `X` the source writes `Λ(L) = (id_X × φ_L)^*P` and derives,
from Theorem (9.1), flat base change and a Leray spectral sequence, formula (8)
`h^n(X × X, Λ(L)) = 0` for `n ≠ g` and `deg(φ_L)` for `n = g`, hence formula (9)
`χ(Λ(L)) = (-1)^g · deg(φ_L)`. Its formula (10), from the projection formula and the finite
support of the direct images, gives `H^n(X × X, Λ(L)) ≅ H^n(X × X, m^*L ⊗ p_1^*L^{-1})` for
all `n`. Together, `χ(m^*L ⊗ p_1^*L^{-1}) = (-1)^g · deg(φ_L)`.

In the Lean interface:

- The source's parameter is the second factor `p_2`; the Library's self-product is
  parameter-first, so the source's `p_1` (the `A`-coordinate) is `pullback.snd`.
- The source's `L` is the normalized `N` (isomorphic to `L`, because line bundles on
  `Spec K` are trivial), and `L^{-1}` is the supplied inverse `M`.
  The Library's Mumford family is
  `m^*N ⊗ fst^*M ⊗ snd^*M` (`mumfordFamilyOfLineBundle_forget`); `Q` omits the parameter
  factor `fst^*M`, as in the source's formula (10).
- The source's `φ_L` is the actual Mumford map `f`, classified by the Library's Poincaré
  family through `mumfordSchemeMapOfLineBundlePullbackIso`.
- The source works over an arbitrary field `k`; the Lean statement assumes `K`
  algebraically closed, so it is narrower in this respect.
- The source assumes `L` non-degenerate, i.e. `φ_L` is an isogeny. The Lean statement
  replaces this by the hypotheses `IsFinite f.left` and `Flat f.left`, and assumes nothing
  else about `L` (in particular no ampleness). In the source's setting a finite
  homomorphism from `X` to its dual, which has the same dimension, is an isogeny, and
  isogenies are flat, so the two conditions agree there; the Lean statement takes the two
  hypotheses directly and does not use this comparison.
- `deg(φ_L)` is replaced by Mathlib's native rank `f.left.finrank y` at an arbitrary point
  `y`. For the isogeny of the source the rank is the same at every point because the dual
  is connected; here the statement asserts the equality at every `y`.

## Role

Statement task `2590f5a1-e1c2-4ec1-ade7-377e97a3e12f`; its proof is a separate later task.
The proposition is an intermediate interface for the proof task
`fc8e4732-8e1b-497e-adb1-c27ee538f442` of the published
`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`. The planned
assembly there, which is not part of the Library, combines it with the shear and Künneth
computation `χ(Q) = χ(N) · χ(M)` (from the source's formula (11)) and with the
symmetry `χ(M) = (-1)^g χ(N)` stated in task `bf395772-bc6c-4f1c-8359-80a9ad561005`
(`Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement`, not yet in the
Library), giving `χ(L)² = deg_y f`.
