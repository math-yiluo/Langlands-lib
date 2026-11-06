import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.Representation.Jacquet.CompressionStabilizationStatement
import Langlands.Representation.Jacquet.IwahoriContraction
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.Characters
import Mathlib.NumberTheory.LocalField.Basic

/-! # Renard VI.9.1: uniform stabilization and the generalized Jacquet lemma

Statements only. Renard 2026, VI.9.1 (printed pp.195-197 / PDF pp.201-203), for the
parabolic `P = MN` of a cocharacter `χ` of a connected reductive group over a
nonarchimedean local field: `N` is the dynamic radical of `χ`, `M` its centralizer and
`N̄` the dynamic radical of the inverse cocharacter. A compact open subgroup `K` and a
`M`-central element `g` satisfy the published Iwahori contraction conditions.

* `UniformCompressionStabilizationStatement` is the Proposition of VI.9.1: one exponent
  `b`, chosen before the representation, from which on the power kernels and power ranges
  of the compressed action `v ↦ e_K(π(g)v)` on `V^K` are constant, for every smooth
  complex representation on a carrier of the fixed universe; the kernel supremum and the
  stable image split `V^K`.
* `GeneralizedJacquetLemmaStatement` is the Theorem of VI.9.1: the Jacquet quotient maps
  `V^K` onto `(V_N)^{K ∩ M}` for every smooth complex representation.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

/-- Renard VI.9.1 Proposition (uniform stabilization): for the dynamic parabolic of a
cocharacter `χ`, every compact open subgroup `K` and every `M`-central element `g`
satisfying the Iwahori contraction conditions for `(N, M, N̄)`, there is one exponent `b`
such that, for every smooth complex representation on a carrier in `Type v`, every power
range of exponent at least `b` of the compressed action of `g` on `V^K` is the stable
image, every such power kernel is the kernel supremum, and these two submodules are
complementary. -/
def UniformCompressionStabilizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
      (g : rationalPoints G),
      (∀ m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)), m * g = g * m) →
      Jacquet.IsIwahoriContraction K
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g →
      ∃ b : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
        (∀ s : ℕ, b ≤ s →
          Jacquet.stableImage ρ hρ K hK g =
              LinearMap.range (Jacquet.compressedAction ρ hρ K hK g ^ s) ∧
            Jacquet.powerKernelSup ρ hρ K hK g =
              LinearMap.ker (Jacquet.compressedAction ρ hρ K hK g ^ s)) ∧
          Jacquet.CompactCompressionSplits ρ hρ K hK g

/-- Renard VI.9.1 Theorem (generalized Jacquet lemma): for the dynamic parabolic of a
cocharacter `χ` and every compact open subgroup `K` admitting an `M`-central element `g`
with the Iwahori contraction conditions for `(N, M, N̄)`, the Jacquet quotient maps the
`K`-fixed vectors of every smooth complex representation on a carrier in `Type v` onto the
`K ∩ M`-fixed vectors of its Jacquet module. -/
def GeneralizedJacquetLemmaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
      ∀ g : rationalPoints G,
      (∀ m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)), m * g = g * m) →
      Jacquet.IsIwahoriContraction K
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g →
      ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (rationalPoints G) V), IsSmooth ρ →
        Function.Surjective
          (Jacquet.fixedJacquetMap ρ
            ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
            ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
            (Dynamic.centralizer_le_normalizer_unipotent χ (Over.mk (𝟙 _)))
            K.toSubgroup)

end Langlands.Aubert.General.RationalPointFamily
