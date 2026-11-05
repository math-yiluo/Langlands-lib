import Langlands.Group.GL.AlgebraicPointTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Rational.Characters
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Closed sets of rational points with bounded matrix entries are compact

Over a nonarchimedean local field `F`, normed by `LocalGalois.localNormedField`, let `ρ` be a
closed linear embedding of an affine group scheme `G`. A closed set of rational points of `G`, in
the canonical rational-point topology, whose matrices and inverse matrices have uniformly bounded
entries is compact: `ρ` is a closed embedding of rational points into `GL_N(F)`, and the set of
invertible matrices with bounded entries and bounded inverse entries is compact. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Invertible matrices with bounded entries and bounded inverse entries form a compact set. -/
theorem isCompact_generalLinear_bounded (N : ℕ) (C : ℝ) :
    letI := LocalGalois.localNormedField F
    IsCompact {g : Langlands.GeneralLinear N F | ∀ k l,
      ‖(g : Matrix (Fin N) (Fin N) F) k l‖ ≤ C ∧
        ‖((g⁻¹ : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F) k l‖ ≤ C} := by
  let := LocalGalois.localNormedField F
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  set K₀ : Set (Matrix (Fin N) (Fin N) F) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : F) C with hK₀
  have hK : IsCompact K₀ :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 C
  have hKop : IsCompact (MulOpposite.unop ⁻¹' K₀ : Set (Matrix (Fin N) (Fin N) F)ᵐᵒᵖ) :=
    (MulOpposite.opHomeomorph.symm.isCompact_preimage).mpr hK
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hK.prod hKop)
  have key : ∀ a : Matrix (Fin N) (Fin N) F, a ∈ K₀ ↔ ∀ k l, ‖a k l‖ ≤ C := by
    intro a
    change (∀ k ∈ Set.univ, ∀ l ∈ Set.univ, a k l ∈ Metric.closedBall (0 : F) C) ↔ _
    simp only [Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  convert h using 1
  ext g
  change _ ↔ ((g : Matrix (Fin N) (Fin N) F) ∈ K₀ ∧
    ((g⁻¹ : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F) ∈ K₀)
  rw [key, key]
  exact ⟨fun hg => ⟨fun k l => (hg k l).1, fun k l => (hg k l).2⟩,
    fun hg k l => ⟨hg.1 k l, hg.2 k l⟩⟩

/-- **Bounded closed sets are compact.** -/
theorem isCompact_of_isClosed_of_bounded {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    [IsClosedImmersion ρ.hom.hom.left] (B : Set (rationalPoints G))
    (hB : letI := rationalPointTopology F G.X; IsClosed B) (C : ℝ)
    (hC : letI := LocalGalois.localNormedField F
      ∀ g ∈ B, ∀ k l, ‖(ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F) k l‖ ≤ C ∧
        ‖(((ρ.rationalMatrix g)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) k l‖ ≤ C) :
    letI := rationalPointTopology F G.X
    IsCompact B := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.left :=
    inferInstanceAs (IsAffine (Spec _))
  let : TopologicalSpace
      (RationalPoint F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X) :=
    rationalPointTopology F _
  have : T2Space F := by
    let := LocalGalois.localNormedField F
    exact inferInstance
  have hemb := isClosedEmbedding_rationalPointMap F ρ.hom.hom
  let e := (GeneralLinear.rationalPointsContinuousMulEquiv N F).toHomeomorph
  have hE : IsClosedEmbedding fun g : rationalPoints G => e (g ≫ ρ.hom.hom) :=
    e.isClosedEmbedding.comp hemb
  have he : ∀ g : rationalPoints G, e (g ≫ ρ.hom.hom) = ρ.rationalMatrix g := by
    intro g
    apply Units.ext
    ext i j
    change (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) (g ≫ ρ.hom.hom) :
      Matrix (Fin N) (Fin N) F) i j = _
    rw [GeneralLinear.rationalPointsEquiv_apply_apply,
      MatrixRepresentation.rationalMatrix_apply_apply]
  rw [hE.isInducing.isCompact_iff]
  refine (isCompact_generalLinear_bounded N C).of_isClosed_subset (hE.isClosedMap B hB) ?_
  rintro _ ⟨g, hg, rfl⟩
  dsimp only
  rw [he]
  exact hC g hg

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
