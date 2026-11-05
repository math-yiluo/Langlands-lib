import Langlands.GroupScheme.Rational.ScalarExtensionTopology
import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.Rational.PointTopology
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Integral models on the original coefficient-point carrier -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

namespace GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

variable [IsAffine G.X.left] [TopologicalSpace L] [IsTopologicalRing L]

private instance changedAffine : IsAffine (baseChanged k L G).X.left := by
  change IsAffine (pullback G.X.hom (baseMap k L))
  infer_instance

local instance coefficientTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of k L)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k L)

local instance genericTopology :
    TopologicalSpace (rationalPoints (baseChanged k L G)) :=
  rationalPointTopology L (baseChanged k L G).X

/-- The published multiplicative comparison preserves the canonical topologies. -/
theorem isHomeomorph_baseChangeCoeffEquiv :
    IsHomeomorph (baseChangeCoeffEquiv k L G) := by
  let e :=
    (rationalPointsAffineHomeomorph (baseChanged k L G)).trans
      (affinePointsBaseChangeContinuousMulEquiv k L L G).symm.toHomeomorph
  have he : (baseChangeCoeffEquiv k L G :
      rationalPoints (baseChanged k L G) →
        G.affinePoints (CommAlgCat.of k L)) = e := by
    funext x
    apply Over.OverMorphism.ext
    change (baseChangeCoeffEquiv k L G x).left =
      ((affinePointsBaseChangeMulEquiv k L L G).symm
        (rationalPointsAffineHomeomorph (baseChanged k L G) x)).left
    rw [baseChangeCoeffEquiv_left, affinePointsBaseChangeMulEquiv_symm_left,
      rationalPointsAffineHomeomorph_left]
  rw [he]
  exact e.isHomeomorph

end GaloisPointComparison

namespace IntegralModel

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {R : Type u} [CommRing R] [IsDomain R] [Algebra R L] [IsFractionRing R L]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (M : IntegralModel R L (baseChanged k L G))

/-- Evaluate an integral section in the original group's actual coefficient points. -/
def coefficientPointMap : M.integralSections →* G.affinePoints (CommAlgCat.of k L) :=
  (baseChangeCoeffEquiv k L G).toMonoidHom.comp M.integralPointMap

/-- This evaluation uses the actual integral inclusion, generic isomorphism and projection. -/
theorem coefficientPointMap_left (x : M.integralSections) :
    (M.coefficientPointMap k L x).left =
      (pullback.lift ((Spec.algebraMap R L) ≫ x.left) (𝟙 _)
        (by simp [Category.assoc, x.w]) ≫ M.genericIso.hom.hom.hom.left) ≫
          pullback.fst G.X.hom (baseMap k L) := by
  change (baseChangeCoeffEquiv k L G (M.integralPointMap x)).left = _
  rw [baseChangeCoeffEquiv_left, integralPointMap_left]

/-- The integral model's image, as a subgroup of the original coefficient-point group. -/
def coefficientIntegralPoints : Subgroup (G.affinePoints (CommAlgCat.of k L)) :=
  (M.coefficientPointMap k L).range

theorem mem_coefficientIntegralPoints (x : G.affinePoints (CommAlgCat.of k L)) :
    x ∈ M.coefficientIntegralPoints k L ↔
      ∃ s : M.integralSections, M.coefficientPointMap k L s = x :=
  Iff.rfl

/-- The subgroup is precisely the image of the already defined integral-point subgroup. -/
theorem coefficientIntegralPoints_eq_map :
    M.coefficientIntegralPoints k L =
      M.integralPoints.map (baseChangeCoeffEquiv k L G).toMonoidHom :=
  MonoidHom.range_comp _ _

/-- Membership is reflected by the inverse of the existing actual-point comparison. -/
theorem mem_coefficientIntegralPoints_iff (x : G.affinePoints (CommAlgCat.of k L)) :
    x ∈ M.coefficientIntegralPoints k L ↔
      (baseChangeCoeffEquiv k L G).symm x ∈ M.integralPoints := by
  rw [coefficientIntegralPoints_eq_map, Subgroup.mem_map_equiv]

/-- A compatible integral-model morphism preserves the coefficient-point evaluations. -/
theorem Hom.coefficientPointMap_naturality
    {H : GroupScheme (Spec (CommRingCat.of k))}
    {N : IntegralModel R L (baseChanged k L H)} {f : G ⟶ H}
    (φ : M.Hom N ((baseChange (baseMap k L)).map f)) (x : M.integralSections) :
    N.coefficientPointMap k L (rationalPoints.map φ.hom x) =
      G.affinePointsTarget f (CommAlgCat.of k L) (M.coefficientPointMap k L x) := by
  change baseChangeCoeffEquiv k L H
      (N.integralPointMap (rationalPoints.map φ.hom x)) = _
  rw [φ.integralPointMap_naturality]
  exact baseChangeCoeffEquiv_map k L f (M.integralPointMap x)

variable [IsAffine G.X.left] [TopologicalSpace L] [IsTopologicalRing L]

private instance changedAffine : IsAffine (baseChanged k L G).X.left := by
  change IsAffine (pullback G.X.hom (baseMap k L))
  infer_instance

local instance coefficientTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of k L)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k L)

local instance genericTopology :
    TopologicalSpace (rationalPoints (baseChanged k L G)) :=
  rationalPointTopology L (baseChanged k L G).X

/-- Compactness agrees for the two canonical point topologies. -/
theorem isCompact_coefficientIntegralPoints_iff :
    IsCompact (M.coefficientIntegralPoints k L :
      Set (G.affinePoints (CommAlgCat.of k L))) ↔
      IsCompact (M.integralPoints : Set (rationalPoints (baseChanged k L G))) := by
  rw [coefficientIntegralPoints_eq_map, Subgroup.coe_map]
  exact (baseChangeCoeffContinuousMulEquiv k L G).toHomeomorph.isCompact_image

/-- Maximality among compact supergroups transfers to the original coefficient points. -/
theorem coefficientIntegralPoints_maximal
    (hmax : ∀ K : Subgroup (rationalPoints (baseChanged k L G)),
      IsCompact (K : Set (rationalPoints (baseChanged k L G))) →
        M.integralPoints ≤ K → K = M.integralPoints) :
    ∀ K : Subgroup (G.affinePoints (CommAlgCat.of k L)),
      IsCompact (K : Set (G.affinePoints (CommAlgCat.of k L))) →
        M.coefficientIntegralPoints k L ≤ K →
        K = M.coefficientIntegralPoints k L := by
  intro K hK hle
  let e := baseChangeCoeffContinuousMulEquiv k L G
  have hcompact : IsCompact (K.comap e.toMonoidHom :
      Set (rationalPoints (baseChanged k L G))) :=
    e.toHomeomorph.isCompact_preimage.mpr hK
  have hinc : M.integralPoints ≤ K.comap e.toMonoidHom := by
    intro x hx
    apply hle
    rw [mem_coefficientIntegralPoints_iff]
    change (baseChangeCoeffEquiv k L G).symm
      (baseChangeCoeffEquiv k L G x) ∈ M.integralPoints
    simpa only [MulEquiv.symm_apply_apply] using hx
  have heq := hmax (K.comap e.toMonoidHom) hcompact hinc
  ext x
  rw [mem_coefficientIntegralPoints_iff, ← heq]
  change x ∈ K ↔
    baseChangeCoeffEquiv k L G ((baseChangeCoeffEquiv k L G).symm x) ∈ K
  rw [MulEquiv.apply_symm_apply]

omit [IsAffine G.X.left] [TopologicalSpace L] [IsTopologicalRing L] in
/-- A literal parabolic-left product transfers without changing the coefficient carrier. -/
theorem coefficientIntegralPoints_covering
    {P : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G)
    (hcover :
      Set.range (rationalPoints.map ((baseChange (baseMap k L)).map p)) *
        (M.integralPoints : Set _) = Set.univ) :
    Set.range (P.affinePointsTarget p (CommAlgCat.of k L)) *
      (M.coefficientIntegralPoints k L : Set _) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (baseChangeCoeffEquiv k L G).symm x ∈
      Set.range (rationalPoints.map ((baseChange (baseMap k L)).map p)) *
        (M.integralPoints : Set _) := by
    rw [hcover]
    trivial
  obtain ⟨a, ⟨y, rfl⟩, b, hb, hab⟩ := hx
  refine ⟨baseChangeCoeffEquiv k L G
      (rationalPoints.map ((baseChange (baseMap k L)).map p) y),
    ⟨baseChangeCoeffEquiv k L P y,
      (baseChangeCoeffEquiv_map k L p y).symm⟩,
    baseChangeCoeffEquiv k L G b, ?_, ?_⟩
  · change baseChangeCoeffEquiv k L G b ∈ M.coefficientIntegralPoints k L
    rw [mem_coefficientIntegralPoints_iff, MulEquiv.symm_apply_apply]
    exact hb
  · dsimp only at hab ⊢
    rw [← map_mul, hab, MulEquiv.apply_symm_apply]

end IntegralModel
end Langlands.GroupScheme
