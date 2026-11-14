import Langlands.GroupScheme.Rational.DenseSpectralBoundedness
import Langlands.GroupScheme.IntegralModel
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension

/-! # Spectral boundedness of dense rational subgroup families over local fields -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A specified dense family of ground-field sections remains dense after
extension of scalars. -/
theorem hasDenseRationalPointFamily_geometricRationalPoint
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type v} (X : Over (Spec (CommRingCat.of k)))
    (p : I → RationalPoint k X) (hp : HasDenseRationalPointFamily p) :
    HasDenseRationalPointFamily (fun i => geometricRationalPoint (K := K) X (p i)) := by
  have h := hp.preimage
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isOpenMap
  simpa only [HasDenseRationalPointFamily, Set.preimage_iUnion,
    ← range_geometricRationalPoint (K := K) X] using h

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- A dense subgroup family with integral characteristic polynomials in a
closed faithful representation of a connected reductive local-field group is
algebraically bounded. -/
def DenseSubgroupSpectralBoundednessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∀ (I : Type v) [Group I] (α : I →* rationalPoints G),
      HasDenseRationalPointFamily α →
      ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
        ρ.HasIntegralCharacteristicPolynomialsOn (Set.range α) →
        IsAlgebraicallyBounded F G.X (Set.range α)

/-- Scalar extension to the algebraic closure reduces the local-field family
criterion to the published algebraically closed family criterion. -/
theorem denseSubgroupSpectralBoundedness :
    DenseSubgroupSpectralBoundednessStatement.{u, v} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  intro I _ α hdense N ρ hc hint
  let K := AlgebraicClosure F
  let e := localFieldAlgebraicValuation F K
  let := e.relation
  let := e.extension
  let b := toAlgebraicClosure F
  let J := (GroupScheme.baseChange b).obj G
  let ρK := ρ.baseChange b
  let β := (baseChangeSectionHom b G).comp α
  have hβ (i : I) : β i = geometricRationalPoint (K := K) G.X (α i) := by
    apply Over.OverMorphism.ext
    rw [MonoidHom.comp_apply, baseChangeSectionHom_left]
    rfl
  let : Smooth J.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom J.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : IsReduced J.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K J.X.left J.X.hom
  let : IsAffine J.X.left := isAffine_of_isAffineHom J.X.hom
  have hcK : IsClosedSubgroup ρK :=
    (hc.baseChange b).comp_iso (GeneralLinear.baseChangeIso (Fin N) b)
  have hdenseK : HasDenseRationalPointFamily β := by
    change Dense (⋃ i : I, Set.range (β i).left)
    simp only [hβ]
    change HasDenseRationalPointFamily
      (fun i => geometricRationalPoint (K := K) G.X (α i))
    exact hasDenseRationalPointFamily_geometricRationalPoint (K := K) G.X α hdense
  have hintK : ρK.HasIntegralCharacteristicPolynomialsOn (Set.range β) := by
    rintro _ ⟨i, rfl⟩ d
    rw [hβ i]
    exact (MatrixRepresentation.charpoly_coeff_baseChange_geometricRationalPoint_vle_one_iff
      ρ (α i) d).mpr (hint _ ⟨i, rfl⟩ d)
  have hB : IsAlgebraicallyBounded K J.X (Set.range β) :=
    ρK.isAlgebraicallyBounded_range_of_dense
      hG.hasTrivialGeometricUnipotentRadical hcK β hdenseK hintK
  apply isAlgebraicallyBounded_of_geometricRationalPoint G.X e.cofinal (Set.range α)
  have hrange :
      geometricRationalPoint (K := K) G.X '' Set.range α = Set.range β := by
    rw [← Set.range_comp]
    congr 1
    exact (funext hβ).symm
  change IsAlgebraicallyBounded K J.X
    (geometricRationalPoint (K := K) G.X '' Set.range α)
  erw [hrange]
  exact hB

end Langlands.GroupScheme
