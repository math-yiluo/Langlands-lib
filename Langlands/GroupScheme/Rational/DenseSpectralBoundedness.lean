import Langlands.GroupScheme.Rational.FactorFamilyBoundedness
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalSpan
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.AlgebraicGeometry.PointTopology.ValuedAlgebraicExtension
import Langlands.GroupScheme.Reductive.RationalPointDensityStatement
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Spectral boundedness of dense rational-point families -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

section Coefficients

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

/-- Integral characteristic coefficients restricted to a specified set of
actual rational points. -/
def HasIntegralCharacteristicPolynomialsOn
    (ρ : MatrixRepresentation G (Fin N)) (B : Set (rationalPoints G)) : Prop :=
  ∀ g ∈ B, ∀ d,
    (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).charpoly.coeff d ≤ᵥ (1 : F)

end Coefficients

variable {k : Type u} [Field k] [IsAlgClosed k] [ValuativeRel k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsReduced G.X.left]
  {N : ℕ} {I : Type v} [Group I]

local instance denseSpectralBoundednessInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- A dense subgroup family with integral characteristic coefficients is
algebraically bounded for a smooth affine group with trivial unipotent radical
and a closed faithful coefficient representation. -/
theorem isAlgebraicallyBounded_range_of_dense
    (hG : HasTrivialUnipotentRadical G) (ρ : MatrixRepresentation G (Fin N))
    (hc : IsClosedSubgroup ρ) (α : I →* rationalPoints G)
    (hα : HasDenseRationalPointFamily α)
    (hint : ρ.HasIntegralCharacteristicPolynomialsOn (Set.range α)) :
    IsAlgebraicallyBounded k G.X (Set.range α) := by
  let F := simpleFactorFamily ρ
  apply F.isAlgebraicallyBounded_range_of_fullMatrixSpans hG hc α
  · intro i
    exact (F.factor i).span_rationalMatrix_comp_eq_top_of_dense (F.simple i) α hα
  · exact fun a d => hint _ ⟨a, rfl⟩ d

end MatrixRepresentation

/-- The scalar-extension/descent step, with the geometric point monoid supplied
explicitly. Density and all matrix coefficient assumptions concern its image. -/
theorem isAlgebraicallyBounded_of_dense_geometricPointHom
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      IsClosedSubgroup ρ → ρ.HasIntegralCharacteristicPolynomials →
      ∀ (α : rationalPoints G →* rationalPoints
        ((GroupScheme.baseChange (toAlgebraicClosure F)).obj G)),
        (∀ g, α g = geometricRationalPoint (K := AlgebraicClosure F) G.X g) →
        HasDenseRationalPointFamily α →
        IsAlgebraicallyBounded F G.X Set.univ := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  intro N ρ hc hint α hα hdense
  let K := AlgebraicClosure F
  let e := localFieldAlgebraicValuation F K
  let := e.relation
  let := e.extension
  let b := toAlgebraicClosure F
  let J := (GroupScheme.baseChange b).obj G
  let ρK := ρ.baseChange b
  let : Smooth J.X.hom := inferInstanceAs (Smooth
    (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : IsAffineHom J.X.hom := inferInstanceAs (IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : IsReduced J.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K J.X.left J.X.hom
  let : IsAffine J.X.left := isAffine_of_isAffineHom J.X.hom
  have hcK : IsClosedSubgroup ρK :=
    (hc.baseChange b).comp_iso (GeneralLinear.baseChangeIso (Fin N) b)
  have hintK : ∀ g d,
      (ρK.rationalMatrix (α g) : Matrix (Fin N) (Fin N) K).charpoly.coeff d ≤ᵥ (1 : K) := by
    intro g d
    rw [hα g]
    exact (MatrixRepresentation.charpoly_coeff_baseChange_geometricRationalPoint_vle_one_iff
      ρ g d).mpr (hint g d)
  have hB : IsAlgebraicallyBounded K J.X (Set.range α) :=
    ρK.isAlgebraicallyBounded_range_of_dense
      hG.hasTrivialGeometricUnipotentRadical hcK α hdense (by
        rintro _ ⟨g, rfl⟩ d
        exact hintK g d)
  apply isAlgebraicallyBounded_of_geometricRationalPoint G.X e.cofinal Set.univ
  have hrange : geometricRationalPoint (K := K) G.X '' Set.univ = Set.range α := by
    rw [Set.image_univ]
    congr 1
    exact (funext hα).symm
  change IsAlgebraicallyBounded K J.X
    (geometricRationalPoint (K := K) G.X '' Set.univ)
  erw [hrange]
  exact hB


end Langlands.GroupScheme
