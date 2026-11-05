import Langlands.GroupScheme.Rational.AnisotropicTorusCompactness
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Rational.SpectralCompactnessPrerequisites
import Langlands.LinearAlgebra.BoundedMatrixPowers

/-! # Integral matrices from compact sets of actual rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Every entry of the actual rational-point matrix is continuous for the
canonical rational-point topology. -/
theorem continuous_rationalMatrix_entry (ρ : MatrixRepresentation G n) (i j : n) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    Continuous (fun g : rationalPoints G => (ρ.rationalMatrix g : Matrix n n F) i j) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let a : AffineCoordinateRing F G.X :=
    ρ.hom.hom.left.appTop (GeneralLinear.entrySection n (CommRingCat.of F) i j)
  have hc : Continuous (fun g : rationalPoints G =>
      rationalPointAlgebraHom F G.X g a) :=
    (AlgPoint.continuous_eval a).comp
      ((affineSchemePointHomeomorph F G.X F).continuous.comp
        (rationalPointHomeomorph F G.X).continuous)
  convert hc using 1
  funext g
  rw [rationalMatrix_apply_apply]
  change _ = affineSchemePointEquiv F G.X F (rationalPointEquiv F G.X g) a
  rw [affineSchemePointEquiv_apply_eq_evaluation]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    ((rationalPointEquiv F G.X g).left.appTop a)
  rw [rationalPointEquiv_left]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of F)).hom (g.left.appTop
    (ρ.hom.hom.left.appTop (GeneralLinear.entrySection n (CommRingCat.of F) i j)))
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    ((g.left ≫ ρ.hom.hom.left).appTop
      (GeneralLinear.entrySection n (CommRingCat.of F) i j)) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The actual rational matrix, bundled as a continuous map. -/
def rationalMatrixContinuousMap (ρ : MatrixRepresentation G n) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    C(rationalPoints G, Matrix n n F) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  exact ⟨fun g => (ρ.rationalMatrix g : Matrix n n F),
    continuous_pi fun i => continuous_pi fun j => ρ.continuous_rationalMatrix_entry i j⟩

@[simp] theorem rationalMatrixContinuousMap_apply (ρ : MatrixRepresentation G n)
    (g : rationalPoints G) :
    ρ.rationalMatrixContinuousMap g = (ρ.rationalMatrix g : Matrix n n F) := rfl

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- All entries on a compact point set have a common nonzero valuative bound. -/
theorem exists_rationalMatrix_entry_bound (ρ : MatrixRepresentation G n)
    (C : Set (rationalPoints G))
    (hC : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact C) :
    ∃ b : F, b ≠ 0 ∧ ∀ g ∈ C, ∀ i j,
      (ρ.rationalMatrix g : Matrix n n F) i j ≤ᵥ b := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let D : Set F := ⋃ i : n, ⋃ j : n,
    (fun g : rationalPoints G => (ρ.rationalMatrix g : Matrix n n F) i j) '' C
  have hD : IsCompact D :=
    isCompact_iUnion fun i => isCompact_iUnion fun j =>
      hC.image (ρ.continuous_rationalMatrix_entry i j)
  obtain ⟨b, hb, h⟩ := IsCompact.exists_valuative_bound hD
  exact ⟨b, hb, fun g hg i j => h _ (Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨j, ⟨g, hg, rfl⟩⟩⟩)⟩

/-- If all nonnegative powers lie in one compact point set, their actual
representation matrix is integral over the canonical valuation integer subring. -/
theorem isIntegral_rationalMatrix_of_powers_mem_compact
    (ρ : MatrixRepresentation G n) (g : rationalPoints G)
    (C : Set (rationalPoints G))
    (hC : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact C) (hg : ∀ k : ℕ, g ^ k ∈ C) :
    IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix g : Matrix n n F) := by
  obtain ⟨b, hb, hbound⟩ := ρ.exists_rationalMatrix_entry_bound C hC
  apply Langlands.LinearAlgebra.isIntegral_matrix_of_bounded_powers
  refine ⟨b, hb, fun k i j => ?_⟩
  simpa only [map_pow, Units.val_pow_eq_pow_val] using hbound (g ^ k) (hg k) i j

/-- Compact rational-point groups have integral matrices in every actual
finite-dimensional representation. -/
theorem isIntegral_rationalMatrix_of_isCompact_univ
    (ρ : MatrixRepresentation G n)
    (hG : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (Set.univ : Set (rationalPoints G))) (g : rationalPoints G) :
    IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix g : Matrix n n F) :=
  ρ.isIntegral_rationalMatrix_of_powers_mem_compact g Set.univ hG (fun _ => Set.mem_univ _)

end MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Anisotropic tori give integral rational-point matrices for every representation. -/
theorem IsAnisotropic.isIntegral_rationalMatrix_of_isTorus
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsAnisotropic T.toGrp) (hTtor : IsTorus T.toGrp)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation T.toGrp n) (t : rationalPoints T.toGrp) :
    IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix t : Matrix n n F) := by
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  exact ρ.isIntegral_rationalMatrix_of_isCompact_univ
    (hT.isCompact_univ_of_isTorus hTtor) t

/-- In particular every actual representation of an anisotropic torus satisfies
the exact coefficient-bound predicate used by the reductive spectral target. -/
theorem IsAnisotropic.hasIntegralCharacteristicPolynomials_of_isTorus
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsAnisotropic T.toGrp) (hTtor : IsTorus T.toGrp)
    {N : ℕ} (ρ : MatrixRepresentation T.toGrp (Fin N)) :
    ρ.HasIntegralCharacteristicPolynomials := by
  intro t i
  apply (ValuativeRel.valuation F).vle_one_iff.mpr
  apply (Valuation.integer.integers (ValuativeRel.valuation F)).isIntegral_iff_v_le_one.mp
  exact Langlands.LinearAlgebra.isIntegral_charpoly_coeff
    (hT.isIntegral_rationalMatrix_of_isTorus hTtor ρ t) i

end Langlands.GroupScheme
