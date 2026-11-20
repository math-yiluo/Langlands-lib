import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.MatrixRepresentationDenseCompact
import Langlands.GroupScheme.MatrixRepresentationPolynomialImage
import Langlands.Group.FormSelfAdjointMean
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.GroupScheme.Rational.RealCompactMatrixPoints
import Langlands.GroupScheme.Rational.RealCompactPoints
import Langlands.GroupScheme.Rational.ScalarExtensionTopology
import Langlands.GroupScheme.Rational.MatrixEntryBoundedCompactness
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.Torus.RationalCharacterSeparation

/-! # Matrix conjugation for compact real forms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Matrix Topology
open scoped CategoryTheory.MonObj ComplexOrder
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.DenseCompactForm Langlands.Group.FormSelfAdjointMean
open Langlands.Group.AlgebraicMatrixPowers (IsPolynomiallyDefined)

namespace Langlands.GroupScheme
namespace RealCompactFormUniqueness

open Langlands.GroupScheme.GeneralLinear (Coordinate values)
open GaloisPointComparison
open RationalCharacterSeparation
open RealCompactForm (eval_eq_zero_of_dense rationalMatrix_eq_coeffMatrix
  rationalMatrix_baseChange_extend extendedRationalMatrix MatrixFixedByBaseAutomorphisms
  HasConjugatorToGaloisFixedPoints)

local notation "RealGroup" => GroupScheme (Spec (CommRingCat.of ℝ))

section Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A form preserved by a dense real matrix subgroup detects real
entries among the complex matrices preserving that form. -/
private theorem conjGL_eq_of_preserves_form (A K : Subgroup (GL n ℂ))
    (hdense : ∀ p : MvPolynomial (Coordinate n) ℂ,
      (∀ k ∈ K, MvPolynomial.eval (values k) p = 0) →
        ∀ g ∈ A, MvPolynomial.eval (values g) p = 0)
    (J : GL n ℂ) (hK : ∀ k ∈ K, star k * J * k = J)
    (hreal : ∀ k ∈ K, conjGL k = k) {g : GL n ℂ}
    (hg : g ∈ A) (hJ : star g * J * g = J) : conjGL g = g := by
  have adjoint_eq_inverse (x : GL n ℂ) (hx : star x * J * x = J) :
      J⁻¹ * star x * J = x⁻¹ := by
    calc
      J⁻¹ * star x * J = J⁻¹ * (star x * J * x) * x⁻¹ := by group
      _ = x⁻¹ := by rw [hx]; group
  have hginv : conjGL g⁻¹ = g⁻¹ := by
    apply Units.ext
    ext i j
    let p := adjointCoordinate J (.entry i j) - MvPolynomial.X (.inverseEntry i j)
    have hp (x : GL n ℂ) (hx : star x * J * x = J) :
        MvPolynomial.eval (values x) p = (conjGL x⁻¹) i j - (x⁻¹ : GL n ℂ) i j := by
      rw [show p = adjointCoordinate J (.entry i j) - MvPolynomial.X (.inverseEntry i j) by rfl,
        map_sub, eval_adjointCoordinate, adjoint_eq_inverse x hx, MvPolynomial.eval_X]
      rfl
    have hz := hdense p (fun k hk => by
      rw [hp k (hK k hk), map_inv, hreal k hk, sub_self]) g hg
    exact sub_eq_zero.mp ((hp g hJ).symm.trans hz)
  simpa only [map_inv, _root_.inv_inj] using hginv

/-- Comparing the two positive forms gives a matrix in the normalizer whose
conjugation transports preservation of the second form to the first. -/
private theorem exists_normalizer_conjugating_forms (A : Subgroup (GL n ℂ))
    (hA : IsPolynomiallyDefined A) {J₁ J₂ : GL n ℂ}
    (h₁ : J₁.val.PosDef) (h₂ : J₂.val.PosDef)
    (hA₁ : IsFormSelfAdjoint A J₁) (hA₂ : IsFormSelfAdjoint A J₂) :
    ∃ c ∈ Subgroup.normalizer (A : Set (GL n ℂ)),
      ∀ g : GL n ℂ, star g * J₂ * g = J₂ →
        star (c * g * c⁻¹) * J₁ * (c * g * c⁻¹) = J₁ := by
  obtain ⟨X, hX, hmean, hAX⟩ := exists_mean A hA h₁ h₂ hA₁ hA₂
  let c := J₁⁻¹ * X
  have hc : star c * J₁ * c = J₂ := by
    dsimp [c]
    rw [star_mul, star_inv, star_eq_self_of_posDef h₁, star_eq_self_of_posDef hX]
    calc
      X * J₁⁻¹ * J₁ * (J₁⁻¹ * X) = X * J₁⁻¹ * X := by group
      _ = J₂ := hmean
  refine ⟨c, inv_mul_mem_normalizer h₁ hX hA₁ hAX, fun g hg => ?_⟩
  simp only [star_mul, star_inv]
  calc
    (star c)⁻¹ * (star g * star c) * J₁ * (c * g * c⁻¹) =
        (star c)⁻¹ * (star g * (star c * J₁ * c) * g) * c⁻¹ := by group
    _ = J₁ := by rw [hc, hg, ← hc]; group

private abbrev fixedByRealAutomorphisms (g : GL n ℂ) : Prop :=
  MatrixFixedByBaseAutomorphisms (k := ℝ) g

private theorem fixedByRealAutomorphisms_of_conjGL_eq {g : GL n ℂ}
    (hreal : conjGL g = g) : fixedByRealAutomorphisms g := by
  intro σ
  apply Units.ext
  ext i j
  change σ (g i j) = g i j
  have hentry : star (g i j) = g i j := congrArg (fun z : GL n ℂ => z i j) hreal
  have hre : algebraMap ℝ ℂ (g i j).re = g i j := Complex.conj_eq_iff_re.mp hentry
  calc
    σ (g i j) = σ (algebraMap ℝ ℂ (g i j).re) := congrArg σ hre.symm
    _ = algebraMap ℝ ℂ (g i j).re := σ.commutes _
    _ = g i j := hre

/-- Two compact subgroups that detect polynomial vanishing on `A` admit a
comparison by a normalizing matrix. If the first consists of real matrices,
the comparison sends the second to matrices fixed by real automorphisms. -/
private theorem exists_normalizer_conjugating_to_real (A K₁ K₂ : Subgroup (GL n ℂ))
    (hA : IsPolynomiallyDefined A) (hK₁ : K₁ ≤ A) (hK₂ : K₂ ≤ A)
    (hc₁ : IsCompact (K₁ : Set (GL n ℂ))) (hc₂ : IsCompact (K₂ : Set (GL n ℂ)))
    (hd₁ : ∀ p : MvPolynomial (Coordinate n) ℂ,
      (∀ k ∈ K₁, MvPolynomial.eval (values k) p = 0) →
        ∀ g ∈ A, MvPolynomial.eval (values g) p = 0)
    (hd₂ : ∀ p : MvPolynomial (Coordinate n) ℂ,
      (∀ k ∈ K₂, MvPolynomial.eval (values k) p = 0) →
        ∀ g ∈ A, MvPolynomial.eval (values g) p = 0)
    (hr : ∀ k ∈ K₁, conjGL k = k) :
    ∃ c ∈ Subgroup.normalizer (A : Set (GL n ℂ)),
      ∀ k ∈ K₂, fixedByRealAutomorphisms (c * k * c⁻¹) := by
  obtain ⟨J₁, hJ₁, hp₁, ha₁⟩ := exists_posDef_formAdjoint_of_dense A K₁ hA hK₁ hc₁ hd₁
  obtain ⟨J₂, hJ₂, hp₂, ha₂⟩ := exists_posDef_formAdjoint_of_dense A K₂ hA hK₂ hc₂ hd₂
  obtain ⟨c, hc, hconj⟩ := exists_normalizer_conjugating_forms A hA hJ₁ hJ₂ ha₁ ha₂
  refine ⟨c, hc, fun k hk => fixedByRealAutomorphisms_of_conjGL_eq ?_⟩
  have hg := (Subgroup.mem_normalizer_iff.mp hc k).mp (hK₂ hk)
  exact conjGL_eq_of_preserves_form A K₁ hd₁ J₁ hp₁ hr hg (hconj k (hp₂ k hk))

end Matrix

section RationalPoints

variable {G H : RealGroup} {N : ℕ}

private abbrev extendedMatrix (ρ : MatrixRepresentation (baseChanged ℝ ℂ G) (Fin N))
    (f : baseChanged ℝ ℂ H ⟶ baseChanged ℝ ℂ G) :
    rationalPoints H →* GL (Fin N) ℂ :=
  extendedRationalMatrix (k := ℝ) (L := ℂ) (G := G) (H := H) ρ f

private theorem extendedMatrix_apply (ρ : MatrixRepresentation (baseChanged ℝ ℂ G) (Fin N))
    (f : baseChanged ℝ ℂ H ⟶ baseChanged ℝ ℂ G) (x : rationalPoints H) :
    extendedMatrix ρ f x = (ρ.restrict f).rationalMatrix (rationalExtend ℝ ℂ H x) := by
  rw [MatrixRepresentation.rationalMatrix_restrict]
  rfl

private theorem extendedMatrix_id_apply (ρ : MatrixRepresentation (baseChanged ℝ ℂ G) (Fin N))
    (x : rationalPoints G) :
    extendedMatrix ρ (𝟙 _) x = ρ.rationalMatrix (rationalExtend ℝ ℂ G x) := by
  rw [extendedMatrix_apply, MatrixRepresentation.rationalMatrix_restrict, Grp.id_hom_hom,
    Category.comp_id]

private theorem isReduced_complexification (hG : IsConnectedReductive G) :
    IsReduced (baseChanged ℝ ℂ G).X.left := by
  have hGC := connectedReductiveFieldExtensionStatement ℝ ℂ G hG
  let : Smooth (baseChanged ℝ ℂ G).X.hom := hGC.smooth
  exact Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    ℂ _ (baseChanged ℝ ℂ G).X.hom

/-- The complex isomorphism transports polynomial density of the extended
real points to the range of the ambient representation. -/
private theorem eval_rationalMatrix_eq_zero_of_extended_iso
    [IsAffine (baseChanged ℝ ℂ H).X.left] (hH : IsConnectedReductive H)
    (ρ : MatrixRepresentation (baseChanged ℝ ℂ G) (Fin N))
    (e : baseChanged ℝ ℂ H ≅ baseChanged ℝ ℂ G) (p : MvPolynomial (Coordinate (Fin N)) ℂ)
    (hp : ∀ k ∈ (extendedMatrix ρ e.hom).range, MvPolynomial.eval (values k) p = 0) :
    ∀ g ∈ ρ.rationalMatrix.range, MvPolynomial.eval (values g) p = 0 := by
  have hp' (x : rationalPoints H) :
      MvPolynomial.eval (values ((ρ.restrict e.hom).rationalMatrix
        (rationalExtend ℝ ℂ H x))) p = 0 := by
    rw [← extendedMatrix_apply]
    exact hp _ ((MonoidHom.mem_range (f := extendedMatrix ρ e.hom)).2 ⟨x, rfl⟩)
  rintro _ ⟨z, rfl⟩
  let : IsReduced (baseChanged ℝ ℂ H).X.left := isReduced_complexification hH
  have hd := dense_iUnion_range_rationalExtend ℝ ℂ H (reductiveRationalPointDensity ℝ H hH)
  have hz := eval_eq_zero_of_dense (ρ.restrict e.hom) (rationalExtend ℝ ℂ H) hd
    p hp' (rationalPoints.map e.inv z)
  rw [MatrixRepresentation.rationalMatrix_restrict, rationalPoints.map_apply, Category.assoc,
    ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] at hz
  exact hz

/-- The canonical homeomorphism transfers compactness to identity-test points. -/
private theorem isCompact_univ_rationalPoints (G : RealGroup) [IsAffine G.X.left]
    (hG : HasCompactRealPoints G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology ℝ G.X
    IsCompact (Set.univ : Set (rationalPoints G)) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology ℝ G.X
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    G.affinePointsTopologicalSpace _
  let e := rationalPointsAffineHomeomorph G
  change IsCompact (Set.univ : Set (G.affinePoints (CommAlgCat.of ℝ ℝ))) at hG
  rw [← Set.image_univ_of_surjective e.symm.surjective]
  exact hG.image e.symm.continuous

private theorem isCompact_range_extended_matrix [IsAffine G.X.left]
    [IsAffine (baseChanged ℝ ℂ G).X.left] [IsAffine (baseChanged ℝ ℂ H).X.left]
    (f : baseChanged ℝ ℂ G ⟶ baseChanged ℝ ℂ H)
    (ρ : MatrixRepresentation (baseChanged ℝ ℂ H) (Fin N))
    (hρ : IsClosedSubgroup ρ) (hG : HasCompactRealPoints G) :
    IsCompact ((extendedMatrix ρ f).range : Set (GL (Fin N) ℂ)) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology ℝ G.X
  let : TopologicalSpace (rationalPoints (baseChanged ℝ ℂ G)) :=
    rationalPointTopology ℂ (baseChanged ℝ ℂ G).X
  let : TopologicalSpace (rationalPoints (baseChanged ℝ ℂ H)) :=
    rationalPointTopology ℂ (baseChanged ℝ ℂ H).X
  have hm := (ρ.isClosedEmbedding_rationalMatrix hρ).continuous
  have hf : Continuous (rationalPoints.map f) := continuous_rationalPointMap ℂ f.hom.hom
  have he := continuous_rationalExtend ℝ ℂ G Complex.continuous_ofReal
  rw [extendedMatrix, extendedRationalMatrix, MonoidHom.coe_range, ← Set.image_univ]
  exact (isCompact_univ_rationalPoints G hG).image (hm.comp (hf.comp he))

private theorem extendedMatrix_range_le (ρ : MatrixRepresentation (baseChanged ℝ ℂ G) (Fin N))
    (f : baseChanged ℝ ℂ H ⟶ baseChanged ℝ ℂ G) :
    (extendedMatrix ρ f).range ≤ ρ.rationalMatrix.range := by
  rintro _ ⟨x, rfl⟩
  exact (MonoidHom.mem_range (f := ρ.rationalMatrix)).2
    ⟨rationalPoints.map f (rationalExtend ℝ ℂ H x), rfl⟩

private theorem rationalMatrix_range_isPolynomiallyDefined
    (ρ : MatrixRepresentation (baseChanged ℝ ℂ G) (Fin N)) (hρ : IsClosedSubgroup ρ) :
    IsPolynomiallyDefined ρ.rationalMatrix.range := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  have heq : ρ.rationalMatrix.range = (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range := by
    apply Subgroup.ext
    intro a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨rationalCoeffEquiv ℂ _ x, (rationalMatrix_eq_coeffMatrix ρ x).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(rationalCoeffEquiv ℂ _).symm y, ?_⟩
      rw [rationalMatrix_eq_coeffMatrix, MulEquiv.apply_symm_apply]
  rw [heq]
  exact ρ.affineMatrix_range_isPolynomiallyDefined ℂ

private theorem conjGL_rationalMatrix_extended
    (ρ : MatrixRepresentation G (Fin N)) (x : rationalPoints G) :
    conjGL ((ρ.baseChange (baseMap ℝ ℂ)).rationalMatrix (rationalExtend ℝ ℂ G x)) =
      (ρ.baseChange (baseMap ℝ ℂ)).rationalMatrix (rationalExtend ℝ ℂ G x) := by
  rw [rationalMatrix_baseChange_extend]
  apply Units.ext
  ext i j
  change star (algebraMap ℝ ℂ (ρ.rationalMatrix x i j)) =
    algebraMap ℝ ℂ (ρ.rationalMatrix x i j)
  exact Complex.conj_ofReal _

set_option maxHeartbeats 1200000 in
private theorem exists_normalizing_real_conjugator
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hcG : HasCompactRealPoints G) (hcH : HasCompactRealPoints H)
    (e : baseChanged ℝ ℂ H ≅ baseChanged ℝ ℂ G)
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ) :
    HasConjugatorToGaloisFixedPoints (k := ℝ) (L := ℂ) (G := G) (H := H) (n := Fin N)
      (ρ.baseChange (baseMap ℝ ℂ)) e.hom := by
  let ρC := ρ.baseChange (baseMap ℝ ℂ)
  have hρC : IsClosedSubgroup ρC := ρ.isClosedSubgroup_baseChange _ hρ
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffineHom (baseChanged ℝ ℂ G).X.hom :=
    (connectedReductiveFieldExtensionStatement ℝ ℂ G hG).isAffineHom
  let : IsAffineHom (baseChanged ℝ ℂ H).X.hom :=
    (connectedReductiveFieldExtensionStatement ℝ ℂ H hH).isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffine (baseChanged ℝ ℂ G).X.left :=
    isAffine_of_isAffineHom (baseChanged ℝ ℂ G).X.hom
  let : IsAffine (baseChanged ℝ ℂ H).X.left :=
    isAffine_of_isAffineHom (baseChanged ℝ ℂ H).X.hom
  let reflG := Iso.refl (baseChanged ℝ ℂ G)
  let mG := extendedMatrix ρC reflG.hom
  let mH := extendedMatrix ρC e.hom
  have hreal : ∀ k ∈ mG.range, conjGL k = k := by
    rintro _ ⟨x, rfl⟩
    change conjGL (extendedMatrix ρC (𝟙 _) x) = extendedMatrix ρC (𝟙 _) x
    rw [extendedMatrix_id_apply]
    exact conjGL_rationalMatrix_extended ρ x
  obtain ⟨c, hc, hconj⟩ := exists_normalizer_conjugating_to_real
    ρC.rationalMatrix.range mG.range mH.range (rationalMatrix_range_isPolynomiallyDefined ρC hρC)
    (extendedMatrix_range_le ρC reflG.hom) (extendedMatrix_range_le ρC e.hom)
    (isCompact_range_extended_matrix reflG.hom ρC hρC hcG)
    (isCompact_range_extended_matrix e.hom ρC hρC hcH)
    (eval_rationalMatrix_eq_zero_of_extended_iso hG ρC reflG)
    (eval_rationalMatrix_eq_zero_of_extended_iso hH ρC e)
    hreal
  refine ⟨c, hc, ?_⟩
  intro x
  exact hconj (mH x) ((MonoidHom.mem_range (f := mH)).2 ⟨x, rfl⟩)

/-- A closed real representation of `G` admits a complex matrix normalizing its
complex point group and conjugating the transported real points of `H` into
matrices fixed by all real automorphisms of `ℂ`. -/
theorem exists_closed_representation_with_real_conjugator
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hcG : HasCompactRealPoints G) (hcH : HasCompactRealPoints H)
    (e : baseChanged ℝ ℂ H ≅ baseChanged ℝ ℂ G) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ ∧
      HasConjugatorToGaloisFixedPoints (k := ℝ) (L := ℂ) (G := G) (H := H) (n := Fin N)
        (ρ.baseChange (baseMap ℝ ℂ)) e.hom := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement ℝ G hG.isAffineHom inferInstance
  exact ⟨N, ρ, hρ, exists_normalizing_real_conjugator hG hH hcG hcH e ρ hρ⟩

end RationalPoints

end RealCompactFormUniqueness
end Langlands.GroupScheme
