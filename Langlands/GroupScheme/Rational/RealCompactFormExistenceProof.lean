import Langlands.AlgebraicGeometry.PointTopology.AffineMapProofs
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.GroupScheme.AffinePointTopologicalGroup
import Langlands.GroupScheme.AffinePolarCompact
import Langlands.GroupScheme.Descent.AffineEffectivityProof
import Langlands.GroupScheme.Descent.SemilinearSolution
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.IntegralModel.SemilinearPoints
import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.GroupScheme.Rational.RealCompactFormExistenceStatement
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality
import Langlands.GroupScheme.Reductive.PinnedGaloisDatum
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Compact real forms of complex semisimple group schemes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Classical Matrix
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Descent
open GaloisPointComparison (baseChanged rationalCoeffEquiv rationalCoeffEquiv_left
  rationalCoeffEquiv_map)

local notation "C" => CommRingCat.of ℂ
local notation "Sℂ" => Spec C
local notation "Sℝ" => Spec (CommRingCat.of ℝ)
local notation "Gal" => (ℂ ≃ₐ[ℝ] ℂ)
local notation "b" => galoisBaseMap ℝ ℂ

local instance : IsGalois ℝ ℂ where
  to_isSeparable := inferInstance
  to_normal := normal_iff.mpr fun x =>
    ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

private theorem eq_one_or_conj (σ : Gal) : σ = 1 ∨ σ = Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · exact Or.inl (AlgEquiv.ext fun z => congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h)
  · exact Or.inr (AlgEquiv.ext fun z => congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h)

private theorem conj_ne_one : (Complex.conjAe : Gal) ≠ 1 := by
  intro h
  have hi := congrArg (fun f : Gal => (f Complex.I).im) h
  change -(1 : ℝ) = 1 at hi
  linarith

private theorem conj_mul_conj : Complex.conjAe * Complex.conjAe = (1 : Gal) := by
  ext z
  change star (star z) = z
  exact star_star z

local instance galoisBaseMap_isIso (σ : Gal) : IsIso (b σ) :=
  isIso_SpecMap_iff.mpr σ.bijective

private theorem rationalMap_comp {R : CommRingCat} {G H K : GroupScheme (Spec R)}
    (f : G ⟶ H) (g : H ⟶ K) (x : rationalPoints G) :
    rationalPoints.map (f ≫ g) x = rationalPoints.map g (rationalPoints.map f x) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

private theorem rationalMap_baseChangeSection {R : CommRingCat}
    {G H : GroupScheme (Spec R)} (a : Spec R ⟶ Spec R) (f : G ⟶ H) (x : rationalPoints G) :
    rationalPoints.map ((baseChange a).map f) (baseChangeSectionHom a G x) =
      baseChangeSectionHom a H (rationalPoints.map f x) :=
  (baseChangeSectionHom_naturality a f x).symm

private def matrixAction {d : ℕ} (σ : Gal) (g : GL (Fin d) ℂ) : GL (Fin d) ℂ :=
  if σ = 1 then g else (star g)⁻¹

private theorem matrixAction_mul {d : ℕ} (σ τ : Gal) (g : GL (Fin d) ℂ) :
    matrixAction (σ * τ) g = matrixAction σ (matrixAction τ g) := by
  rcases eq_one_or_conj σ with rfl | rfl
  · simp [matrixAction]
  rcases eq_one_or_conj τ with rfl | rfl
  · simp [matrixAction]
  simp [matrixAction, conj_ne_one, conj_mul_conj, star_inv]

private theorem matrixAction_involutive {d : ℕ} (σ : Gal) :
    Function.Involutive (matrixAction (d := d) σ) := by
  intro g
  rw [← matrixAction_mul]
  rcases eq_one_or_conj σ with rfl | rfl
  · simp [matrixAction]
  · simp [matrixAction, conj_mul_conj]

private abbrev GLComplex (d : ℕ) := GeneralLinear.groupScheme (Fin d) C

private abbrev standardMatrix (d : ℕ) := (MatrixRepresentation.standard (Fin d) C).rationalMatrix

private def matrixTwist (d : ℕ) (σ : Gal) : (baseChange (b σ)).obj (GLComplex d) ≅ GLComplex d :=
  GeneralLinear.baseChangeIso (Fin d) (b σ) ≪≫
    if σ = 1 then Iso.refl _ else GeneralLinear.contragredientIso (Fin d) C

private theorem standardMatrix_baseChange (d : ℕ) (σ : Gal) (x : rationalPoints (GLComplex d)) :
    standardMatrix d (rationalPoints.map (GeneralLinear.baseChangeIso (Fin d) (b σ)).hom
        (baseChangeSectionHom (b σ) (GLComplex d) x)) =
      Matrix.GeneralLinearGroup.map σ.toRingHom (standardMatrix d x) := by
  apply Units.ext
  ext i j
  let y := baseChangeSectionHom (b σ) (GLComplex d) x
  have hy : (baseChangePointsEquiv (b σ) (GLComplex d) (Over.mk (𝟙 Sℂ)) y).left =
      b σ ≫ x.left := by
    rw [baseChangePointsEquiv_left, baseChangeSectionHom_fst]
  change (Scheme.ΓSpecIso C).hom (GeneralLinear.pointsEquiv (Fin d) C _
    (y ≫ (GeneralLinear.baseChangeIso (Fin d) (b σ)).hom.hom.hom) i j) = _
  rw [GeneralLinear.pointsEquiv_comp_baseChangeIso_hom,
    GeneralLinear.pointsEquiv_apply_apply, hy, Scheme.Hom.comp_appTop]
  change (((b σ).appTop ≫ (Scheme.ΓSpecIso C).hom).hom) _ = _
  unfold galoisBaseMap
  rw [Scheme.ΓSpecIso_naturality]
  change σ ((Scheme.ΓSpecIso C).hom (x.left.appTop _)) =
    σ ((Scheme.ΓSpecIso C).hom (GeneralLinear.pointsEquiv (Fin d) C _ x i j))
  rw [GeneralLinear.pointsEquiv_apply_apply]

private theorem standardMatrix_contragredient (d : ℕ) (x : rationalPoints (GLComplex d)) :
    standardMatrix d (rationalPoints.map (GeneralLinear.contragredientIso (Fin d) C).hom x) =
      GeneralLinear.matrixContragredient (Fin d) ℂ (standardMatrix d x) := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso C).hom.hom
    (GeneralLinear.pointsEquiv (Fin d) C _ (x ≫ (GeneralLinear.contragredientIso (Fin d) C).hom.hom.hom)) = _
  rw [GeneralLinear.pointsEquiv_contragredientIso]
  apply Units.ext
  rfl

private theorem standardMatrix_twist (d : ℕ) (σ : Gal) (x : rationalPoints (GLComplex d)) :
    standardMatrix d (rationalPoints.map (matrixTwist d σ).hom
        (baseChangeSectionHom (b σ) (GLComplex d) x)) = matrixAction σ (standardMatrix d x) := by
  rcases eq_one_or_conj σ with rfl | rfl
  · simp only [matrixTwist, matrixAction, eq_self, ite_true, Iso.trans_refl]
    rw [standardMatrix_baseChange]
    rfl
  · simp only [matrixTwist, matrixAction, ite_eq_right conj_ne_one, Iso.trans_hom]
    rw [rationalMap_comp, standardMatrix_contragredient, standardMatrix_baseChange]
    apply Units.ext
    rfl

private theorem standardMatrix_map {G : GroupScheme Sℂ} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (x : rationalPoints G) :
    standardMatrix d (rationalPoints.map ρ x) = ρ.rationalMatrix x := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso C).hom.hom
    (GeneralLinear.pointsEquiv (Fin d) C _ ((x ≫ ρ.hom.hom) ≫ 𝟙 _)) = _
  rw [Category.comp_id]
  rfl

private theorem rationalMatrix_eq_coeffMatrix {G : GroupScheme Sℂ} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (x : rationalPoints G) :
    ρ.rationalMatrix x = ρ.affineMatrix (CommAlgCat.of ℂ ℂ) (rationalCoeffEquiv ℂ G x) := by
  rw [ρ.rationalMatrix_eq_affineMatrix]
  congr 1

private theorem exists_matrixAction_eq {G : GroupScheme Sℂ} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d))
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range)
    (σ : Gal) (x : rationalPoints G) :
    ∃ y : rationalPoints G, ρ.rationalMatrix y = matrixAction σ (ρ.rationalMatrix x) := by
  rcases eq_one_or_conj σ with rfl | rfl
  · exact ⟨x, by simp [matrixAction]⟩
  · have hx : ρ.rationalMatrix x ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range :=
      ⟨rationalCoeffEquiv ℂ G x, (rationalMatrix_eq_coeffMatrix ρ x).symm⟩
    obtain ⟨y, hy⟩ := hstar _ hx
    refine ⟨((rationalCoeffEquiv ℂ G).symm y)⁻¹, ?_⟩
    rw [map_inv, rationalMatrix_eq_coeffMatrix, MulEquiv.apply_symm_apply, hy,
      matrixAction, ite_eq_right conj_ne_one]

private abbrev twist (σ : Gal) (G : GroupScheme Sℂ) := (baseChange (b σ)).obj G

private def twistedRepresentation {G : GroupScheme Sℂ} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (σ : Gal) :
    MatrixRepresentation (twist σ G) (Fin d) :=
  (baseChange (b σ)).map ρ ≫ (matrixTwist d σ).hom

private theorem twistedRepresentation_matrix {G : GroupScheme Sℂ} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (σ : Gal) (x : rationalPoints G) :
    (twistedRepresentation ρ σ).rationalMatrix (baseChangeSectionHom (b σ) G x) =
      matrixAction σ (ρ.rationalMatrix x) := by
  rw [← standardMatrix_map, twistedRepresentation, rationalMap_comp,
    rationalMap_baseChangeSection, standardMatrix_twist, standardMatrix_map]

private theorem smooth_twist (G : GroupScheme Sℂ) [Smooth G.X.hom] (σ : Gal) :
    Smooth (twist σ G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom (b σ)))

private theorem reduced_of_smooth (G : GroupScheme Sℂ) [Smooth G.X.hom] :
    IsReduced G.X.left :=
  Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field ℂ _ G.X.hom

private theorem closed_twistedRepresentation {G : GroupScheme Sℂ} {d : ℕ}
    {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ) (σ : Gal) :
    IsClosedSubgroup (twistedRepresentation ρ σ) :=
  (hρ.baseChange (b σ)).comp_iso (matrixTwist d σ)

private theorem range_twistedRepresentation {G : GroupScheme Sℂ} [Smooth G.X.hom] {d : ℕ}
    {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range) (σ : Gal) :
    SubgroupFunctor.range (twistedRepresentation ρ σ) = SubgroupFunctor.range ρ := by
  have := smooth_twist G σ
  have := reduced_of_smooth G
  have := reduced_of_smooth (twist σ G)
  have : Mono (MatrixRepresentation.standard (Fin d) C).hom.hom := by
    rw [MatrixRepresentation.standard, Grp.id_hom_hom]
    infer_instance
  have hinj := (MatrixRepresentation.standard (Fin d) C).rationalMatrix_injective
  apply le_antisymm
  · apply SubgroupFunctor.range_le_of_dense_rationalPoints
      (hasDenseRationalPoints_of_smooth_of_isSepClosed ℂ (twist σ G).X) hρ
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := baseChangeSectionHom_surjective (b σ) G y
    obtain ⟨z, hz⟩ := exists_matrixAction_eq ρ hstar σ x
    refine ⟨z, hinj ?_⟩
    change standardMatrix d (rationalPoints.map ρ z) =
      standardMatrix d (rationalPoints.map (twistedRepresentation ρ σ)
        (baseChangeSectionHom (b σ) G x))
    rw [standardMatrix_map, standardMatrix_map, twistedRepresentation_matrix, hz]
  · apply SubgroupFunctor.range_le_of_dense_rationalPoints
      (hasDenseRationalPoints_of_smooth_of_isSepClosed ℂ G.X) (closed_twistedRepresentation hρ σ)
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := exists_matrixAction_eq ρ hstar σ x
    refine ⟨baseChangeSectionHom (b σ) G z, hinj ?_⟩
    change standardMatrix d (rationalPoints.map (twistedRepresentation ρ σ)
      (baseChangeSectionHom (b σ) G z)) = standardMatrix d (rationalPoints.map ρ x)
    rw [standardMatrix_map, standardMatrix_map, twistedRepresentation_matrix, hz,
      matrixAction_involutive σ]

private def compactTwist {G : GroupScheme Sℂ} [Smooth G.X.hom] {d : ℕ}
    {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range) (σ : Gal) : twist σ G ≅ G :=
  (closed_twistedRepresentation hρ σ).sourceIsoOfRangeEq hρ (range_twistedRepresentation hρ hstar σ)

private theorem compactTwist_matrix {G : GroupScheme Sℂ} [Smooth G.X.hom] {d : ℕ}
    {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range)
    (σ : Gal) (x : rationalPoints G) :
    ρ.rationalMatrix (rationalPoints.map (compactTwist hρ hstar σ).hom
      (baseChangeSectionHom (b σ) G x)) = matrixAction σ (ρ.rationalMatrix x) := by
  have h : (compactTwist hρ hstar σ).hom ≫ ρ = twistedRepresentation ρ σ :=
    IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ (range_twistedRepresentation hρ hstar σ)
  rw [← standardMatrix_map, ← rationalMap_comp, h, standardMatrix_map,
    twistedRepresentation_matrix]

private theorem pullbackComparison_section {R : CommRingCat} (G : GroupScheme (Spec R))
    {a c d : Spec R ⟶ Spec R} (h : a ≫ c = d) (x : rationalPoints G) :
    rationalPoints.map (pullbackComparison c a d h G).hom
        (baseChangeSectionHom a ((baseChange c).obj G) (baseChangeSectionHom c G x)) =
      baseChangeSectionHom d G x := by
  apply (baseChangeBasePointsEquiv d G).injective
  apply Over.OverMorphism.ext
  simp only [baseChangeBasePointsEquiv_left, rationalPoints.map_apply, Over.comp_left,
    Category.assoc, pullbackComparison_hom_fst]
  rw [section_tower_fst, baseChangeSectionHom_fst, h]

private def sectionAction {R : CommRingCat} {G : GroupScheme (Spec R)}
    {a : Spec R ⟶ Spec R} (e : (baseChange a).obj G ⟶ G) (x : rationalPoints G) :
    rationalPoints G :=
  rationalPoints.map e (baseChangeSectionHom a G x)

private theorem semilinear_cocycle_of_sections {k : Type} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {a c d : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)}
    [IsIso a] [IsIso c] [IsSeparated G.X.hom]
    [IsReduced ((baseChange a).obj ((baseChange c).obj G)).X.left]
    (h : a ≫ c = d)
    (hDense : HasDenseRationalPoints k ((baseChange a).obj ((baseChange c).obj G)).X)
    (ea : (baseChange a).obj G ≅ G) (ec : (baseChange c).obj G ≅ G)
    (ed : (baseChange d).obj G ≅ G)
    (hAction : ∀ x, sectionAction ed.hom x = sectionAction ea.hom (sectionAction ec.hom x)) :
    pullbackComparison c a d h G ≪≫ ed = (baseChange a).mapIso ec ≪≫ ea := by
  apply Iso.ext
  apply Grp.hom_ext
  refine hom_ext_of_denseRationalPoints hDense ?_
  intro p
  obtain ⟨y, rfl⟩ := baseChangeSectionHom_surjective a ((baseChange c).obj G) p
  obtain ⟨x, rfl⟩ := baseChangeSectionHom_surjective c G y
  change rationalPoints.map ((pullbackComparison c a d h G).hom ≫ ed.hom) _ =
    rationalPoints.map (((baseChange a).mapIso ec).hom ≫ ea.hom) _
  rw [rationalMap_comp, rationalMap_comp, pullbackComparison_section, Functor.mapIso_hom,
    rationalMap_baseChangeSection]
  exact hAction x

private theorem compactTwist_comp {G : GroupScheme Sℂ} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {d : ℕ} {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range)
    (σ τ υ : Gal) (hm : σ * τ = υ) (h : b σ ≫ b τ = b υ) :
    pullbackComparison (b τ) (b σ) (b υ) h G ≪≫ compactTwist hρ hstar υ =
      (baseChange (b σ)).mapIso (compactTwist hρ hstar τ) ≪≫ compactTwist hρ hstar σ := by
  have := smooth_twist G τ
  have := smooth_twist (twist τ G) σ
  have := reduced_of_smooth (twist σ (twist τ G))
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  refine semilinear_cocycle_of_sections h
    (hasDenseRationalPoints_of_smooth_of_isSepClosed ℂ (twist σ (twist τ G)).X)
    (compactTwist hρ hstar σ) (compactTwist hρ hstar τ) (compactTwist hρ hstar υ) ?_
  intro x
  apply ρ.rationalMatrix_injective
  unfold sectionAction
  rw [compactTwist_matrix, compactTwist_matrix, compactTwist_matrix, ← hm, matrixAction_mul]

private def compactDatum {G : GroupScheme Sℂ} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {d : ℕ} {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range) :
    Datum (fieldMap ℝ ℂ) G :=
  SemilinearComponents.datumOfSemilinear (fieldMap ℝ ℂ)
    (finiteGaloisComponent ℝ ℂ) (fun i => b (galoisIndexEquiv ℝ ℂ i))
    (finiteGaloisComponent_fst ℝ ℂ) (finiteGaloisComponent_snd ℝ ℂ)
    (finiteGaloisIndexMul ℝ ℂ) (finiteGaloisBaseMap_comp ℝ ℂ) G
    (fun i => compactTwist hρ hstar (galoisIndexEquiv ℝ ℂ i))
    (fun i j => compactTwist_comp hρ hstar _ _ _ (galoisIndexEquiv_mul ℝ ℂ i j).symm
      (finiteGaloisBaseMap_comp ℝ ℂ i j))

private theorem pullIso_compactDatum {G : GroupScheme Sℂ} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {d : ℕ} {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range) (i : Fin (Module.finrank ℝ ℂ)) :
    pullIso (finiteGaloisComponent ℝ ℂ i) (finiteGaloisComponent_fst ℝ ℂ i)
        (finiteGaloisComponent_snd ℝ ℂ i) (compactDatum hρ hstar).overlap =
      semilinearComponent G (compactTwist hρ hstar (galoisIndexEquiv ℝ ℂ i)) :=
  SemilinearComponents.pullIso_datumOfSemilinear _ _ _ _ _ _ _ _ _ _ _

private theorem canonicalSection_fixes_baseChange {K R : CommRingCat}
    (p : Spec R ⟶ Spec K) (a : Spec R ⟶ Spec R) (ha : a ≫ p = p)
    (H : GroupScheme (Spec K)) (x : rationalPoints H) :
    sectionAction (descentBaseChangeIso p a ha H).hom (baseChangeSectionHom p H x) =
      baseChangeSectionHom p H x := by
  unfold sectionAction
  rw [rationalPoints.map_apply]
  apply (baseChangeBasePointsEquiv p H).injective
  apply Over.OverMorphism.ext
  simp only [baseChangeBasePointsEquiv_left, descentBaseChangeIso_section_fst,
    baseChangeSectionHom_fst]
  rw [← Category.assoc, ha]

private theorem fixed_section_of_intertwining {R : CommRingCat}
    {G H : GroupScheme (Spec R)} {a : Spec R ⟶ Spec R}
    (f : H ⟶ G) (eH : (baseChange a).obj H ⟶ H) (eG : (baseChange a).obj G ⟶ G)
    (h : (baseChange a).map f ≫ eG = eH ≫ f)
    (x : rationalPoints H) (hx : sectionAction eH x = x) :
    sectionAction eG (rationalPoints.map f x) = rationalPoints.map f x := by
  have hmap := congrArg (fun g => rationalPoints.map g (baseChangeSectionHom a H x)) h
  change rationalPoints.map eH (baseChangeSectionHom a H x) = x at hx
  rw [rationalMap_comp, rationalMap_comp, rationalMap_baseChangeSection, hx] at hmap
  exact hmap

private theorem solution_fixed_component {G : GroupScheme Sℂ}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {d : ℕ} {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range)
    (s : Solution (compactDatum hρ hstar)) (i : Fin (Module.finrank ℝ ℂ))
    (x : rationalPoints s.obj) :
    sectionAction (compactTwist hρ hstar (galoisIndexEquiv ℝ ℂ i)).hom
        (rationalPoints.map s.iso.hom (baseChangeSectionHom (fieldMap ℝ ℂ) s.obj x)) =
      rationalPoints.map s.iso.hom (baseChangeSectionHom (fieldMap ℝ ℂ) s.obj x) := by
  let τ := galoisIndexEquiv ℝ ℂ i
  let ha := galoisBaseMap_over ℝ ℂ τ
  let e := descentBaseChangeIso (fieldMap ℝ ℂ) (b τ) ha s.obj
  refine fixed_section_of_intertwining (a := b τ) s.iso.hom e.hom
    (compactTwist hρ hstar τ).hom ?_ (baseChangeSectionHom (fieldMap ℝ ℂ) s.obj x) ?_
  · exact s.semilinear (b τ) ha (finiteGaloisComponent ℝ ℂ i)
      (finiteGaloisComponent_fst ℝ ℂ i) (finiteGaloisComponent_snd ℝ ℂ i)
      (compactTwist hρ hstar τ) (pullIso_compactDatum hρ hstar i)
  · exact canonicalSection_fixes_baseChange (fieldMap ℝ ℂ) (b τ) ha s.obj x

private theorem solution_mem_unitary {G : GroupScheme Sℂ} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {d : ℕ} {ρ : MatrixRepresentation G (Fin d)} (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range)
    (s : Solution (compactDatum hρ hstar)) (x : rationalPoints s.obj) :
    rationalCoeffEquiv ℂ G
        (rationalPoints.map s.iso.hom (baseChangeSectionHom (fieldMap ℝ ℂ) s.obj x)) ∈
      ρ.affineUnitarySubgroup (S := ℂ) := by
  let y := rationalPoints.map s.iso.hom (baseChangeSectionHom (fieldMap ℝ ℂ) s.obj x)
  obtain ⟨i, hi⟩ := (galoisIndexEquiv ℝ ℂ).surjective Complex.conjAe
  have hy := solution_fixed_component hρ hstar s i x
  have hm := (compactTwist_matrix hρ hstar (galoisIndexEquiv ℝ ℂ i) y).symm.trans
    (congrArg (fun z : rationalPoints G => ρ.rationalMatrix z) hy)
  rw [hi, matrixAction, ite_eq_right conj_ne_one] at hm
  rw [ρ.mem_affineUnitarySubgroup, Matrix.mem_unitaryGroup_iff, ← rationalMatrix_eq_coeffMatrix]
  exact congrArg Units.val (calc
    ρ.rationalMatrix y * star (ρ.rationalMatrix y) =
        (star (ρ.rationalMatrix y))⁻¹ * star (ρ.rationalMatrix y) :=
      congrArg (fun q => q * star (ρ.rationalMatrix y)) hm.symm
    _ = 1 := inv_mul_cancel _)

private theorem coefficientExtend_baseChange (H : GroupScheme Sℝ)
    (x : H.affinePoints (CommAlgCat.of ℝ ℝ)) :
    affinePointsBaseChangeMulEquiv ℝ ℂ ℂ H (GaloisPoint.extend ℝ ℂ H x) =
      rationalCoeffEquiv ℂ (baseChanged ℝ ℂ H)
        (baseChangeSectionHom (fieldMap ℝ ℂ) H ((rationalCoeffEquiv ℝ H).symm x)) := by
  apply (affinePointsBaseChangeMulEquiv ℝ ℂ ℂ H).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left, rationalCoeffEquiv_left]
  change fieldMap ℝ ℂ ≫ x.left =
    (baseChangeSectionHom (fieldMap ℝ ℂ) H ((rationalCoeffEquiv ℝ H).symm x)).left ≫
      pullback.fst H.X.hom (fieldMap ℝ ℂ)
  rw [baseChangeSectionHom_fst]
  exact congrArg (fun z => fieldMap ℝ ℂ ≫ z)
    ((congrArg (fun z => z.left) ((rationalCoeffEquiv ℝ H).apply_symm_apply x)).symm.trans
      (rationalCoeffEquiv_left ℝ H _))

section Compactness

local instance realPointTopology (H : GroupScheme Sℝ) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of ℝ ℝ)) := H.affinePointsTopologicalSpace _

local instance complexCoefficientPointTopology (H : GroupScheme Sℝ) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of ℝ ℂ)) := H.affinePointsTopologicalSpace _

local instance complexPointTopology (G : GroupScheme Sℂ) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of ℂ ℂ)) := G.affinePointsTopologicalSpace _

private theorem isClosedEmbedding_realExtend (H : GroupScheme Sℝ) [IsAffine H.X.left] :
    IsClosedEmbedding (GaloisPoint.extend ℝ ℂ H) := by
  let f : ℝ →ₐ[ℝ] ℂ := Algebra.ofId ℝ ℂ
  have hf : IsClosedEmbedding f := Complex.isometry_ofReal.isClosedEmbedding
  let eReal := H.affinePointsAlgebraHomeomorph (CommAlgCat.of ℝ ℝ)
  let eComplex := H.affinePointsAlgebraHomeomorph (CommAlgCat.of ℝ ℂ)
  have hmap := AlgPoint.isClosedEmbedding_mapCoefficients
    (A := AffineCoordinateRing ℝ H.X) f hf
  have heq : eComplex.symm ∘ AlgPoint.mapCoefficients f ∘ eReal =
      (GaloisPoint.extend ℝ ℂ H : H.affinePoints (CommAlgCat.of ℝ ℝ) →
        H.affinePoints (CommAlgCat.of ℝ ℂ)) := by
    funext x
    apply eComplex.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    apply AlgPoint.ext
    intro a
    change AlgPoint.mapCoefficients f
        (H.affinePointsAlgebraHomeomorph (CommAlgCat.of ℝ ℝ) x) a =
      H.affinePointsAlgebraHomeomorph (CommAlgCat.of ℝ ℂ)
        (H.affinePointMap (CommAlgCat.ofHom f) x) a
    rw [AlgPoint.mapCoefficients_apply,
      H.affinePointsAlgebraHomeomorph_apply (CommAlgCat.of ℝ ℝ) x a,
      H.affinePointsAlgebraHomeomorph_apply (CommAlgCat.of ℝ ℂ) _ a]
    exact (H.affinePointEvaluation_map (CommAlgCat.ofHom f) x a).symm
  rw [← heq]
  exact eComplex.symm.isClosedEmbedding.comp (hmap.comp eReal.isClosedEmbedding)

private theorem solution_hasCompactRealPoints {G : GroupScheme Sℂ}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {d : ℕ} {ρ : MatrixRepresentation G (Fin d)}
    (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℂ ℂ)).range)
    (s : Solution (compactDatum hρ hstar)) [IsAffine s.obj.X.left] :
    HasCompactRealPoints s.obj := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let e := (affinePointsBaseChangeContinuousMulEquiv ℝ ℂ ℂ s.obj).toHomeomorph.trans
    (affinePointsIsoHomeomorph s.iso (CommAlgCat.of ℂ ℂ))
  have he := e.isClosedEmbedding.comp (isClosedEmbedding_realExtend s.obj)
  have hc := he.isCompact_preimage (ρ.isCompact_affineUnitarySubgroup (S := ℂ) hρ)
  have hpre : (e ∘ GaloisPoint.extend ℝ ℂ s.obj) ⁻¹'
      (ρ.affineUnitarySubgroup (S := ℂ) : Set (G.affinePoints (CommAlgCat.of ℂ ℂ))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change (baseChanged ℝ ℂ s.obj).affinePointsTarget s.iso.hom (CommAlgCat.of ℂ ℂ)
      (affinePointsBaseChangeMulEquiv ℝ ℂ ℂ s.obj (GaloisPoint.extend ℝ ℂ s.obj x)) ∈
        ρ.affineUnitarySubgroup (S := ℂ)
    rw [coefficientExtend_baseChange, ← rationalCoeffEquiv_map]
    exact solution_mem_unitary hρ hstar s ((rationalCoeffEquiv ℝ s.obj).symm x)
  rw [hpre] at hc
  exact hc

/-- Every complex semisimple group scheme has a compact real form. -/
theorem realCompactFormExistence : RealCompactFormExistenceStatement := by
  intro G hG
  have : Smooth G.X.hom := hG.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  obtain ⟨d, ρ, hρ, hstar⟩ :=
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement ℂ G
      hG.isConnectedReductive
  obtain ⟨s, hs⟩ :=
    affineGroupSchemeFiniteGaloisObjectDescent ℝ ℂ G inferInstance (compactDatum hρ hstar)
  have : IsAffineHom s.obj.X.hom := hs
  have : IsAffine s.obj.X.left := isAffine_of_isAffineHom s.obj.X.hom
  exact ⟨s.obj, IsSemisimple.of_fieldExtension (IsSemisimple.of_iso s.iso hG),
    solution_hasCompactRealPoints hρ hstar s, ⟨s.iso⟩⟩

end Compactness

end Langlands.GroupScheme
