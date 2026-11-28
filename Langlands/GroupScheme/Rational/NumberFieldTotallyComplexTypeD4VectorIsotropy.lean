import Langlands.Algebra.DivisionBrauerClass
import Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting
import Langlands.GroupScheme.OrthogonalInnerForm.QuadraticTransport
import Langlands.GroupScheme.OrthogonalMatrix.TypeD4VectorMaximalWeight
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaNormOneChart
import Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryProof
import Langlands.GroupScheme.Quaternionic.SpinCoverScalarComparison
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexScalarSpinIsotropy
import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDAlignedSpinCoverProof
import Langlands.GroupScheme.SimplyConnected.NormOneHomTitsObstruction
import Langlands.GroupScheme.SimplyConnected.TypeD4CentralCharacters

/-! # Isotropy of type D4 with split vector algebra over a totally complex number field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.CentralSimple Langlands.Brauer Quaternionic OrthogonalInnerForm
open OrthogonalMorita CentralSimpleUnits.SplitRepresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 1200
set_option maxHeartbeats 1800000

private theorem dual_reindex {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ : MatrixRepresentation G I) (e : I ≃ J) :
    (ρ.reindex e).dual = ρ.dual.reindex e := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv J R T).injective
  change ((ρ.reindex e).dual).pointMatrix T x = (ρ.dual.reindex e).pointMatrix T x
  rw [MatrixRepresentation.dual_pointMatrix, MatrixRepresentation.reindex_pointMatrix,
    MatrixRepresentation.reindex_pointMatrix, MatrixRepresentation.dual_pointMatrix]
  apply Units.ext
  rw [GeneralLinear.matrixContragredient_coe, ← map_inv,
    MatrixRepresentation.reindexGL_val, MatrixRepresentation.reindexGL_val,
    GeneralLinear.matrixContragredient_coe]
  rfl

private theorem finrank_weightSpace_reindex {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (p : SplitPinning G)
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ : MatrixRepresentation G I) (e : I ≃ J) (χ : characterLattice p.torus) :
    Module.finrank k (p.representationWeightSpace (ρ.reindex e) χ) =
      Module.finrank k (p.representationWeightSpace ρ χ) := by
  let E := MatrixRepresentation.reindexVector (k := k) e
  have h (v : I → k) : E v ∈ p.representationWeightSpace (ρ.reindex e) χ ↔
      v ∈ p.representationWeightSpace ρ χ := by
    rw [p.mem_representationWeightSpace_iff_affine, p.mem_representationWeightSpace_iff_affine]
    refine forall_congr' fun R => forall_congr' fun t => ?_
    rw [MatrixRepresentation.reindex_affineMatrix, MatrixRepresentation.reindexGL_val]
    let M : Matrix I I R := ρ.affineMatrix R (t ≫ p.inclusion.hom.hom)
    let w : I → R := fun i => algebraMap k R (v i)
    let c : R := Lie.characterValue χ t
    change (M.submatrix e.symm e.symm) *ᵥ (w ∘ e.symm) = (c • w) ∘ e.symm ↔ M *ᵥ w = c • w
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
    constructor
    · intro he
      funext i
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      exact congrFun he j
    · intro he
      exact funext fun j => congrFun he (e.symm j)
  have heq : p.representationWeightSpace (ρ.reindex e) χ =
      (p.representationWeightSpace ρ χ).map E.toLinearMap := by
    ext w
    obtain ⟨v, rfl⟩ := E.surjective w
    rw [h]
    exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨v', hv', he⟩ => E.injective he ▸ hv'⟩
  rw [heq, E.finrank_map_eq]

private theorem finrank_division_eq_one_of_classOf_eq_zero
    (k D : Type u) [Field k] [DivisionRing D] [Algebra k D]
    [FiniteDimensional k D] [Algebra.IsCentral k D]
    (h : classOf (divisionAlgebra k D) = 0) : Module.finrank k D = 1 := by
  obtain ⟨r, hr, ⟨e⟩⟩ := (classOf_eq_zero_iff _).mp h
  change D ≃ₐ[k] Matrix (Fin r) (Fin r) k at e
  have hr' : r = 1 := by
    by_contra hne
    let i : Fin r := ⟨0, hr⟩
    let j : Fin r := ⟨1, by omega⟩
    have hij : i ≠ j := by intro hh; have := congrArg Fin.val hh; simp [i, j] at this
    let X : Matrix (Fin r) (Fin r) k := Matrix.single i i 1
    let Y : Matrix (Fin r) (Fin r) k := Matrix.single j j 1
    have hX : X ≠ 0 := by intro h0; have := congrFun (congrFun h0 i) i; simp [X] at this
    have hY : Y ≠ 0 := by intro h0; have := congrFun (congrFun h0 j) j; simp [Y] at this
    have hXY : X * Y = 0 := Matrix.single_mul_single_of_ne (c := (1 : k)) i i j hij (1 : k)
    have hz : e.symm X * e.symm Y = 0 := by rw [← _root_.map_mul, hXY, map_zero]
    rcases mul_eq_zero.mp hz with hx | hy
    · exact hX (e.symm.injective (hx.trans (map_zero e.symm).symm))
    · exact hY (e.symm.injective (hy.trans (map_zero e.symm).symm))
  subst r
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
  simp

private theorem spinCover_isotropic_of_scalar_division
    {F D : Type u} [Field F] [NumberField F] [IsTotallyComplex F]
    [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    (hD : Module.finrank F D = 1) (σ : FirstKindInvolution F D)
    (q : σ.QuadraticForms (Fin 8)) (hq : σ.IsNondegenerateQuadratic q)
    {G : GroupScheme (Spec (CommRingCat.of F))} (π : G ⟶ σ.isometryGroup q)
    (hπ : σ.IsSpinCover q π) : ¬ IsAnisotropic G := by
  let j := Langlands.Algebra.CentralSimple.algEquivOfFinrankEqOne hD
  have hσ (a : D) : σ a = a := by
    obtain ⟨k, rfl⟩ := j.surjective a
    exact σ.map_algebraMap k
  let I := Fin 8
  let τ := FirstKindInvolution.scalar F
  let φ : Matrix I I D ≃ₐ[F] Matrix I I F := j.symm.mapMatrix
  have hm (x : Matrix I I D) : φ (σ.matrix I x) = τ.matrix I (φ x) := by
    ext i k
    change j.symm (σ (x k i)) = τ (j.symm (x k i))
    rw [hσ, FirstKindInvolution.scalar_apply]
  let Q : Matrix I I D := Quotient.out q
  let q' : τ.QuadraticForms I := Submodule.Quotient.mk (φ Q * 1)
  let E : σ.isometryGroup q ≅ τ.isometryGroup q' :=
    isometryCutAlgEquivIso (σ.matrix I) τ φ 1 (τ.matrix I).map_one isUnit_one
      (fun x => by simpa only [mul_one, one_mul] using hm x) Q
  have hq' : τ.IsNondegenerateQuadratic q' := by
    change IsUnit (τ.polar (Submodule.Quotient.mk (φ Q * 1)))
    rw [mul_one, FirstKindInvolution.polar_mk, ← hm, ← _root_.map_add]
    have hQ : IsUnit (σ.polar (Submodule.Quotient.mk Q : σ.QuadraticForms I)) := by
      rw [show (Submodule.Quotient.mk Q : σ.QuadraticForms I) = q from Quotient.out_eq q]
      exact hq
    exact hQ.map φ.toMonoidHom
  obtain ⟨hs, _⟩ := ordinaryOrthogonalGeometry F 4 (by decide) q' hq'
  let : Smooth (τ.isometryGroup q').X.hom := hs
  let : Smooth (σ.isometryGroup q).X.hom := hπ.smooth
  obtain ⟨p, hp, hcomp⟩ := hπ.exists_centralIsogeny
  let E₀ := IdentityComponent.mapIso E
  have hπ' : τ.IsSpinCover q' (π ≫ E.hom) := by
    refine ⟨hπ.isSimplyConnected, hs, p ≫ E₀.hom, hp.comp_iso E₀, ?_⟩
    rw [Category.assoc, IdentityComponent.mapIso_hom_identityComponentι, ← Category.assoc, hcomp]
  exact numberFieldTotallyComplexScalarSpinIsotropy F 8 q' (by decide) hq' G (π ≫ E.hom) hπ'

/-- A simply connected absolutely almost-simple D4 group with the nonfork
vertices fixed and trivial vector Tits obstruction is isotropic over a
totally complex number field. -/
def NumberFieldTotallyComplexTypeD4VectorIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4) (hsc : IsSimplyConnected G),
    IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) →
    (∀ (g : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
      (e a).val + 2 < 4 → d.star g a = a) →
    ∀ w : d.pinning.starFixedWeights,
      w.val = d.absoluteFundamentalCharacter hsc (e.symm 0) →
      d.pinning.titsObstruction hsc w = 0 → ¬ IsAnisotropic G

set_option synthInstance.maxHeartbeats 120000 in
theorem numberFieldTotallyComplexTypeD4VectorIsotropy :
    NumberFieldTotallyComplexTypeD4VectorIsotropyStatement.{u} := by
  classical
  intro F _ _ _ G _ _ d e hsc habs hcart hstar w hw hobs
  obtain ⟨D, _, _, _, _, degree, m, hdegree, hD, hm, σ, hσ, q, hq, π, hπ, halign⟩ :=
    classicalTypeDAlignedSpinCover F G d 4 e (by decide) hsc habs hcart hstar
  let : NeZero m := ⟨by
    intro h
    rw [h, zero_mul] at hm
    omega⟩
  let L := SeparableClosure F
  let G_L := (GroupScheme.baseChange (algebraBaseMap F L)).obj G
  let : IsAffineHom G_L.X.hom := by change IsAffineHom (Limits.pullback.snd _ _); infer_instance
  let p := d.pinning.toSplitPinning
  obtain ⟨r, _, ⟨eD⟩⟩ := exists_matrix_chart F D L
  have hr : r = degree := by
    have h := finrank_eq_matrix_size F D L r eD
    rw [hD, pow_two] at h
    exact Nat.mul_self_inj.mp h.symm
  subst r
  have hpolar := isUnit_splitGram_polar eD σ (by simpa using hσ)
    q (Quotient.out q) (Quotient.out_eq q) hq
  have hcard : Fintype.card (Fin m × Fin degree) = 2 * 4 := by simpa using hm
  obtain ⟨P, P', hPP', hP'P, hPQ⟩ := OrthogonalMatrix.exists_hyperbolic_matrix
    hcard (DegreeSplitting.splitGram eD σ (Quotient.out q)) hpolar
  let M := comparisonOfSplitting eD σ hσ q P P' hPP' hP'P hPQ
  let S := OrthogonalMatrix.groupScheme (Fin 4) (CommRingCat.of L)
  let : Smooth S.X.hom := OrthogonalMatrix.smooth_groupScheme (Fin 4) (CommRingCat.of L)
  let : IsAffineHom S.X.hom := OrthogonalMatrix.isAffineHom_groupScheme (Fin 4) (CommRingCat.of L)
  let π_L := splitCover M hπ
  have hAlign (v : d.Vertex) (hv : (e v).val = 0) : p.FundamentalWeightTrivialOnKernel v π_L := by
    intro χ hχ hχ'
    have h := ((d.fundamentalWeightTrivialOnKernel_iff v π).mp (halign v hv)) χ hχ hχ'
    let : IsIso M.groupIso.hom.hom.hom := (Grp.forget (Over _)).map_isIso M.groupIso.hom
    apply characterLattice.TrivialOnKernel.of_postcomp χ (p.inclusion ≫ π_L) (identityComponentι S)
    have h' := characterLattice.TrivialOnKernel.comp_mono χ
      (p.inclusion ≫ (GroupScheme.baseChange (algebraBaseMap F L)).map π) M.groupIso.hom h
    change χ.TrivialOnKernel ((p.inclusion ≫ splitCover M hπ) ≫
      identityComponentι (OrthogonalMatrix.groupScheme (Fin 4) (CommRingCat.of L)))
    rw [Category.assoc, splitCover_factor M hπ, ← Category.assoc]
    exact h'
  let ρ : MatrixRepresentation G_L (Fin 4 ⊕ Fin 4) :=
    π_L ≫ identityComponentι S ≫ OrthogonalMatrix.inclusion (Fin 4) (CommRingCat.of L)
  obtain ⟨hWeight, hMax⟩ := OrthogonalMatrix.typeD4VectorMaximalWeight L G_L p
    π_L e (isSimplyConnected_splitCover (L := L) hπ) (isCentralIsogeny_splitCover M hπ)
    hcart hAlign (d.pinning_corootSpan_eq_top hsc)
  let D₀ := divisionAlgebra F D
  let A := Langlands.Brauer.matrix D₀ m
  let C := conjugatedChart eD P P' hPP' hP'P
  let s := (Fintype.equivFin (Fin 4 ⊕ Fin 4)).trans (finCongr (by decide : Fintype.card (Fin 4 ⊕ Fin 4) = 8))
  have hA : 8 = reducedDegree F A := matrix_size_eq_reducedDegree F A L 8
    (C.trans (Matrix.reindexAlgEquiv L L s))
  let s' := s.trans (finCongr hA)
  let C' := C.trans (Matrix.reindexAlgEquiv L L s')
  let f := normOneLift A hsc.isSemisimple (π ≫ σ.isometryGroupι q)
  have hf := normOneLift_comp A hsc.isSemisimple (π ≫ σ.isometryGroupι q)
  have hρ : (representation F A C').restrict ((GroupScheme.baseChange (algebraBaseMap F L)).map f) =
      ρ.reindex s' := by
    have he := normOneChart_eq_orthogonal eD σ hσ q P P' hPP' hP'P hPQ s' π f hf
    change _ = (MatrixRepresentation.reindex
      (MatrixRepresentation.restrict (OrthogonalMatrix.inclusion (Fin 4) (CommRingCat.of L))
        ((GroupScheme.baseChange (algebraBaseMap F L)).map π ≫ M.groupIso.hom)) s') at he
    rw [← splitCover_factor M hπ] at he
    exact he
  have hh : ((representation F A C').dual).restrict ((GroupScheme.baseChange (algebraBaseMap F L)).map f) =
      ρ.dual.reindex s' := by
    rw [← MatrixRepresentation.dual_restrict, hρ, dual_reindex]
  have hm₁ : Module.finrank L (p.representationWeightSpace ρ.dual w.val) = 1 := by
    rw [hw]
    exact hWeight
  have hmax₁ : ∀ χ, p.representationWeightSpace ρ.dual χ ≠ ⊥ →
      χ - w.val ∈ p.positiveRootMonoid → χ = w.val := by
    rw [hw]
    exact hMax
  have hclass := normOneHomDualTitsObstruction A C' d.pinning hsc w f
  change Module.finrank L (p.representationWeightSpace
      ((representation F A C').dual.restrict ((GroupScheme.baseChange (algebraBaseMap F L)).map f)) w.val) = 1 →
    (∀ χ, p.representationWeightSpace
      ((representation F A C').dual.restrict ((GroupScheme.baseChange (algebraBaseMap F L)).map f)) χ ≠ ⊥ →
      χ - w.val ∈ p.positiveRootMonoid → χ = w.val) →
    d.pinning.titsObstruction hsc w = -classOf A at hclass
  rw [hh, finrank_weightSpace_reindex, hobs] at hclass
  have hnz (χ : characterLattice p.torus) : p.representationWeightSpace (ρ.dual.reindex s') χ ≠ ⊥ →
      p.representationWeightSpace ρ.dual χ ≠ ⊥ := by
    intro hc hz
    apply hc
    apply Submodule.finrank_eq_zero.mp
    rw [finrank_weightSpace_reindex, hz, finrank_bot]
  have hzero : classOf A = 0 := neg_eq_zero.mp ((hclass hm₁ (fun χ hχ => hmax₁ χ (hnz χ hχ))).symm)
  have hD₁ : Module.finrank F D = 1 :=
    finrank_division_eq_one_of_classOf_eq_zero F D ((classOf_matrix D₀ m).symm.trans hzero)
  have hd₁ : degree = 1 := by
    rw [hD₁, pow_two] at hD
    exact Nat.mul_self_inj.mp hD.symm
  subst degree
  simp only [mul_one] at hm
  subst m
  exact spinCover_isotropic_of_scalar_division hD₁ σ q hq π hπ

end Langlands.GroupScheme
