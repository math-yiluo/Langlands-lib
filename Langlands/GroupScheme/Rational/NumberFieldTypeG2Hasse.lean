import Langlands.GroupScheme.Composition.CayleyGaloisDescent
import Langlands.GroupScheme.SimplyConnected.TypeG2CayleyPresentationProof
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof

/-! # The number-field Hasse kernel for simply connected type G2 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CayleyDatum

open GaloisPoint

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {c : CayleyDatum F} {iG : G ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of F)}

local notation "S" => CommRingCat.of F
local notation "A[" L "]" => CommAlgCat.of S L
local notation "GL₈" => GeneralLinear.groupScheme (Fin 8) S

/-- The actual representation on affine coefficient points in matrix coordinates. -/
private def matrixPoint (iG : G ⟶ GL₈) (L : Type u) [Field L] [Algebra F L] :
    G.affinePoints (A[L]) →* GL (Fin 8) L :=
  (GeneralLinear.affinePointsEquiv (Fin 8) S (A[L])).toMonoidHom.comp
    (G.affinePointsTarget iG (A[L]))

private theorem matrixPoint_naturality
    {L M : Type u} [Field L] [Algebra F L] [Field M] [Algebra F M]
    (a : L →ₐ[F] M) (x : G.affinePoints (A[L])) :
    matrixPoint iG M (G.affinePointMap (CommAlgCat.ofHom a) x) =
      GeneralLinearGroup.map a.toRingHom (matrixPoint iG L x) := by
  change GeneralLinear.affinePointsEquiv (Fin 8) S (A[M])
    (((algSpec S).map (CommAlgCat.ofHom a).op ≫ x) ≫ iG.hom.hom) = _
  rw [Category.assoc, GeneralLinear.affinePointsEquiv_naturality]
  rfl

private theorem matrixPoint_conjugate {L : Type u} [Field L] [Algebra F L]
    (σ : L ≃ₐ[F] L) (x : G.affinePoints (A[L])) :
    matrixPoint iG L (conjugate F L G σ x) =
      GeneralLinearGroup.map (σ : L →+* L) (matrixPoint iG L x) :=
  matrixPoint_naturality σ.toAlgHom x

private theorem matrixPoint_range (p : c.IsAutomorphismRepresentation iG) {L : Type u}
    [Field L] [Algebra F L] (B : GL (Fin 8) L) :
    B ∈ Set.range (matrixPoint iG L) ↔ c.IsAutomorphismMatrix (algebraMap F L) B := by
  let R := A[L]
  let T := (algSpec S).obj (op R)
  let sec := (Corepresented.affineSectionsIso R).inv
  let f := sec.hom.toRingHom
  have hf : f.comp (algebraMap F L) = algebraMap S ((algΓ S).obj T).unop := by
    ext k
    exact sec.hom.commutes k
  have hf' : Function.Injective f := (ConcreteCategory.bijective_of_isIso sec).1
  let b := (GeneralLinear.affinePointsEquiv (Fin 8) S R).symm B
  have hb := p.2 T b
  rw [GeneralLinear.pointsEquiv_eq_affinePointsEquiv, MulEquiv.apply_symm_apply] at hb
  change b ∈ (SubgroupFunctor.range iG).carrier T ↔
    IsIsomorphismMatrix (algebraMap S ((algΓ S).obj T).unop) c c (GeneralLinearGroup.map f B) at hb
  rw [← hf] at hb
  constructor
  · rintro ⟨x, hx⟩
    have hx' : x ≫ iG.hom.hom = b := by
      apply (GeneralLinear.affinePointsEquiv (Fin 8) S R).injective
      exact hx.trans ((GeneralLinear.affinePointsEquiv (Fin 8) S R).apply_symm_apply B).symm
    exact IsIsomorphismMatrix.of_map f hf' (hb.mp (SubgroupFunctor.mem_range.mpr ⟨x, hx'⟩))
  · intro hB
    obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp (hb.mpr (IsIsomorphismMatrix.map hB f))
    refine ⟨x, ?_⟩
    change GeneralLinear.affinePointsEquiv (Fin 8) S R (x ≫ iG.hom.hom) = B
    rw [hx, MulEquiv.apply_symm_apply]

private theorem matrixPoint_injective (p : c.IsAutomorphismRepresentation iG) (L : Type u)
    [Field L] [Algebra F L] : Function.Injective (matrixPoint iG L) := by
  intro x y h
  let : IsClosedImmersion iG.hom.hom.left := p.1
  let : Mono iG.hom.hom := Over.mono_of_mono_left iG.hom.hom
  apply (cancel_mono iG.hom.hom).mp
  exact (GeneralLinear.affinePointsEquiv (Fin 8) S (A[L])).injective h

section Descent

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  (ξ : Cocycle G (GaloisCocycle.cover F L))

private structure MatrixPrimitive where
  matrix : GL (Fin 8) L
  coboundary : ∀ σ : L ≃ₐ[F] L, matrixPoint iG L (GaloisCocycle.value ξ σ) =
    matrix * (GeneralLinearGroup.map (σ : L →+* L) matrix)⁻¹

omit [IsGalois F L] in
private theorem exists_matrixPrimitive : Nonempty (MatrixPrimitive (iG := iG) ξ) := by
  let g (σ : L ≃ₐ[F] L) := matrixPoint iG L (GaloisCocycle.value ξ σ)
  have hg (σ τ : L ≃ₐ[F] L) : g (σ * τ) = g σ * GeneralLinearGroup.map (σ : L →+* L) (g τ) := by
    simp only [g, GaloisCocycle.value_mul, _root_.map_mul]
    rw [matrixPoint_conjugate σ]
  obtain ⟨P, hP⟩ := Langlands.LinearAlgebra.GaloisFixedBasis.exists_fixed (g := g) hg
  exact ⟨⟨P, fun σ => eq_mul_inv_of_mul_eq (hP σ)⟩⟩

variable {ξ} (p : c.IsAutomorphismRepresentation iG) (t : MatrixPrimitive (iG := iG) ξ)

include p in
omit [FiniteDimensional F L] [IsGalois F L] in
private theorem MatrixPrimitive.isGaloisTwist : c.IsGaloisTwist t.matrix := by
  intro σ
  rw [← t.coboundary]
  exact (matrixPoint_range p _).mp ⟨_, rfl⟩

variable [Infinite F] [Invertible (2 : F)]

private def MatrixPrimitive.datum : CayleyDatum F := galoisTwist (t.isGaloisTwist p)

private theorem MatrixPrimitive.isIsomorphismMatrix :
    IsIsomorphismMatrix (algebraMap F L) (t.datum p) c t.matrix :=
  galoisTwist_isIsomorphismMatrix (t.isGaloisTwist p)

private theorem MatrixPrimitive.isTrivial_of_normIsometry
    (h2 : (2 : F) ≠ 0) (a : c.norm.IsometryEquiv (t.datum p).norm) : ξ.IsTrivial := by
  obtain ⟨e, hU, hM⟩ := c.exists_preserves_mul_unit_of_norm_isometry _ h2 a
  obtain ⟨R, hR⟩ := exists_isIsomorphismMatrix_of_linearEquiv e hU hM
  let Q := GeneralLinearGroup.map (algebraMap F L) R
  have hQ : IsIsomorphismMatrix (algebraMap F L) c (t.datum p) Q := by
    simpa only [RingHom.comp_id] using hR.map (algebraMap F L)
  obtain ⟨b, hb⟩ := (matrixPoint_range p (t.matrix * Q)).mpr ((t.isIsomorphismMatrix p).mul hQ)
  refine (GaloisCocycle.isTrivial_iff ξ).mpr ⟨b, fun σ => ?_⟩
  apply matrixPoint_injective p L
  have hfix : GeneralLinearGroup.map (σ : L →+* L) Q = Q := by
    have he : (σ : L →+* L).comp (algebraMap F L) = algebraMap F L :=
      RingHom.ext fun a => σ.commutes a
    change GeneralLinearGroup.map ((σ : L →+* L).comp (algebraMap F L)) R = Q
    rw [he]
  rw [t.coboundary, _root_.map_mul, _root_.map_inv, matrixPoint_conjugate, hb, _root_.map_mul, hfix]
  group

variable {K M : Type u} [Field K] [Algebra F K] [Field M] [Algebra F M]
  [Algebra K M] [Algebra L M] [IsScalarTower F K M] [IsScalarTower F L M]
  [FiniteDimensional K M] [IsGalois K M]

private theorem exists_fixed_matrix (B : GL (Fin 8) M)
    (hB : ∀ σ : M ≃ₐ[K] M, GeneralLinearGroup.map (σ : M →+* M) B = B) :
    ∃ R : GL (Fin 8) K, GeneralLinearGroup.map (algebraMap K M) R = B := by
  choose r hr using fun i j : Fin 8 =>
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) ((B : Matrix (Fin 8) (Fin 8) M) i j)).mpr
      (fun σ => congrArg (fun x : GL (Fin 8) M => (x : Matrix (Fin 8) (Fin 8) M) i j) (hB σ))
  let R := Matrix.of r
  have hR : (algebraMap K M).mapMatrix R = (B : Matrix (Fin 8) (Fin 8) M) := Matrix.ext hr
  have hdet : R.det ≠ 0 := by
    intro h
    have h' := (algebraMap K M).map_det R
    rw [h, _root_.map_zero, hR] at h'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero h'.symm
  exact ⟨GeneralLinearGroup.mk'' R (isUnit_iff_ne_zero.mpr hdet), Units.ext hR⟩

include M in
private theorem MatrixPrimitive.exists_local_isomorphism
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ R : GL (Fin 8) K, IsIsomorphismMatrix (algebraMap F K) (t.datum p) c R := by
  obtain ⟨b, hb⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
    (K := K) (M := M) ξ h
  let B := GeneralLinearGroup.map (algebraMap L M) t.matrix
  let Y := matrixPoint iG M b
  have hY : IsIsomorphismMatrix (algebraMap F M) c c Y :=
    (matrixPoint_range p Y).mp ⟨b, rfl⟩
  have hB : IsIsomorphismMatrix (algebraMap F M) (t.datum p) c B := by
    simpa only [IsScalarTower.algebraMap_eq F L M] using (t.isIsomorphismMatrix p).map (algebraMap L M)
  have hfix (s : M ≃ₐ[K] M) : GeneralLinearGroup.map (s : M →+* M) (Y⁻¹ * B) = Y⁻¹ * B := by
    let s₀ := s.restrictScalars F
    let s₁ := s₀.restrictNormal L
    have hval := congrArg (matrixPoint iG M) (hb s)
    change matrixPoint iG M (relativeExtend F L M G (GaloisCocycle.value ξ s₁)) =
      matrixPoint iG M (b * (conjugate F M G s₀ b)⁻¹) at hval
    rw [show matrixPoint iG M (relativeExtend F L M G (GaloisCocycle.value ξ s₁)) =
        GeneralLinearGroup.map (algebraMap L M) (matrixPoint iG L (GaloisCocycle.value ξ s₁)) from
          matrixPoint_naturality (IsScalarTower.toAlgHom F L M) _,
      t.coboundary, _root_.map_mul, _root_.map_inv, _root_.map_mul, _root_.map_inv,
      matrixPoint_conjugate] at hval
    have hcomp : (algebraMap L M).comp (s₁ : L →+* L) = (s : M →+* M).comp (algebraMap L M) :=
      RingHom.ext fun x => s₀.restrictNormal_commutes L x
    rw [← GeneralLinearGroup.map_comp_apply, ← GeneralLinearGroup.map_comp, hcomp,
      GeneralLinearGroup.map_comp, MonoidHom.comp_apply] at hval
    change B * (GeneralLinearGroup.map (s : M →+* M) B)⁻¹ =
      Y * (GeneralLinearGroup.map (s : M →+* M) Y)⁻¹ at hval
    have hv := congrArg (fun x => Y⁻¹ * x * GeneralLinearGroup.map (s : M →+* M) B) hval
    group at hv
    rw [_root_.map_mul, _root_.map_inv]
    simpa only [_root_.zpow_neg_one] using hv.symm
  obtain ⟨R, hR⟩ := exists_fixed_matrix (Y⁻¹ * B) hfix
  refine ⟨R, IsIsomorphismMatrix.of_map (algebraMap K M) (algebraMap K M).injective ?_⟩
  rw [← IsScalarTower.algebraMap_eq F K M, hR]
  exact hY.inv.mul hB

private theorem MatrixPrimitive.local_normIsometry [CharZero K]
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    (c.norm.baseChange K).Equivalent ((t.datum p).norm.baseChange K) := by
  obtain ⟨M, _, _, _, _, _, _, _, _⟩ := CentralSimpleUnits.exists_finiteGalois_over_baseChange F K L
  obtain ⟨R, hR⟩ := t.exists_local_isomorphism p (M := M) h
  exact ⟨(c.baseChangeNormIsometry (A := K)).trans
    (hR.normIsometry.symm.trans (t.datum p).baseChangeNormIsometry.symm)⟩

end Descent

end Langlands.GroupScheme.CayleyDatum

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

/-- The localization kernel for actual numbered absolutely almost-simple simply
  connected groups of type G2 over number fields. -/
def NumberFieldTypeG2HasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 2),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- Full local triviality of a type G2 cocycle identifies the descended Cayley norm
  at every completion, so Hasse–Minkowski makes the original cocycle trivial. -/
theorem numberFieldTypeG2Hasse : NumberFieldTypeG2HasseStatement.{u} := by
  intro F _ _ G _ _ d e hsc habs hcart L _ _ _ _ ξ hξ
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨c, iG, p⟩ := typeG2CayleyPresentation F G d e hsc habs hcart
  obtain ⟨t⟩ := CayleyDatum.exists_matrixPrimitive (iG := iG) ξ
  have hloc (v : Global.Place F) : (c.norm.baseChange (Global.placeCompletion F v)).Equivalent
      ((t.datum p).norm.baseChange (Global.placeCompletion F v)) := by
    rcases v with v | v
    · let : CharZero v.Completion := charZero_of_injective_algebraMap (algebraMap F v.Completion).injective
      exact t.local_normIsometry p (K := v.Completion) (hξ (.inl v))
    · let : CharZero (Global.FiniteCompletion F v) := charZero_of_injective_algebraMap
        (algebraMap F (Global.FiniteCompletion F v)).injective
      exact t.local_normIsometry p (K := Global.FiniteCompletion F v) (hξ (.inr v))
  obtain ⟨a⟩ := Langlands.numberFieldQuadraticIsometry F 8 c.norm (t.datum p).norm
    c.norm_nondegenerate (t.datum p).norm_nondegenerate hloc
  exact t.isTrivial_of_normIsometry p two_ne_zero a

end Langlands.GroupScheme
