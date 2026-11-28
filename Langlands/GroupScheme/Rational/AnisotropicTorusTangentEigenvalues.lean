import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.MatrixRepresentation.CharacterDifferential
import Langlands.GroupScheme.MatrixRepresentation.GaloisCharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Rational.AnisotropicGaloisFixedCharacters
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Ground-field eigenvalues of anisotropic torus differentials -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

namespace MatrixRepresentation

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom]

omit [IsAffineHom H.X.hom] in
private theorem fst_character_unit (X : lieKernel H k) (χ : rationalCharacters H) :
    (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k (DualNumber k))
      (X.val ≫ χ.toMul.hom.hom) : DualNumber k).fst = 1 := by
  let y := Lie.targetMap χ.toMul k X
  have hy := y.property
  change GroupScheme.affinePointMap _ (CommAlgCat.ofHom (TrivSqZeroExt.fstHom k k k)) y.val = 1 at hy
  have hh := congrArg (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k k)) hy
  rw [Gm.affineUnitsEquiv_naturality, map_one] at hh
  exact congrArg Units.val hh

/-- Differentiating characters at one actual tangent point is additive in the character. -/
def characterTangentScalarAddHom (X : lieKernel H k) : rationalCharacters H →+ k where
  toFun χ := characterTangentScalar χ X
  map_zero' := by
    simp [characterTangentScalar]
  map_add' χ ψ := by
    unfold characterTangentScalar
    rw [rationalCharacters.comp_add, map_mul, Units.val_mul, TrivSqZeroExt.snd_mul,
      fst_character_unit X χ, fst_character_unit X ψ]
    simp [add_comm]

end MatrixRepresentation

open MatrixRepresentation

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

/-- A rational eigenvalue of the tangent action of any torus inside an anisotropic
characteristic-zero group is zero. -/
theorem IsAnisotropic.tangentMatrix_eigenvalue_eq_zero
    {k : Type u} [Field k] [CharZero k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsAnisotropic G) {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsClosedSubgroup i) (hT : IsTorus T.toGrp) {n : ℕ}
    (ρ : MatrixRepresentation T.toGrp (Fin n)) (X : lieKernel T.toGrp k)
    (value : k) (v : Fin n → k) (hv : v ≠ 0)
    (he : ρ.tangentMatrix k X *ᵥ v = value • v) : value = 0 := by
  classical
  let : IsAffineHom T.toGrp.X.hom := hi.isAffineHom
  obtain ⟨K, _, _, _, _, hsplit⟩ := torusFiniteGaloisSplitting k T.toGrp hT
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let b := algebraBaseMap k K
  let TK := (CommGroupScheme.baseChange b).obj T
  let ρK := ρ.baseChange b
  let X₀ := lieKernelMap T.toGrp (Algebra.ofId k K) X
  let XK := (Lie.kernelBaseChangeEquiv k K T.toGrp K).symm X₀
  let B := ρK.tangentMatrix K XK
  have hB : B = (ρ.tangentMatrix k X).map (algebraMap k K) := by
    change (ρ.baseChange b).tangentMatrix K ((Lie.kernelBaseChangeEquiv k K T.toGrp K).symm X₀) = _
    rw [ρ.tangentMatrix_baseChange, MulEquiv.apply_symm_apply, ρ.tangentMatrix_naturality]
    rfl
  let vK : Fin n → K := fun i => algebraMap k K (v i)
  let eigen := algebraMap k K value
  have hvK : vK ≠ 0 := by
    intro h
    apply hv
    funext i
    exact (algebraMap k K).injective (by simpa [vK] using congrFun h i)
  have heK : B *ᵥ vK = eigen • vK := by
    funext j
    rw [hB]
    change ((ρ.tangentMatrix k X).map (algebraMap k K) *ᵥ (algebraMap k K ∘ v)) j = _
    rw [← RingHom.map_mulVec, he]
    change algebraMap k K (value * v j) = eigen * algebraMap k K (v j)
    exact map_mul _ _ _
  let D : Module.End K (Fin n → K) := Matrix.toLin' B
  let scalar := characterTangentScalarAddHom XK
  have hspan := ρK.iSup_characterSpace_eq_top_of_isSplitTorus hsplit
  have hχ : ∃ χ : rationalCharacters TK.toGrp, ρK.characterSpace χ ≠ ⊥ ∧ scalar χ = eigen := by
    by_contra! hn
    let W := ⨆ a ∈ {a : K | a ≠ eigen}, D.eigenspace a
    have hdis : Disjoint (D.eigenspace eigen) W :=
      (Module.End.eigenspaces_iSupIndep D).disjoint_biSup (by simp)
    have htop : (⊤ : Submodule K (Fin n → K)) ≤ W := by
      rw [← hspan]
      refine iSup_le fun χ => ?_
      by_cases hzero : ρK.characterSpace χ = ⊥
      · rw [hzero]
        exact bot_le
      · have hl : ρK.characterSpace χ ≤ D.eigenspace (scalar χ) := by
          intro y hy
          apply Module.End.mem_eigenspace_iff.mpr
          exact ρK.tangentMatrix_mulVec_of_mem_characterSpace χ hy XK
        exact hl.trans (le_iSup_of_le (scalar χ)
          (le_iSup (fun _ : scalar χ ∈ {a : K | a ≠ eigen} => D.eigenspace (scalar χ)) (hn χ hzero)))
    have hvec : vK ∈ D.eigenspace eigen := Module.End.mem_eigenspace_iff.mpr heK
    exact hvK ((Submodule.disjoint_def.mp hdis) vK hvec (htop (Submodule.mem_top)))
  obtain ⟨χ, hχ, hEigen⟩ := hχ
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hχ
  let A := rationalCharacters.galoisRepresentation k K T.toGrp
  have hcoeff (σ : K ≃ₐ[k] K) : scalar (A σ χ) = eigen := by
    let y : Fin n → K := fun i => σ (w i)
    have hy : y ∈ ρK.characterSpace (A σ χ) :=
      conjugate_mem_characterSpace_baseChange ρ σ χ hw
    have hy0 : y ≠ 0 := by
      intro h
      apply hw0
      funext i
      exact σ.injective (by simpa [y] using congrFun h i)
    have hwEigen : B *ᵥ w = eigen • w := by
      rw [← hEigen]
      exact ρK.tangentMatrix_mulVec_of_mem_characterSpace χ hw XK
    have hmap : B.map σ.toRingHom = B := by
      ext i j
      rw [hB]
      exact σ.commutes _
    have hyEigen : B *ᵥ y = eigen • y := by
      funext j
      calc
        (B *ᵥ y) j = σ ((B *ᵥ w) j) := by
          change (B *ᵥ (σ.toRingHom ∘ w)) j = σ.toRingHom ((B *ᵥ w) j)
          simpa only [hmap] using (σ.toRingHom.map_mulVec B w j).symm
        _ = (eigen • y) j := by
          rw [hwEigen]
          change σ (eigen * w j) = eigen * σ (w j)
          rw [map_mul, σ.commutes value]
    have heq : (scalar (A σ χ) - eigen) • y = 0 := by
      have hweight : B *ᵥ y = scalar (A σ χ) • y :=
        ρK.tangentMatrix_mulVec_of_mem_characterSpace _ hy XK
      rw [sub_smul, ← hweight, hyEigen, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp heq).resolve_right hy0)
  let : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  let ψ := ∑ σ : K ≃ₐ[k] K, A σ χ
  have hfix (τ : K ≃ₐ[k] K) : A τ ψ = ψ := by
    simp only [ψ, map_sum, ← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)
  let E := rationalCharacters.equivCharacterLattice TK
  have hψ : ψ = 0 := by
    apply E.injective
    rw [E.map_zero]
    apply hG.galoisFixed_character_eq_zero hi hT K
    intro σ
    change _ = rationalCharacters.equivCharacterLattice TK ψ
    rw [← rationalCharacters.equivCharacterLattice_galoisRepresentation]
    exact congrArg E (hfix σ)
  have hsum : (Fintype.card (K ≃ₐ[k] K) : K) * eigen = 0 := by
    have h := congrArg scalar hψ
    simpa [ψ, hcoeff, nsmul_eq_mul] using h
  have hcard : (Fintype.card (K ≃ₐ[k] K) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  apply (algebraMap k K).injective
  rw [(algebraMap k K).map_zero]
  exact (mul_eq_zero.mp hsum).resolve_left hcard

/-- Ground-field eigenvalues of the tangent action of a torus in an anisotropic group. -/
def AnisotropicTorusTangentEigenvaluesStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
      (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsClosedSubgroup i → IsTorus T.toGrp →
      ∀ (n : ℕ) (ρ : MatrixRepresentation T.toGrp (Fin n)) (X : lieKernel T.toGrp k)
        (value : k) (v : Fin n → k), v ≠ 0 →
          ρ.tangentMatrix k X *ᵥ v = value • v → value = 0

theorem anisotropicTorusTangentEigenvalues : AnisotropicTorusTangentEigenvaluesStatement.{u} :=
  fun _ _ _ _ _ _ hG _ _ hi hT _ ρ X value v hv he =>
    hG.tangentMatrix_eigenvalue_eq_zero hi hT ρ X value v hv he

end Langlands.GroupScheme
