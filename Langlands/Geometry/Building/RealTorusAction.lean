import Langlands.Geometry.Building.RealTorusSpace
import Langlands.GroupScheme.Torus.CocharacterAction

/-! # Real torus automorphisms and the normalizer and relative Weyl actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The real extension of the published inverse-precomposition character automorphism. -/
def characterRealAut (σ : T ≅ T) : Vstar T ≃ₗ[ℝ] Vstar T :=
  LinearEquiv.baseChange ℤ ℝ _ _ (characterAut σ)

/-- The real extension of postcomposition on cocharacters. -/
def cocharacterRealAut (σ : T ≅ T) : V T ≃ₗ[ℝ] V T :=
  LinearEquiv.baseChange ℤ ℝ _ _ (cocharacterAut σ)

@[simp] theorem characterRealAut_tmul (σ : T ≅ T) (r : ℝ) (χ : characterLattice T) :
    characterRealAut σ (r ⊗ₜ[ℤ] χ) = r ⊗ₜ[ℤ] (σ.inv ≫ χ) := rfl

@[simp] theorem cocharacterRealAut_tmul (σ : T ≅ T) (r : ℝ) (ν : cocharacterLattice T) :
    cocharacterRealAut σ (r ⊗ₜ[ℤ] ν) = r ⊗ₜ[ℤ] (ν ≫ σ.hom) := rfl

/-- The scalar-extended pairing is invariant under simultaneous automorphisms. -/
theorem pair_aut (σ : T ≅ T) (x : Vstar T) (v : V T) :
    pair T (characterRealAut σ x) (cocharacterRealAut σ v) = pair T x v := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    induction v using TensorProduct.inductionOn with
    | tmul s ν =>
      simpa only [characterRealAut_tmul, cocharacterRealAut_tmul, pair_tmul_tmul,
        characterAut_apply, cocharacterAut_apply] using
        congrArg (fun z : ℤ => r * s * (z : ℝ)) (latticePairing_aut σ χ ν)
    | add v w hv hw => simp only [map_add, hv, hw]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Evaluation is invariant under the simultaneous character and cocharacter action. -/
theorem eval_aut (σ : T ≅ T) (χ : characterLattice T) (v : V T) :
    eval T (characterAut σ χ) (cocharacterRealAut σ v) = eval T χ v := by
  simpa only [eval_eq_pair, characterRealAut_tmul, characterAut_apply] using
    pair_aut σ (1 ⊗ₜ[ℤ] χ) v

variable {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
  [Mono i.hom.hom.left]

/-- The real linear action of the actual normalizer points on the cocharacter space. -/
def normalizerAction : normalizerPoints i →* (V T ≃ₗ[ℝ] V T) where
  toFun n := cocharacterRealAut (normalizingAut i n)
  map_one' := by
    have h : normalizingAut i 1 = Iso.refl T :=
      (isNormalizingPoint_normalizingAut i 1).unique i IsNormalizingPoint.one
    apply LinearEquiv.toLinearMap_injective
    apply AlgebraTensorModule.ext
    intro r ν
    simp [h]
  map_mul' n m := by
    have h : normalizingAut i (n * m) = normalizingAut i m ≪≫ normalizingAut i n :=
      (isNormalizingPoint_normalizingAut i (n * m)).unique i
        ((isNormalizingPoint_normalizingAut i n).mul (isNormalizingPoint_normalizingAut i m))
    apply LinearEquiv.toLinearMap_injective
    apply AlgebraTensorModule.ext
    intro r ν
    simp [h, Category.assoc]

@[simp] theorem normalizerAction_tmul (n : normalizerPoints i) (r : ℝ)
    (ν : cocharacterLattice T) :
    normalizerAction i n (r ⊗ₜ[ℤ] ν) = r ⊗ₜ[ℤ] (ν ≫ (normalizingAut i n).hom) := rfl

instance normalizerDistribMulAction : DistribMulAction (normalizerPoints i) (V T) where
  smul n v := normalizerAction i n v
  one_smul v := by change normalizerAction i 1 v = v; simp
  mul_smul n m v := by
    change normalizerAction i (n * m) v = normalizerAction i n (normalizerAction i m v)
    rw [map_mul, LinearEquiv.mul_apply]
  smul_zero n := (normalizerAction i n).map_zero
  smul_add n v w := (normalizerAction i n).map_add v w

theorem normalizer_smul_def (n : normalizerPoints i) (v : V T) :
    n • v = normalizerAction i n v := rfl

/-- Centralizer points act as the identity on the real cocharacter space. -/
theorem normalizerAction_eq_one_of_mem_centralizerPoints {n : normalizerPoints i}
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ centralizerPoints i) :
    normalizerAction i n = 1 := by
  have h : normalizingAut i n = Iso.refl T :=
    (isNormalizingPoint_normalizingAut i n).unique i hn
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro r ν
  simp [normalizerAction, h]

/-- The real cocharacter action descends to the Library's actual relative Weyl quotient. -/
def relativeWeylRealAction : relativeWeylGroup i →* (V T ≃ₗ[ℝ] V T) :=
  QuotientGroup.lift _ (normalizerAction i) fun _ hz =>
    normalizerAction_eq_one_of_mem_centralizerPoints i hz

@[simp] theorem relativeWeylRealAction_mk (n : normalizerPoints i) :
    relativeWeylRealAction i (QuotientGroup.mk n) = normalizerAction i n := rfl

instance relativeWeylDistribMulAction : DistribMulAction (relativeWeylGroup i) (V T) where
  smul w v := relativeWeylRealAction i w v
  one_smul v := by change relativeWeylRealAction i 1 v = v; simp
  mul_smul w z v := by
    change relativeWeylRealAction i (w * z) v =
      relativeWeylRealAction i w (relativeWeylRealAction i z v)
    rw [map_mul, LinearEquiv.mul_apply]
  smul_zero w := (relativeWeylRealAction i w).map_zero
  smul_add w v z := (relativeWeylRealAction i w).map_add v z

theorem relativeWeyl_smul_def (w : relativeWeylGroup i) (v : V T) :
    w • v = relativeWeylRealAction i w v := rfl

@[simp] theorem relativeWeyl_mk_smul (n : normalizerPoints i) (v : V T) :
    (QuotientGroup.mk n : relativeWeylGroup i) • v = n • v := rfl

/-- The real cocharacter action is contragredient to the published character action. -/
theorem eval_normalizer_smul (n : normalizerPoints i) (χ : characterLattice T) (v : V T) :
    eval T χ (n • v) = eval T (weylAction i n⁻¹ χ) v := by
  have h := eval_aut (normalizingAut i n) (weylAction i n⁻¹ χ) v
  change eval T (weylAction i n (weylAction i n⁻¹ χ)) (n • v) = _ at h
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

/-- The same contragredient identity applies to every actual relative root. -/
theorem rootEval_normalizer_smul [IsAffineHom G.X.hom]
    (n : normalizerPoints i) (α : relativeRoots i) (v : V T) :
    rootEval T i α (n • v) =
      rootEval T i ⟨weylAction i n⁻¹ α.1,
        weylAction_mapsTo_relativeRoots i n⁻¹ α.2⟩ v :=
  eval_normalizer_smul i n α.1 v

end Langlands.GroupScheme.RealTorusSpace
