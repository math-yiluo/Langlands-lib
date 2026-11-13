import Langlands.Global.SplitRankOneBinaryForm
import Langlands.GroupScheme.MatrixRepresentation.RankOneRootCoefficient
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.MatrixRepresentation.NormalKernel
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.MatrixRepresentation.UnipotentFixedLine

/-! # Root-group points acting on the binary form of a rank-one lowering curve

For a matrix representation `ρ` of a group scheme `G` over a field `F`, raising and
lowering additive maps `xp, xm` satisfying the rank-one relation with a cocharacter
`cor`, a coordinate vector `e = e_j` fixed by the raising map and lying on a torus
character line of weight `lam` with `⟨lam, cor⟩ = m`, this module verifies, over every
field extension `L` of `F`, the hypotheses of `SplitRankOneBinaryForm`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.SplitRankOne

open Langlands.GroupScheme
open Langlands.GroupScheme.MatrixRepresentation
open Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The affine additive point with coordinate `t`. -/
abbrev gaPoint (A : CommAlgCat.{u} F) (t : A) :
    (algSpec (CommRingCat.of F)).obj (op A) ⟶
      (VectorGroup.groupScheme (CommRingCat.of F) 1).X :=
  VectorGroup.affinePoint (R := CommRingCat.of F) (d := 1) A (fun _ => t)

/-- The affine multiplicative point with unit coordinate `u`. -/
abbrev gmPoint (A : CommAlgCat.{u} F) (u : Aˣ) :
    (algSpec (CommRingCat.of F)).obj (op A) ⟶ (Gm (Spec (CommRingCat.of F))).X :=
  (Gm.affinePointsEquiv ((algSpec (CommRingCat.of F)).obj (op A)).hom).symm u

/-- A character evaluated on the image of a cocharacter is a power. -/
theorem characterValue_cocharacter (A : CommAlgCat.{u} F)
    (χ : characterLattice T) (cor : cocharacterLattice T) (u : Aˣ) :
    Lie.characterValue χ (gmPoint A u ≫ (CommGroupScheme.groupHom cor).hom.hom) =
      u ^ latticePairing T χ cor := by
  have hνw : cor ≫ χ = (gmEndEquiv F).symm (latticePairing T χ cor) := by
    rw [latticePairing_apply, AddEquiv.symm_apply_apply]
  rw [Lie.characterValue, ← comp_groupHom_comp, hνw, gmEndEquiv_symm_comp, map_zpow]
  have h : Gm.affinePointsEquiv ((algSpec (CommRingCat.of F)).obj (op A)).hom
      (gmPoint A u) = u :=
    MulEquiv.apply_symm_apply _ u
  exact congrArg (· ^ latticePairing T χ cor) h

/-- Character values add. -/
theorem characterValue_add' (A : CommAlgCat.{u} F) (χ ψ : characterLattice T)
    (t : GroupScheme.affinePoints T.toGrp A) :
    Lie.characterValue (χ + ψ) t = Lie.characterValue χ t * Lie.characterValue ψ t := by
  unfold Lie.characterValue
  rw [← map_mul]
  exact congrArg _ (comp_groupHom_add t χ ψ)

theorem characterValue_zero' (A : CommAlgCat.{u} F) (t : GroupScheme.affinePoints T.toGrp A) :
    Lie.characterValue (0 : characterLattice T) t = 1 := by
  unfold Lie.characterValue
  rw [comp_groupHom_zero]
  exact map_one _

theorem characterValue_neg' (A : CommAlgCat.{u} F) (χ : characterLattice T)
    (t : GroupScheme.affinePoints T.toGrp A) :
    Lie.characterValue (-χ) t = (Lie.characterValue χ t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← characterValue_add', neg_add_cancel, characterValue_zero']

theorem characterValue_nsmul' (A : CommAlgCat.{u} F) (χ : characterLattice T) (d : ℕ)
    (t : GroupScheme.affinePoints T.toGrp A) :
    Lie.characterValue (d • χ) t = Lie.characterValue χ t ^ d := by
  induction d with
  | zero => rw [zero_nsmul, characterValue_zero', pow_zero]
  | succ d ih => rw [succ_nsmul, characterValue_add', ih, pow_succ]

variable (ρ : MatrixRepresentation G n) (j : n) (i : T.toGrp ⟶ G)
  (xp xm : VectorGroup.groupScheme (CommRingCat.of F) 1 ⟶ G)
  (cor : cocharacterLattice T) (α lam : characterLattice T) (m : ℤ)

/-- The scheme-level rank-one data used for the binary form: the rank-one relation, the
torus weight of the lowering map, the raising-fixed coordinate vector, its torus
character and the coroot weight `m = ⟨lam, cor⟩`. -/
structure CellHyp : Prop where
  cell : ∀ Z : Over (Spec (CommRingCat.of F)), RootCell.RelationOver i cor xp xm Z
  equivm : VectorGroup.IsTorusEquivariant i xm (-α)
  fixp : (ρ.restrict xp).IsFixedVector (Pi.single j 1)
  line : ∀ (A : CommAlgCat.{u} F) (τ : GroupScheme.affinePoints T.toGrp A),
    ((ρ.restrict i).affineMatrix A τ : Matrix n n A) *ᵥ (Pi.single j (1 : A) : n → A) =
      ((Lie.characterValue lam τ : Aˣ) : A) • (Pi.single j (1 : A) : n → A)
  pairing : latticePairing T lam cor = m

/-- The lowering matrices over an extension field. -/
def lowerMat (L : Type u) [Field L] [Algebra F L] (t : L) : Matrix n n L :=
  (univariateMatrix (ρ.restrict xm)).map (Polynomial.aeval t)

/-- The raising matrices over an extension field. -/
def raiseMat (L : Type u) [Field L] [Algebra F L] (s : L) : Matrix n n L :=
  (univariateMatrix (ρ.restrict xp)).map (Polynomial.aeval s)

/-- The coefficient vectors of the lowering curve through `e_j`, over `L`. -/
def wvec (L : Type u) [Field L] [Algebra F L] (d : ℕ) : n → L :=
  algebraMap F L ∘ coeffVec (univariateMatrix (ρ.restrict xm)) (Pi.single j 1) d

variable (L : Type u) [Field L] [Algebra F L]

theorem lowerMat_eq (t : L) :
    lowerMat ρ xm L t =
      ((ρ.restrict xm).affineMatrix (CommAlgCat.of F L) (gaPoint (CommAlgCat.of F L) t) :
        Matrix n n L) :=
  univariateMatrix_aeval (ρ.restrict xm) (CommAlgCat.of F L) t

theorem raiseMat_eq (s : L) :
    raiseMat ρ xp L s =
      ((ρ.restrict xp).affineMatrix (CommAlgCat.of F L) (gaPoint (CommAlgCat.of F L) s) :
        Matrix n n L) :=
  univariateMatrix_aeval (ρ.restrict xp) (CommAlgCat.of F L) s

theorem lowerMat_add (s t : L) :
    lowerMat ρ xm L (s + t) = lowerMat ρ xm L s * lowerMat ρ xm L t :=
  univariateMatrix_add (ρ.restrict xm) (CommAlgCat.of F L) s t

variable {ρ j i xp xm cor α lam m}

omit [Fintype n] in
theorem single_eq_algebraMap :
    (Pi.single j (1 : L) : n → L) = algebraMap F L ∘ (Pi.single j (1 : F) : n → F) := by
  funext r
  by_cases h : r = j
  · subst h; simp
  · simp [h]

theorem CellHyp.raiseMat_mulVec_single (h : CellHyp ρ j i xp xm cor α lam m) (s : L) :
    raiseMat ρ xp L s *ᵥ (Pi.single j (1 : L) : n → L) = Pi.single j 1 := by
  rw [raiseMat_eq, single_eq_algebraMap (F := F) L]
  exact h.fixp.affine (CommAlgCat.of F L) _

theorem CellHyp.coroot_mulVec_single (h : CellHyp ρ j i xp xm cor α lam m) (u : Lˣ) :
    (ρ.affineMatrix (CommAlgCat.of F L)
        (gmPoint (CommAlgCat.of F L) u ≫ (CommGroupScheme.groupHom cor).hom.hom ≫ i.hom.hom) :
          Matrix n n L) *ᵥ (Pi.single j (1 : L) : n → L) =
      (u : L) ^ m • (Pi.single j (1 : L) : n → L) := by
  have hl := h.line (CommAlgCat.of F L) (gmPoint (CommAlgCat.of F L) u ≫
    (CommGroupScheme.groupHom cor).hom.hom)
  rw [affineMatrix_restrict, Category.assoc] at hl
  rw [hl, characterValue_cocharacter, h.pairing]
  simp

/-- The rank-one relation applied to the fixed coordinate vector, over an extension field. -/
theorem CellHyp.relation (h : CellHyp ρ j i xp xm cor α lam m) (s t : L)
    (hst : 1 + s * t ≠ 0) :
    raiseMat ρ xp L s *ᵥ (lowerMat ρ xm L t *ᵥ (Pi.single j (1 : L) : n → L)) =
      (1 + s * t) ^ m •
        (lowerMat ρ xm L ((1 + s * t)⁻¹ * t) *ᵥ (Pi.single j (1 : L) : n → L)) := by
  set u : Lˣ := Units.mk0 (1 + s * t) hst with hu
  have hrel := RankOneRootCoefficient.affineMatrix_cell_relation ρ i cor xp xm h.cell
    (CommAlgCat.of F L) s t u rfl
  have hinv : ((u⁻¹ : Lˣ) : L) = (1 + s * t)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hu, Units.val_mk0]
  have hmat : raiseMat ρ xp L s * lowerMat ρ xm L t =
      lowerMat ρ xm L ((1 + s * t)⁻¹ * t) *
        (ρ.affineMatrix (CommAlgCat.of F L)
          (gmPoint (CommAlgCat.of F L) u ≫ (CommGroupScheme.groupHom cor).hom.hom ≫
            i.hom.hom) : Matrix n n L) *
        raiseMat ρ xp L ((1 + s * t)⁻¹ * s) := by
    rw [raiseMat_eq, lowerMat_eq, lowerMat_eq, raiseMat_eq, ← hinv]
    have := congrArg (fun g : GL n L => (g : Matrix n n L)) hrel
    simpa only [Units.val_mul] using this
  rw [Matrix.mulVec_mulVec, hmat]
  rw [← Matrix.mulVec_mulVec, h.raiseMat_mulVec_single L]
  rw [← Matrix.mulVec_mulVec, h.coroot_mulVec_single L, Matrix.mulVec_smul, hu, Units.val_mk0]

/-- **Degree bound.** The lowering curve through `e_j` has degree at most `m`. -/
theorem CellHyp.coeffVec_eq_zero [Infinite F] (h : CellHyp ρ j i xp xm cor α lam m)
    (d : ℕ) (hd : m < d) :
    coeffVec (univariateMatrix (ρ.restrict xm)) (Pi.single j (1 : F) : n → F) d = 0 := by
  refine coeffVec_eq_zero_of_relation (univariateMatrix (ρ.restrict xp)) _ _ m ?_ d hd
  intro t ht
  have hr := h.relation F 1 t (by simpa using ht)
  simp only [one_mul, lowerMat, raiseMat, Polynomial.coe_aeval_eq_eval] at hr
  exact hr

/-- The lowering matrix at `0` is the identity. -/
theorem lowerMat_zero : lowerMat ρ xm L 0 = 1 := by
  have hadd := lowerMat_add ρ xm L 0 0
  rw [add_zero, lowerMat_eq] at hadd
  have hg := congrArg (fun M => M * ((((ρ.restrict xm).affineMatrix (CommAlgCat.of F L)
    (gaPoint (CommAlgCat.of F L) 0))⁻¹ : GL n L) : Matrix n n L)) hadd
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_assoc] at hg
  rw [lowerMat_eq]
  simpa using hg.symm

/-- The constant coefficient of the lowering curve is `e_j`. -/
theorem coeffVec_zero :
    coeffVec (univariateMatrix (ρ.restrict xm)) (Pi.single j (1 : F) : n → F) 0 =
      Pi.single j 1 := by
  funext r
  have h := congrFun (mulVec_map_eval (univariateMatrix (ρ.restrict xm))
    (Pi.single j (1 : F) : n → F) 0) r
  have h0 : lowerMat ρ xm F 0 = (univariateMatrix (ρ.restrict xm)).map (Polynomial.eval 0) := by
    simp only [lowerMat, Polynomial.coe_aeval_eq_eval]
  rw [← h0, lowerMat_zero (ρ := ρ) (xm := xm) F, Matrix.one_mulVec] at h
  rw [coeffVec, Polynomial.coeff_zero_eq_eval_zero, ← h]

/-- The coroot weight of `e_j` is nonnegative. -/
theorem CellHyp.pairing_nonneg [Infinite F] (h : CellHyp ρ j i xp xm cor α lam m) : 0 ≤ m := by
  by_contra hm
  have h0 := h.coeffVec_eq_zero 0 (by exact_mod_cast not_le.mp hm)
  rw [coeffVec_zero] at h0
  have := congrFun h0 j
  simp at this

/-- A torus point normalizes the lowering curve through the inverse root value. -/
theorem CellHyp.torus_commute (h : CellHyp ρ j i xp xm cor α lam m)
    (τ : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F L)) (y : L) (v : n → L) :
    ((ρ.restrict i).affineMatrix (CommAlgCat.of F L) τ : Matrix n n L) *ᵥ
        (lowerMat ρ xm L y *ᵥ v) =
      lowerMat ρ xm L (((Lie.characterValue α τ : Lˣ) : L)⁻¹ * y) *ᵥ
        (((ρ.restrict i).affineMatrix (CommAlgCat.of F L) τ : Matrix n n L) *ᵥ v) := by
  have hc := h.equivm.affineMatrix_commutation ρ (CommAlgCat.of F L) τ y
  rw [characterValue_neg'] at hc
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, lowerMat_eq, lowerMat_eq]
  congr 1
  have := congrArg (fun g : GL n L => (g : Matrix n n L)) hc
  simpa only [Units.val_mul, Units.val_inv_eq_inv_val] using this

/-- The torus point acts on `e_j` by the line character. -/
theorem CellHyp.torus_mulVec_single (h : CellHyp ρ j i xp xm cor α lam m)
    (τ : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F L)) :
    ((ρ.restrict i).affineMatrix (CommAlgCat.of F L) τ : Matrix n n L) *ᵥ
        (Pi.single j (1 : L) : n → L) =
      ((Lie.characterValue lam τ : Lˣ) : L) • (Pi.single j (1 : L) : n → L) :=
  h.line (CommAlgCat.of F L) τ

section Natural

variable {k : ℕ}

/-- The rank-one relation with a natural coroot weight. -/
theorem CellHyp.relation_nat (h : CellHyp ρ j i xp xm cor α lam k) (s t : L)
    (hst : 1 + s * t ≠ 0) :
    raiseMat ρ xp L s *ᵥ (lowerMat ρ xm L t *ᵥ (Pi.single j (1 : L) : n → L)) =
      (1 + s * t) ^ k •
        (lowerMat ρ xm L ((1 + s * t)⁻¹ * t) *ᵥ (Pi.single j (1 : L) : n → L)) := by
  rw [h.relation L s t hst, zpow_natCast]

/-- The lowering curve through `e_j` is the dehomogenized binary form. -/
theorem CellHyp.lowerMat_mulVec_single [Infinite F] (h : CellHyp ρ j i xp xm cor α lam k)
    (t : L) :
    lowerMat ρ xm L t *ᵥ (Pi.single j (1 : L) : n → L) =
      binaryForm k (wvec ρ j xm L) 1 t := by
  rw [lowerMat, single_eq_algebraMap (F := F) L, mulVec_map_aeval,
    aeval_curve_eq_sum _ _ k (fun d hd => h.coeffVec_eq_zero d (by exact_mod_cast hd)),
    binaryForm_one_left]
  rfl

variable [Infinite F] [Infinite L]

/-- Lowering points act on the binary form by `GL₂`-substitutions. -/
theorem CellHyp.isBinarySimilitude_lower (h : CellHyp ρ j i xp xm cor α lam k) (y : L) :
    IsBinarySimilitude k (wvec ρ j xm L) (lowerMat ρ xm L y) 1 :=
  isBinarySimilitude_lowering k (wvec ρ j xm L) (lowerMat ρ xm L) _
    (h.lowerMat_mulVec_single L) (lowerMat_add ρ xm L) y

/-- Raising points act on the binary form by `GL₂`-substitutions. -/
theorem CellHyp.isBinarySimilitude_raise (h : CellHyp ρ j i xp xm cor α lam k) (z : L) :
    IsBinarySimilitude k (wvec ρ j xm L) (raiseMat ρ xp L z) 1 :=
  isBinarySimilitude_raising k (wvec ρ j xm L) (lowerMat ρ xm L) (raiseMat ρ xp L) _
    (h.lowerMat_mulVec_single L) (fun s t hst => h.relation_nat L s t hst) z

/-- Torus points act on the binary form by `GL₂`-substitutions, with multiplier
`λ(τ)² α(τ)^(-m)`. -/
theorem CellHyp.isBinarySimilitude_torus (h : CellHyp ρ j i xp xm cor α lam k)
    (τ : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F L)) :
    IsBinarySimilitude k (wvec ρ j xm L)
      ((ρ.restrict i).affineMatrix (CommAlgCat.of F L) τ : Matrix n n L)
      (((Lie.characterValue lam τ : Lˣ) : L) ^ 2 *
        (((Lie.characterValue α τ : Lˣ) : L)⁻¹) ^ k) :=
  SplitRankOne.isBinarySimilitude_torus k (wvec ρ j xm L) (lowerMat ρ xm L) _
    (h.lowerMat_mulVec_single L) _ _ _ (Units.ne_zero _) (Units.ne_zero _)
    (h.torus_mulVec_single L τ) (fun t => h.torus_commute L τ t _)

end Natural

end Langlands.Global.SplitRankOne
