import Langlands.Global.ArthurWeylHeightStatement
import Langlands.Global.AdelicLineCharacterHeight
import Langlands.Global.AdelicOrbitHeightCompactBounds
import Langlands.GroupScheme.Dynamic.GeneralLinearProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Rational.StandardMinimalLeviMultiplication
import Langlands.GroupScheme.Rational.BruhatContractionReduction
import Langlands.GroupScheme.Rational.MaximalParabolicLineDominance
import Langlands.GroupScheme.Rational.MinimalParabolicLineCharacter
import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationProof
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof

/-! # The uniform Weyl displacement bound for the minimal Iwasawa height -/

noncomputable section

set_option maxHeartbeats 240000

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open AdelicGroupPoints ArthurParabolicSpaces RepresentationGrowth
open Langlands.Aubert.General.RationalPointFamily
open Langlands.Automorphic.GroupSchemeFunctions (innerAdelicPoint innerAdelicPoint_eq_rational)

/-- An invertible coordinate of a primitive vector has idelic norm at most the
primitive-vector height. The norms at every place use the same normalization. -/
private theorem ideleNorm_le_primitiveHeight {F : Type u} [Field F] [NumberField F] {d : ℕ}
    {v : PrimitiveAdelicHeight.Vector F d} (hv : PrimitiveAdelicHeight.IsPrimitive F d v)
    (j : Fin d) (z : Ideles F) (hz : z.val = v j) :
    ((IdeleAbsoluteValue.full F z : ℝ≥0) : ℝ) ≤ PrimitiveAdelicHeight.height F d v := by
  rw [IdeleAbsoluteValue.coe_full, PrimitiveAdelicHeight.height]
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
  · refine Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _) fun place _ => ?_
    apply pow_le_pow_left₀ (norm_nonneg _)
    change ‖infiniteProjection F place z.val‖ ≤ ‖fun l : Fin d => infiniteProjection F place (v l)‖
    rw [hz]
    exact norm_le_pi_norm (fun l : Fin d => infiniteProjection F place (v l)) j
  · have hfin : (fun p : FinitePlace F => ‖z.val.2 p‖).HasFiniteMulSupport :=
      NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (ideleProductEquiv F z).2
    refine finprod_le_finprod₀ hfin (fun _ => norm_nonneg _) (hv.hasFiniteMulSupport F d) ?_
    intro place
    change ‖finiteProjection F place z.val‖ ≤ ‖fun l : Fin d => finiteProjection F place (v l)‖
    rw [hz]
    exact norm_le_pi_norm (fun l : Fin d => finiteProjection F place (v l)) j

section CompactComparison

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

private theorem characterNorm_exp_height (χ : rationalCharacters P)
    {q : AdelicGroupPoints F P} {k x : AdelicGroupPoints F G}
    (hk : k ∈ K) (hx : map F P G p q * k = x) :
    ((characterNorm F P χ.toMul q⁻¹ : ℝ≥0) : ℝ) = Real.exp (-hK.height x χ) := by
  rw [hK.height_eq hk hx, characterLog_apply, map_inv, Units.val_inv_eq_inv_val,
    NNReal.coe_inv, Real.exp_neg, Real.exp_log]
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (characterNorm F P χ.toMul q).ne_zero)

/-- Compare Iwasawa logarithms through two rational vectors in an actual representation.
The first vector is a parabolic eigenvector. For the second vector one specified
coordinate records the second parabolic character. Compactness of the Iwasawa
subgroup bounds the effect of the two compact factors. -/
private theorem exists_heightCharacter_le_add_of_orbit_eq {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    {v₁ v₂ : Fin d → F} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (j : Fin d)
    (χ₁ χ₂ : rationalCharacters P)
    (h₁ : ∀ q : AdelicGroupPoints F P,
      (adelicMatrix F G ρ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₁ =
        (character F P χ₁.toMul q).val • PrimitiveAdelicHeight.rational F d v₁)
    (h₂ : ∀ q : AdelicGroupPoints F P,
      ((adelicMatrix F G ρ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₂) j =
        (character F P χ₂.toMul q).val) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : AdelicGroupPoints F G,
      (adelicMatrix F G ρ x⁻¹).val *ᵥ PrimitiveAdelicHeight.rational F d v₁ =
        (adelicMatrix F G ρ y⁻¹).val *ᵥ PrimitiveAdelicHeight.rational F d v₂ →
      hK.height x χ₁ ≤ hK.height y χ₂ + B := by
  obtain ⟨b, hb, hdist⟩ :=
    exists_pos_orbitHeight_bounds_of_isCompact F G ρ (Nat.zero_lt_of_lt j.isLt) hK.isCompact
  let M := b * (b * orbitHeight F G ρ v₁ 1)
  have hM : 0 < M := mul_pos hb (mul_pos hb (orbitHeight_pos F G ρ hv₁ 1))
  refine ⟨max (Real.log M) 0, le_max_right _ _, fun x y heq => ?_⟩
  obtain ⟨q₁, k₁, hk₁, hx⟩ := hK.exists_eq x
  obtain ⟨q₂, k₂, hk₂, hy⟩ := hK.exists_eq y
  have hx' : x⁻¹ = k₁⁻¹ * map F P G p q₁⁻¹ := by rw [← hx, mul_inv_rev, map_inv]
  have hy' : y⁻¹ = k₂⁻¹ * map F P G p q₂⁻¹ := by rw [← hy, mul_inv_rev, map_inv]
  have horbit : orbitHeight F G ρ v₁ x⁻¹ = orbitHeight F G ρ v₂ y⁻¹ :=
    congrArg (PrimitiveAdelicHeight.height F d) heq
  have h1 :
      orbitHeight F G ρ v₁ x⁻¹ ≤
        Real.exp (-hK.height x χ₁) * (b * orbitHeight F G ρ v₁ 1) := by
    rw [hx', orbitHeight_mul_eq_of_idele_scalar F G ρ v₁ hv₁ _ _ _ (h₁ q₁⁻¹)]
    change ((characterNorm F P χ₁.toMul q₁⁻¹ : ℝ≥0) : ℝ) * orbitHeight F G ρ v₁ k₁⁻¹ ≤ _
    rw [characterNorm_exp_height hK χ₁ hk₁ hx]
    exact mul_le_mul_of_nonneg_left (by
      simpa only [mul_one] using (hdist k₁⁻¹ (K.inv_mem hk₁) 1 v₁ hv₁).1)
      (Real.exp_nonneg _)
  let z := (adelicMatrix F G ρ (map F P G p q₂⁻¹)).val *ᵥ PrimitiveAdelicHeight.rational F d v₂
  have hz : PrimitiveAdelicHeight.IsPrimitive F d z := ⟨_, v₂, hv₂, rfl⟩
  have hcoord := ideleNorm_le_primitiveHeight hz j (character F P χ₂.toMul q₂⁻¹) (h₂ q₂⁻¹).symm
  change ((characterNorm F P χ₂.toMul q₂⁻¹ : ℝ≥0) : ℝ) ≤
    orbitHeight F G ρ v₂ (map F P G p q₂⁻¹) at hcoord
  rw [characterNorm_exp_height hK χ₂ hk₂ hy] at hcoord
  have h2 : orbitHeight F G ρ v₂ (map F P G p q₂⁻¹) ≤ b * orbitHeight F G ρ v₂ y⁻¹ := by
    rw [hy']
    exact (hdist k₂⁻¹ (K.inv_mem hk₂) (map F P G p q₂⁻¹) v₂ hv₂).2
  have hcmp : Real.exp (-hK.height y χ₂) ≤ M * Real.exp (-hK.height x χ₁) := by
    calc
      _ ≤ _ := hcoord.trans h2
      _ ≤ b * (Real.exp (-hK.height x χ₁) * (b * orbitHeight F G ρ v₁ 1)) := by
        rw [← horbit]
        exact mul_le_mul_of_nonneg_left h1 hb.le
      _ = _ := by unfold M; ring
  have hlog := Real.log_le_log (Real.exp_pos _) hcmp
  rw [Real.log_exp, Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hle := le_max_left (Real.log M) 0
  linarith

end CompactComparison

/-- The cocharacter limit retains the diagonal entry at the chosen coordinate. -/
private theorem affineMatrix_diagonal_entry_of_hasLimit
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {d : ℕ}
    {ρ : MatrixRepresentation G (Fin d)} {c : (Gm (Spec R)).toGrp ⟶ G}
    {e : Fin d → ℤ} (hdiag : c ≫ ρ = GeneralLinear.diagonalCocharacter (Fin d) R e)
    {A : CommAlgCat R} {g m : G.affinePoints A} (h : Dynamic.HasLimit c g m) (j : Fin d) :
    (ρ.affineMatrix A g).val j j = (ρ.affineMatrix A m).val j j := by
  have h' := h.comp_hom c ρ
  rw [hdiag] at h'
  obtain ⟨_, hblock⟩ := (GeneralLinear.hasLimit_diagonalCocharacter_iff e).mp h'
  have heq := congrArg (fun M => M.val j j) hblock
  change (ρ.pointMatrix _ m).val j j =
    (GeneralLinear.blockDiagonalPart _ e (ρ.pointMatrix _ g).val) j j at heq
  rw [GeneralLinear.blockDiagonalPart_apply, ite_eq_left rfl, ρ.pointMatrix_eq_affineMatrix,
    ρ.pointMatrix_eq_affineMatrix] at heq
  exact (Corepresented.affineSectionsAlgEquiv A).symm.injective heq.symm

/-- Compare the two actual orbit heights using a rational line, its inverse-conjugate
representation and the limit retraction on the parabolic. -/
private theorem heightComparison_of_transported_line
    {F : Type u} [Field F] [NumberField F]
    {G P L U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : L ⟶ G}
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (uP : U ⟶ P) (hU : IsUnipotent U)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (lim : P ⟶ L) (f : L ⟶ P) (hf : f ≫ p = l ≫ (G.innerIso n⁻¹).hom)
    (hlimit : ∀ q : AdelicGroupPoints F P,
      Dynamic.HasLimit c (map F P G p q) (map F L G l (map F P L lim q)))
    {d : ℕ} (σ : MatrixRepresentation G (Fin d)) (a : Fin d) {e : Fin d → ℤ}
    (hd : c ≫ σ.restrict (G.innerIso n⁻¹).hom = GeneralLinear.diagonalCocharacter (Fin d)
      (CommRingCat.of F) e)
    (hσP : (σ.restrict p).PreservesCoordinateLine a) (χ₁ : rationalCharacters P)
    (hχ₁ : (σ.restrict p).coordinateLineCharacter a hσP = χ₁.toMul) :
    let χ₂ := characterRestrict (lim ≫ f) χ₁
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : AdelicGroupPoints F U) (x : AdelicGroupPoints F G),
      hK.height x χ₁ ≤ hK.height (innerAdelicPoint F G n * map F P G p (map F U P uP u) * x) χ₂ + C := by
  classical
  let A := CommAlgCat.of F (Adeles F)
  let w := innerAdelicPoint F G n
  let conjInv := (G.innerIso n⁻¹).hom
  let τ := σ.restrict conjInv
  let χ₂ := characterRestrict (lim ≫ f) χ₁
  let v₂ : Fin d → F := Pi.single a 1
  have hv₂ : v₂ ≠ 0 := by
    intro hz
    simpa [v₂] using congrFun hz a
  have hrat : PrimitiveAdelicHeight.rational F d v₂ = (Pi.single a 1 : Fin d → Adeles F) := by
    ext b
    by_cases hb : b = a <;> simp [PrimitiveAdelicHeight.rational, v₂, hb]
  let wRat : RationalGroupPoints F G := G.constantPoint n
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))
  let v₁ := (rationalMatrix F G τ wRat⁻¹).val *ᵥ v₂
  have hv₁ : v₁ ≠ 0 := PrimitiveAdelicHeight.rational_mulVec_ne_zero F d _ hv₂
  have hvec : PrimitiveAdelicHeight.rational F d v₁ =
      (adelicMatrix F G τ w⁻¹).val *ᵥ PrimitiveAdelicHeight.rational F d v₂ := by
    rw [PrimitiveAdelicHeight.rational_mulVec, ← adelicMatrix_rational, map_inv]
    rw [show rational F G wRat = w from (innerAdelicPoint_eq_rational F G n).symm]
  have hconj (g : AdelicGroupPoints F G) :
      adelicMatrix F G τ g = adelicMatrix F G σ (w⁻¹ * g * w) := by
    change τ.affineMatrix A g = σ.affineMatrix A (w⁻¹ * g * w)
    rw [MatrixRepresentation.affineMatrix_restrict]
    change σ.affineMatrix A (g ≫ (G.innerIso n⁻¹).hom.hom.hom) = _
    rw [comp_innerIso_hom, constantPoint_inv, inv_inv]
  have heigen (q : AdelicGroupPoints F P) :
      (adelicMatrix F G σ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₂ =
        (character F P χ₁.toMul q).val • PrimitiveAdelicHeight.rational F d v₂ := by
    rw [hrat]
    have he := (σ.restrict p).affine_coordinateLineCharacter_action a hσP A q
    rw [hχ₁] at he
    exact he
  have hfirst (q : AdelicGroupPoints F P) :
      (adelicMatrix F G τ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₁ =
        (character F P χ₁.toMul q).val • PrimitiveAdelicHeight.rational F d v₁ := by
    have hw : w⁻¹ * w⁻¹ * w = w⁻¹ := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have hmatrix : adelicMatrix F G τ (map F P G p q) * adelicMatrix F G τ w⁻¹ =
        adelicMatrix F G τ w⁻¹ * adelicMatrix F G σ (map F P G p q) := by
      rw [hconj (map F P G p q), hconj w⁻¹, hw, ← map_mul, ← map_mul,
        mul_assoc, mul_inv_cancel, mul_one]
    rw [hvec, Matrix.mulVec_mulVec, ← Units.val_mul, hmatrix, Units.val_mul,
      ← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul]
  have hsecond (q : AdelicGroupPoints F P) :
      ((adelicMatrix F G τ (map F P G p q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₂) a =
        (character F P χ₂.toMul q).val := by
    let m := map F P L lim q
    have hentry := affineMatrix_diagonal_entry_of_hasLimit (ρ := τ) hd (A := A) (hlimit q) a
    change (adelicMatrix F G τ (map F P G p q)).val a a =
      (adelicMatrix F G τ (map F L G l m)).val a a at hentry
    have hm : adelicMatrix F G τ (map F L G l m) =
        adelicMatrix F G σ (map F P G p (map F L P f m)) := by
      change adelicMatrix F G σ (map F G G conjInv (map F L G l m)) = _
      rw [← map_comp_apply_of_hom (p := (G.innerIso n⁻¹).hom) l m, ← hf, map_comp_apply_of_hom]
    have hval : character F P χ₂.toMul q = character F P χ₁.toMul (map F L P f m) := by
      change characterUnits F P ((lim ≫ f) ≫ χ₁.toMul) A q = _
      rw [characterUnits_comp]
      change character F P χ₁.toMul (map F P P (lim ≫ f) q) = _
      rw [map_comp_apply_of_hom]
    have he := congrFun (heigen (map F L P f m)) a
    rw [hrat, Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, mul_one] at he
    rw [hrat, Matrix.mulVec_single_one, Matrix.col_apply, hentry, hm, he, hval]
  obtain ⟨C, hC, hbound⟩ := exists_heightCharacter_le_add_of_orbit_eq hK τ hv₁ hv₂ a
    χ₁ χ₂ hfirst hsecond
  refine ⟨C, hC, fun u x => ?_⟩
  let v := map F P G p (map F U P uP u)
  refine hbound x (w * v * x) ?_
  have heval (u' : AdelicGroupPoints F U) : character F P χ₁.toMul (map F U P uP u') = 1 := by
    change characterUnits F P χ₁.toMul A (U.affinePointsTarget uP A u') = 1
    rw [← characterUnits_comp F U P uP,
      ← show (characterRestrict uP χ₁).toMul = uP ≫ χ₁.toMul from rfl,
      hU.rationalCharacter_eq_zero (characterRestrict uP χ₁), characterUnits_zero]
  have hvfix : (adelicMatrix F G τ v⁻¹).val *ᵥ PrimitiveAdelicHeight.rational F d v₁ =
      PrimitiveAdelicHeight.rational F d v₁ := by
    dsimp only [v]
    rw [← map_inv, ← map_inv, hfirst, heval, Units.val_one, one_smul]
  symm
  rw [mul_inv_rev, mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← hvec, hvfix]

section MinimalParabolic

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}

local notation "P" => Standard.parabolicScheme i ν ∅
local notation "L" => Standard.leviScheme i ν ∅
local notation "U" => Standard.unipotentScheme i ν ∅
local notation "p₀" => Standard.parabolicHom i ν ∅
local notation "l₀" => Standard.leviHom i ν ∅
local notation "uP" => Standard.unipotentToParabolic i ν ∅
local notation "uG" => Standard.unipotentHom i ν ∅
local notation "tP" => torusToParabolic F i ν ∅

omit [NumberField F] [Mono i.hom.hom.left] in
private theorem isUnipotent_emptyStandard (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) : IsUnipotent U := by
  let : Smooth G.X.hom := hG.smooth
  apply Dynamic.isUnipotent_unipotentRepresentative (CommGroupScheme.groupHom ν ≫ i) (j := uG)
  rw [← standardUnipotent_empty_eq_dynamic i ν hG hi]
  exact Standard.isRepresentedBy_unipotentHom i ν ∅

omit [NumberField F] [Mono i.hom.hom.left] in
/-- The minimal-parabolic limit followed by inverse Weyl conjugation acts by
the inverse torus automorphism on the embedded split torus. -/
private theorem exists_minimalLevi_limit_conjugate (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (n : normalizerPoints i) :
    let c := CommGroupScheme.groupHom ν ≫ i
    let conjInv := (G.innerIso n.val⁻¹).hom
    ∃ (lim : P ⟶ L) (f : L ⟶ P),
      f ≫ p₀ = l₀ ≫ conjInv ∧
      tP ≫ lim ≫ f = CommGroupScheme.groupHom (normalizingAut i n).inv ≫ tP ∧
      ∀ {Z : Over (Spec (CommRingCat.of F))} (q : Z ⟶ (P).X),
        Dynamic.HasLimit c (q ≫ (p₀).hom.hom) ((q ≫ lim.hom.hom) ≫ (l₀).hom.hom) := by
  let c := CommGroupScheme.groupHom ν ≫ i
  let conjInv := (G.innerIso n.val⁻¹).hom
  let tInv := CommGroupScheme.groupHom (normalizingAut i n).inv
  have hconjInvT : i ≫ conjInv = tInv ≫ i := (isNormalizingPoint_normalizingAut i n).inv
  have hP := Standard.isRepresentedBy_parabolicHom i ν ∅
  have hL := Standard.isRepresentedBy_leviHom i ν ∅
  have hPD : (Dynamic.parabolic c).IsRepresentedBy p₀ :=
    (standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν) ▸ hP
  have hLD : (Dynamic.centralizer c).IsRepresentedBy l₀ :=
    (standardLevi_empty_eq_dynamic_of_generic i ν hG hi hν) ▸ hL
  let lim := Dynamic.limitGroupHom hPD hLD
  have hrange : SubgroupFunctor.range (l₀ ≫ conjInv) ≤ standardParabolic i ν ∅ := by
    intro Z z hz
    obtain ⟨m, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    apply standardLevi_le_standardParabolic i ν ∅ Z
    rw [standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν]
    have hm : m ≫ (l₀).hom.hom ∈ (standardLevi i ν ∅).carrier Z :=
      (hL.pointsEquiv Z m).property
    rw [standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν] at hm
    rw [← torusCentralizer_comap_innerIso_normalizer i n⁻¹, SubgroupFunctor.mem_comap] at hm
    change m ≫ (l₀ ≫ conjInv).hom.hom ∈ (torusCentralizer i).carrier Z
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hm
  let f := hP.factorHom (l₀ ≫ conjInv) hrange
  have hf : f ≫ p₀ = l₀ ≫ conjInv := hP.factorHom_comp _ _
  refine ⟨lim, f, hf, ?_, fun q => ?_⟩
  · let tL := standardLeviTorusFactor i ν ∅ hL
    have htL : tL ≫ l₀ = i := standardLeviTorusFactor_comp i ν ∅ hL
    have htP : tP ≫ p₀ = i := torusToParabolic_comp F i ν ∅
    have htor : tL ≫ Dynamic.centralizerToParabolic hPD hLD = tP := by
      apply hP.hom_ext
      rw [Category.assoc, Dynamic.centralizerToParabolic_comp, htL, htP]
    have hlimitT : tP ≫ lim = tL := by
      rw [← htor, Category.assoc, Dynamic.centralizerToParabolic_comp_limitGroupHom,
        Category.comp_id]
    rw [← Category.assoc, hlimitT]
    apply hP.hom_ext
    rw [Category.assoc, hf, ← Category.assoc tL l₀ conjInv, htL,
      Category.assoc, htP, hconjInvT]
  · change Dynamic.HasLimit c (q ≫ (p₀).hom.hom) ((q ≫ lim.hom.hom) ≫ (l₀).hom.hom)
    rw [Dynamic.limitGroupHom_comp]
    exact Dynamic.hasLimit_limit c (hPD.pointsEquiv _ q)

omit [NumberField F] [Mono i.hom.hom.left] in
/-- Change the rational basis so that the line is still a coordinate line and
the cocharacter conjugated by the inverse lift acts diagonally. -/
private theorem exists_diagonal_basis_for_weyl_translate
    {d : ℕ} (ρ : MatrixRepresentation G (Fin d)) (j : Fin d)
    (hPline : (ρ.restrict p₀).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j) (n : normalizerPoints i) :
    ∃ (σ : MatrixRepresentation G (Fin d)) (a : Fin d) (e : Fin d → ℤ)
      (hσP : (σ.restrict p₀).PreservesCoordinateLine a),
      (CommGroupScheme.groupHom ν ≫ i) ≫ σ.restrict (G.innerIso n.val⁻¹).hom =
        GeneralLinear.diagonalCocharacter (Fin d) (CommRingCat.of F) e ∧
      (σ.restrict p₀).coordinateLineCharacter a hσP =
        (ρ.restrict p₀).coordinateLineCharacter j hPline := by
  let c := CommGroupScheme.groupHom ν ≫ i
  let conjInv := (G.innerIso n.val⁻¹).hom
  let tInv := CommGroupScheme.groupHom (normalizingAut i n).inv
  have hconjInvT : i ≫ conjInv = tInv ≫ i := (isNormalizingPoint_normalizingAut i n).inv
  have hcline : (ρ.restrict (c ≫ conjInv)).PreservesCoordinateLine j := by
    rw [show c ≫ conjInv = (CommGroupScheme.groupHom ν ≫ tInv) ≫ i by
      dsimp only [c]
      rw [Category.assoc, hconjInvT, ← Category.assoc]]
    exact ρ.preservesCoordinateLine_restrict_comp i _ j hTline
  obtain ⟨B, e, a, hB, -, hdiag⟩ :=
    (ρ.restrict (c ≫ conjInv)).exists_diagonalization_retaining_coordinateLine j hcline
  let σ := ρ.basisConjugate B
  have hσP : (σ.restrict p₀).PreservesCoordinateLine a :=
    ((ρ.restrict p₀).basisConjugate_preservesCoordinateLine_iff B a j hB).mpr hPline
  refine ⟨σ, a, e, hσP, ?_,
    (ρ.restrict p₀).basisConjugate_coordinateLineCharacter B a j hB hPline hσP
    ⟩
  simpa only [c, σ, MatrixRepresentation.restrict, MatrixRepresentation.basisConjugate,
    MatrixRepresentation.conjugate, Category.assoc] using hdiag

/-- Transport a parabolic line to the Weyl translate. The original and translated
vectors give the same inverse orbit at the two points in the height inequality. -/
private theorem weyl_line_heightComparison (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (hK : IsIwasawaCompact p₀ K)
    {d : ℕ} (ρ : MatrixRepresentation G (Fin d)) (j : Fin d)
    (hPline : (ρ.restrict p₀).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j) (n : normalizerPoints i) :
    let χ₁ := (ρ.restrict p₀).coordinateLineRationalCharacter j hPline
    ∃ χ₂ : rationalCharacters P,
      torusCharacterRestrict tP χ₂ = weylAction i n (torusCharacterRestrict tP χ₁) ∧
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range uG))
          (x : AdelicGroupPoints F G),
          hK.height x χ₁ ≤ hK.height (innerAdelicPoint F G n.val * v.val * x) χ₂ + B := by
  classical
  let c := CommGroupScheme.groupHom ν ≫ i
  let χ₁ := (ρ.restrict p₀).coordinateLineRationalCharacter j hPline
  obtain ⟨σ, a, e, hσP, hd, hχ₁⟩ := exists_diagonal_basis_for_weyl_translate ρ j hPline hTline n
  obtain ⟨lim, f, hf, htor, hlimit⟩ := exists_minimalLevi_limit_conjugate hG hi hν n
  let χ₂ := characterRestrict (lim ≫ f) χ₁
  have hχ₂ : torusCharacterRestrict tP χ₂ = weylAction i n (torusCharacterRestrict tP χ₁) := by
    rw [weylAction_apply]
    change Additive.ofMul ((tP ≫ lim ≫ f) ≫ χ₁.toMul) =
      Additive.ofMul ((CommGroupScheme.groupHom (normalizingAut i n).inv ≫ tP) ≫ χ₁.toMul)
    rw [htor]

  obtain ⟨C, hC, hbound⟩ := heightComparison_of_transported_line hK uP
    (isUnipotent_emptyStandard (ν := ν) hG hi) n.val c lim f hf (fun q => hlimit q)
    σ a hd hσP χ₁ hχ₁
  refine ⟨χ₂, hχ₂, C, hC, fun v x => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : AdelicGroupPoints F U, map F U G uG u = v.val := v.property
  rw [← hu, ← Standard.unipotentToParabolic_comp i ν ∅, map_comp_apply_of_hom]
  exact hbound u x

omit [NumberField F] in
/-- A dominant maximal-parabolic line character is a positive multiple of the
corresponding fundamental weight modulo restricted ambient characters. -/
private theorem lineCharacter_decomposition (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    (β : simpleRelativeRoots i ν) (ϖ : Vstar T) (hϖ : D.IsRealFundamentalWeight ν β ϖ)
    (ψ : characterLattice T)
    (hfixed : ∀ s ∈ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {β.val}),
      schemeWeylCharacterAction i s ψ = ψ)
    (hpositive : ∀ (f : characterLattice T →+ ℤ), f β.val = 2 →
      ∀ s ∈ standardRelativeWeylGroup i ν {β.val},
        (∀ χ, schemeWeylCharacterAction i s χ = χ - f χ • β.val) → 0 < f ψ) :
    ∃ d : ℝ, 0 < d ∧ ∃ ambient : ℝ ⊗[ℤ] rationalCharacters G,
      (1 : ℝ) ⊗ₜ[ℤ] ψ = d • ϖ + rationalCharacterRestrictReal i ambient := by
  let α (a : simpleRelativeRoots i ν) := simpleToRelativeRoot i ν a
  let f (a : simpleRelativeRoots i ν) := (latticePairing T).flip (D.coroot (α a))
  let s (a : simpleRelativeRoots i ν) : relativeWeylGroup i := QuotientGroup.mk (D.representative (α a))
  have htwo (a : simpleRelativeRoots i ν) : f a a.val = 2 := D.pair_self (α a)
  have hreflect (a : simpleRelativeRoots i ν) (χ : characterLattice T) :
      schemeWeylCharacterAction i (s a) χ = χ - f a χ • a.val := D.action (α a) χ
  have hW {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
      (a : simpleRelativeRoots i ν) (ha : a.val ∈ J) : s a ∈ standardRelativeWeylGroup i ν J := by
    rw [← standardRelativeWeylGeneration F G hG T i hi ν hν J hJ]
    exact Subgroup.subset_closure ⟨a.val, ha,
      D.isRelativeReflection_representative hi.isSplitSubtorus.1
        (ArthurRelative.finite_relativeRoots hG hi) (α a)⟩
  have hpos : 0 < f β ψ := hpositive (f β).toAddMonoidHom (htwo β) (s β)
    (hW (Set.singleton_subset_iff.mpr β.property) β (Set.mem_singleton _)) (hreflect β)
  have hvanish (a : simpleRelativeRoots i ν) (ha : a ≠ β) : f a ψ = 0 := by
    have hne : a.val ≠ β.val := fun h => ha (Subtype.ext h)
    have h := hfixed (s a) (hW Set.sdiff_subset a ⟨a.property, hne⟩)
    rw [hreflect] at h
    have he := congrArg (f a) h
    change f a (ψ - f a ψ • a.val) = f a ψ at he
    rw [map_sub, map_zsmul, htwo, smul_eq_mul] at he
    omega
  let d := (f β ψ : ℝ)
  have hd : 0 < d := by
    change (0 : ℝ) < (f β ψ : ℝ)
    exact_mod_cast hpos
  have hmem : (1 : ℝ) ⊗ₜ[ℤ] ψ - d • ϖ ∈ corootAnnihilator i D (simpleRelativeRoots i ν) := by
    rw [mem_corootAnnihilator]
    intro a ha
    let b : simpleRelativeRoots i ν := ⟨a.val, ha⟩
    change pair T ((1 : ℝ) ⊗ₜ[ℤ] ψ - d • ϖ) (D.realCoroot (α b)) = 0
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      RelativeRootReflectionData.pair_tmul_realCoroot, one_mul]
    change (f b ψ : ℝ) - d * pair T ϖ (D.realCoroot (α b)) = 0
    by_cases hb : b = β
    · rw [hb, hϖ.2.1, mul_one, sub_self]
    · rw [hvanish b hb, hϖ.2.2 b hb]
      simp
  rw [(standardLeviRealDecomposition F G hG T i hi ν hν D).1] at hmem
  obtain ⟨ambient, hambient⟩ := hmem
  exact ⟨d, hd, ambient, (sub_eq_iff_eq_add.mp hambient.symm).trans (add_comm _ _)⟩

variable (hi : IsMaximalSplitTorus i)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

omit [Mono i.hom.hom.left] in
private theorem pair_height_character (χ : rationalCharacters P) (g : AdelicGroupPoints F G) :
    pair T ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict tP χ) (height hi hK hρ g) = hK.height g χ := by
  change pair T (restrictToTorus F i ν ∅ ((1 : ℝ) ⊗ₜ[ℤ] χ))
    (toA0 hi.isSplitSubtorus.1 hρ (hK.height g)) = _
  simpa only [realParameterPairing_tmul, one_mul] using
    pair_toA0 hi.isSplitSubtorus.1 hρ (hK.height g) ((1 : ℝ) ⊗ₜ[ℤ] χ)

omit [Mono i.hom.hom.left] in
private theorem pair_height_ambient_character (χ : rationalCharacters G) (g : AdelicGroupPoints F G) :
    pair T ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i χ) (height hi hK hρ g) =
      characterLog F G g χ := by
  have hrestrict : torusCharacterRestrict tP (characterRestrict p₀ χ) = torusCharacterRestrict i χ := by
    change characterRestrict tP (characterRestrict p₀ χ) = characterRestrict i χ
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, torusToParabolic_comp]
  rw [← hrestrict, pair_height_character hi hK hρ]
  obtain ⟨q, k, hk, hqk⟩ := hK.exists_eq g
  rw [hK.height_eq hk hqk, ← hqk, characterLog_mul,
    characterLog_eq_zero_on_compactSubgroup F G K hK.isCompact hk, add_zero, characterLog_map]
  rfl

/-- The Weyl action fixes restricted ambient characters. Their Iwasawa pairings
agree at points with the same ambient logarithm. -/
private theorem pair_ambient_invariant (n : normalizerPoints i) (ambient : ℝ ⊗[ℤ] rationalCharacters G)
    (x y : AdelicGroupPoints F G) (hlog : characterLog F G y = characterLog F G x) :
    pair T (relativeWeylFullRealAction i (QuotientGroup.mk n : relativeWeylGroup i)
      (rationalCharacterRestrictReal i ambient)) (height hi hK hρ y) =
      pair T (rationalCharacterRestrictReal i ambient) (height hi hK hρ x) := by
  induction ambient using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul r χ =>
    change pair T (relativeWeylFullRealAction i (QuotientGroup.mk n : relativeWeylGroup i)
      (r ⊗ₜ[ℤ] torusCharacterRestrict i χ)) _ = pair T (r ⊗ₜ[ℤ] torusCharacterRestrict i χ) _
    rw [relativeWeylFullRealAction_tmul, relativeWeylLatticeAction_mk,
      weylAction_torusCharacterRestrict]
    rw [show (r ⊗ₜ[ℤ] torusCharacterRestrict i χ : Vstar T) =
        r • ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i χ) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simp only [map_smul, LinearMap.smul_apply, pair_height_ambient_character hi hK hρ, hlog]

end MinimalParabolic

/-- Arthur's Weyl displacement inequality with a uniform error for the specified
compact Iwasawa subgroup. -/
theorem weylHeightLowerBound : WeylHeightLowerBoundStatement.{u} := by
  classical
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ β ϖ hϖ n
  obtain ⟨d, j, ρ, hP, hT, hfixed, hpositive⟩ :=
    exists_maximalParabolic_dominant_line hG i hi ν hν β.val β.property
  let χ := (ρ.restrict (Standard.parabolicHom i ν ∅)).coordinateLineRationalCharacter j hP
  let ψ := ρ.torusCoordinateLineCharacter i j hT
  have hψ : ψ = torusCharacterRestrict (torusToParabolic F i ν ∅) χ :=
    ρ.torusCoordinateLineCharacter_eq_restrict i (Standard.parabolicHom i ν ∅)
      (torusToParabolic F i ν ∅) (torusToParabolic_comp F i ν ∅) j hT hP
  obtain ⟨a, ha, ambient, hdecomp⟩ := lineCharacter_decomposition hG hi hν D β ϖ hϖ ψ hfixed hpositive
  obtain ⟨χ', hχ', C, hC, hbound⟩ := weyl_line_heightComparison hG hi hν hK ρ j hP hT n
  refine ⟨C / a, div_nonneg hC ha.le, fun v x => ?_⟩
  let y := innerAdelicPoint F G n.val * v.val * x
  have hvlog : characterLog F G v.val = 0 := by
    obtain ⟨u, hu⟩ : ∃ u : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅),
        map F _ G (Standard.unipotentHom i ν ∅) u = v.val := v.property
    rw [← hu, characterLog_map, characterLog_eq_zero_of_isUnipotent
      (isUnipotent_emptyStandard (ν := ν) hG hi), map_zero]
  have hlog : characterLog F G y = characterLog F G x := by
    dsimp only [y]
    rw [characterLog_mul, characterLog_mul, innerAdelicPoint_eq_rational,
      characterLog_rational, hvlog, zero_add, zero_add]
  have hambient := pair_ambient_invariant hi hK hρ n ambient x y hlog
  have hcmp := hbound v x
  change hK.height x χ ≤ hK.height y χ' + C at hcmp
  rw [← pair_height_character hi hK hρ χ, ← pair_height_character hi hK hρ χ', hχ'] at hcmp
  change _ ≤ pair T ((1 : ℝ) ⊗ₜ[ℤ] relativeWeylLatticeAction i
    (QuotientGroup.mk n : relativeWeylGroup i) (torusCharacterRestrict (torusToParabolic F i ν ∅) χ))
    (height hi hK hρ y) + C at hcmp
  rw [← relativeWeylFullRealAction_tmul, ← hψ, hdecomp, map_add, map_smul] at hcmp
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hambient] at hcmp
  change pair T ϖ (height hi hK hρ x) ≤ pair T (relativeWeylFullRealAction i
    (QuotientGroup.mk n : relativeWeylGroup i) ϖ) (height hi hK hρ y) + C / a
  apply (mul_le_mul_iff_right₀ ha).mp
  rw [mul_add, mul_div_cancel₀ _ ha.ne']
  linarith

end Langlands.Global.ArthurTruncation
