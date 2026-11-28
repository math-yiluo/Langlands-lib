import Langlands.GroupScheme.SplitExistence.Opposite
import Langlands.GroupScheme.SplitExistence.RankOnePoints
import Langlands.GroupScheme.SplitExistence.WeylWords

/-! # Normalized root coordinates and Steinberg words on Chevalley rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

section SL2

variable {R : Type*} [CommRing R]

private def sl2SteinbergW (a : Rˣ) : SpecialLinearGroup (Fin 2) R :=
  sl2Upper (a : R) * sl2Lower (-((a⁻¹ : Rˣ) : R)) * sl2Upper (a : R)

private theorem sl2SteinbergW_eq (a : Rˣ) :
    sl2SteinbergW a = sl2Diag a * sl2Weyl := by
  simpa [sl2SteinbergW] using sl2Upper_mul_sl2Lower_mul_sl2Upper (-a⁻¹)

private theorem coe_sl2SteinbergW (a : Rˣ) :
    (sl2SteinbergW a : Matrix (Fin 2) (Fin 2) R) = !![0, (a : R); -((a⁻¹ : Rˣ) : R), 0] := by
  rw [sl2SteinbergW_eq]
  change !![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)] * !![0, 1; -1, 0] = _
  simp

private theorem sl2SteinbergW_mul_neg (a : Rˣ) : sl2SteinbergW a * sl2SteinbergW (-a) = 1 := by
  apply Subtype.ext
  change (sl2SteinbergW a : Matrix (Fin 2) (Fin 2) R) * (sl2SteinbergW (-a) : Matrix (Fin 2) (Fin 2) R) = 1
  rw [coe_sl2SteinbergW, coe_sl2SteinbergW, Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q <;> simp

private theorem sl2SteinbergW_one : sl2SteinbergW (1 : Rˣ) = sl2Weyl := by
  simpa [sl2SteinbergW] using (sl2Weyl_eq (R := R)).symm

private theorem sl2SteinbergW_mul_neg_one (a : Rˣ) :
    sl2SteinbergW a * sl2SteinbergW (-1) = sl2Diag a := by
  have h : sl2SteinbergW (-1 : Rˣ) = sl2Weyl⁻¹ := by
    rw [← sl2SteinbergW_one]
    exact (inv_eq_of_mul_eq_one_right (sl2SteinbergW_mul_neg (1 : Rˣ))).symm
  rw [h, sl2SteinbergW_eq, mul_inv_cancel_right]

private theorem sl2SteinbergW_mul_upper (a : Rˣ) (t : R) :
    sl2SteinbergW a * sl2Upper t =
      sl2Lower (-(((a⁻¹ : Rˣ) : R) ^ 2) * t) * sl2SteinbergW a := by
  let c := ((a⁻¹ : Rˣ) : R)
  have h : c * t = c ^ 2 * t * (a : R) := by
    calc
      _ = (c * (a : R)) * c * t := by rw [show c * (a : R) = 1 from a.inv_mul, one_mul]
      _ = _ := by ring
  apply Subtype.ext
  change (sl2SteinbergW a : Matrix (Fin 2) (Fin 2) R) * !![1, t; 0, 1] =
    !![1, 0; -c ^ 2 * t, 1] * (sl2SteinbergW a : Matrix (Fin 2) (Fin 2) R)
  simp only [coe_sl2SteinbergW, Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q <;> simp
  exact h

end SL2

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}

local notation "opp" => negIndex P

private def weylWordIndex : List b.support → J → J
  | [], j => j
  | i :: w, j => P.reflectionPerm i (weylWordIndex w j)

private theorem root_weylWordIndex (w : List b.support) (j : J) :
    P.root (weylWordIndex w j) = weylWord P b w (P.root j) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [weylWordIndex, RootPairing.root_reflectionPerm, weylWord_cons, ih]

private theorem weylWordIndex_opposite (w : List b.support) (j : J) :
    weylWordIndex w (opp j) = opp (weylWordIndex w j) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [weylWordIndex, weylWordIndex, ih]
    exact ChevalleyData.reflectionPerm_reflectionPerm_neg (P := P) i _

private structure RootTransport (j : J) where
  word : List b.support
  simple : b.support
  index_eq : weylWordIndex word simple = j

private theorem exists_rootTransport [Finite J] [P.IsReduced] (j : J) :
    Nonempty (RootTransport (b := b) j) := by
  obtain ⟨w, i, h⟩ := exists_weylWord_root (b := b) j
  exact ⟨⟨w, i, P.root.injective ((root_weylWordIndex w i).trans h.symm)⟩⟩

private def rootTransport [Finite J] [P.IsReduced] (j : J) : RootTransport (b := b) j := by
  classical
  exact if h : j ∈ b.support then ⟨[], ⟨j, h⟩, rfl⟩
    else Classical.choice (exists_rootTransport j)

private theorem rootTransport_word_simple [Finite J] [P.IsReduced] (i : b.support) :
    (rootTransport (b := b) i).word = [] := by
  classical
  simp only [rootTransport, dite_eq_left i.property]

private theorem isPos_opposite (j : J) : b.IsPos (opp j) ↔ ¬ b.IsPos j :=
  RootPairing.Base.IsPos.neg_iff_not b j

namespace ChevalleyData

variable (D : ChevalleyData P b)

private theorem exists_integralWeylSign (i : b.support) (j : J) :
    ∃ ε : ℤˣ, ∀ (R : Type u) [CommRing R] (t : R),
      D.φ i R sl2Weyl * D.x j t * (D.φ i R sl2Weyl)⁻¹ =
        D.x (P.reflectionPerm i j) (((ε : ℤ) : R) * t) := by
  obtain ⟨ε, hε, h⟩ := D.exists_weyl_conj_x i j
  rcases hε with rfl | rfl
  · exact ⟨1, h⟩
  · exact ⟨-1, h⟩

private def integralWeylSign (i : b.support) (j : J) : ℤˣ :=
  (D.exists_integralWeylSign i j).choose

private def weylWordSign : List b.support → J → ℤˣ
  | [], _ => 1
  | i :: w, j => D.integralWeylSign i (weylWordIndex w j) * weylWordSign w j

section FiniteReduced

variable [Finite J] [P.IsReduced]

/-- The integral coordinate sign of a root. Both signs in an opposite pair come from the word
chosen for its positive member. -/
def steinbergSign (j : J) : ℤˣ := by
  classical
  exact if b.IsPos j then
    let r := rootTransport (b := b) j
    D.weylWordSign r.word r.simple
  else
    let r := rootTransport (b := b) (opp j)
    D.weylWordSign r.word (opp r.simple)

theorem steinbergSign_simple (i : b.support) : D.steinbergSign i = 1 := by
  simp only [steinbergSign, ite_eq_left (b.isPos_of_mem_support i.property), rootTransport_word_simple,
    weylWordSign]

theorem steinbergSign_opposite_simple (i : b.support) : D.steinbergSign (opp i) = 1 := by
  have h : ¬ b.IsPos (opp i) := fun hi =>
    (isPos_opposite (b := b) i).mp hi (b.isPos_of_mem_support i.property)
  rw [steinbergSign, ite_eq_right h, negIndex_negIndex]
  simp only [rootTransport_word_simple, weylWordSign]

end FiniteReduced

variable {D} {k : Type u} [Field k]

namespace ChevGroup

variable (G : D.ChevGroup k)

local notation "S" => Spec (CommRingCat.of k)
local notation "U" => Over.mk (𝟙 S)

private def weylWordPoint (w : List b.support) : rationalPoints G.H :=
  (w.map G.weylPoint).prod

private theorem weylWordPoint_cons_conj (i : b.support) (w : List b.support)
    (x : rationalPoints G.H) :
    G.weylWordPoint (i :: w) * x * (G.weylWordPoint (i :: w))⁻¹ =
      G.weylPoint i * (G.weylWordPoint w * x * (G.weylWordPoint w)⁻¹) * (G.weylPoint i)⁻¹ := by
  simp [weylWordPoint, mul_assoc, _root_.mul_inv_rev]

private theorem weylPoint_conj_rootPt (i : b.support) (j : J) (t : k) :
    G.weylPoint i * G.rootPt j t * (G.weylPoint i)⁻¹ =
      G.rootPt (P.reflectionPerm i j) (((D.integralWeylSign i j : ℤ) : k) * t) := by
  apply G.mono_i.right_cancellation
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U).injective
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, map_mul, map_mul, map_inv,
    pointsEquiv_weylPoint, pointsEquiv_rootPt, pointsEquiv_rootPt,
    (D.exists_integralWeylSign i j).choose_spec, map_mul, map_intCast, integralWeylSign]

private theorem weylWordPoint_conj_rootPt (w : List b.support) (j : J) (t : k) :
    G.weylWordPoint w * G.rootPt j t * (G.weylWordPoint w)⁻¹ =
      G.rootPt (weylWordIndex w j) (((D.weylWordSign w j : ℤ) : k) * t) := by
  induction w with
  | nil => simp [weylWordPoint, weylWordIndex, weylWordSign]
  | cons i w ih =>
    rw [G.weylWordPoint_cons_conj, ih, G.weylPoint_conj_rootPt, weylWordIndex, weylWordSign]
    rw [Units.val_mul, Int.cast_mul, mul_assoc]

private theorem weylPoint_conj_corootPt (i : b.support) (j : J) (a : kˣ) :
    G.weylPoint i * G.corootPt j a * (G.weylPoint i)⁻¹ =
      G.corootPt (P.reflectionPerm i j) a := by
  let c := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom a
  let χ := corootCharRing (P := P) j c
  have h := (G.isNormalizingPoint_weylPoint i).conj_comp U ((torusPointsEquiv k U).symm χ)
  rw [constantPoint_self, groupHom_torusAut_hom] at h
  have hχ : (torusPointsEquiv k U).symm χ ≫
      (torusEnd k (P.reflection i).toAddEquiv.toAddMonoidHom).hom.hom =
      (torusPointsEquiv k U).symm (corootCharRing (P := P) (P.reflectionPerm i j) c) := by
    apply (torusPointsEquiv k U).injective
    simp only [torusPointsEquiv_torusEnd, MulEquiv.apply_symm_apply]
    apply MonoidHom.ext
    intro x
    exact congrArg (fun n : ℤ => c ^ n)
      (P.coroot'_reflection (i := i) (j := j) (Multiplicative.toAdd x))
  rw [hχ] at h
  exact h

private theorem weylWordPoint_conj_corootPt (w : List b.support) (j : J) (a : kˣ) :
    G.weylWordPoint w * G.corootPt j a * (G.weylWordPoint w)⁻¹ =
      G.corootPt (weylWordIndex w j) a := by
  induction w with
  | nil => simp [weylWordPoint, weylWordIndex]
  | cons i w ih =>
    rw [G.weylWordPoint_cons_conj, ih, G.weylPoint_conj_corootPt, weylWordIndex]

private theorem torusAut_trans (e d : X ≃+ X) :
    torusAut k e ≪≫ torusAut k d = torusAut k (d.trans e) := by
  apply Iso.ext
  change Additive.ofMul (torusEnd k e.toAddMonoidHom ≫ torusEnd k d.toAddMonoidHom) =
    Additive.ofMul (torusEnd k (d.trans e).toAddMonoidHom)
  rw [torusEnd_comp]
  rfl

private theorem isNormalizingPoint_weylWord_conj (w : List b.support) {n : rationalPoints G.H}
    {j : J} (hn : IsNormalizingPoint G.t n (torusAut k (P.reflection j).toAddEquiv)) :
    IsNormalizingPoint G.t (G.weylWordPoint w * n * (G.weylWordPoint w)⁻¹)
      (torusAut k (P.reflection (weylWordIndex w j)).toAddEquiv) := by
  induction w with
  | nil => simpa [weylWordPoint, weylWordIndex] using hn
  | cons i w ih =>
    rw [G.weylWordPoint_cons_conj, weylWordIndex]
    have hi := G.isNormalizingPoint_weylPoint i
    have h := (hi.mul ih).mul hi.inv
    have hsymm : (torusAut k (P.reflection i).toAddEquiv).symm =
        torusAut k (P.reflection i).toAddEquiv := Iso.ext rfl
    rw [hsymm, torusAut_trans, torusAut_trans] at h
    rw [RootPairing.reflection_reflectionPerm]
    exact h

variable [Finite J] [P.IsReduced]

private def transportedRankOne (j : J) : SpecialLinearGroup (Fin 2) k →* rationalPoints G.H :=
  let r := rootTransport (b := b) j
  (MulAut.conj (G.weylWordPoint r.word)).toMonoidHom.comp (G.simpleRankOne r.simple)

private theorem transportedRankOne_upper (j : J) (t : k) :
    G.transportedRankOne j (sl2Upper t) =
      let r := rootTransport (b := b) j
      G.rootPt j (((D.weylWordSign r.word r.simple : ℤ) : k) * t) := by
  simp only [transportedRankOne, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    simpleRankOne_upper, weylWordPoint_conj_rootPt, RootTransport.index_eq]

private theorem transportedRankOne_lower (j : J) (t : k) :
    G.transportedRankOne j (sl2Lower t) =
      let r := rootTransport (b := b) j
      G.rootPt (opp j) (((D.weylWordSign r.word (opp r.simple) : ℤ) : k) * t) := by
  simp only [transportedRankOne, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    simpleRankOne_lower, ← negIndex_apply, weylWordPoint_conj_rootPt, weylWordIndex_opposite,
    RootTransport.index_eq]

private theorem transportedRankOne_diag (j : J) (a : kˣ) :
    G.transportedRankOne j (sl2Diag a) = G.corootPt j a := by
  simp only [transportedRankOne, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    simpleRankOne_diag, weylWordPoint_conj_corootPt, RootTransport.index_eq]

private theorem isNormalizingPoint_transportedRankOne_weyl (j : J) :
    IsNormalizingPoint G.t (G.transportedRankOne j sl2Weyl)
      (torusAut k (P.reflection j).toAddEquiv) := by
  let r := rootTransport (b := b) j
  have h := G.isNormalizingPoint_weylWord_conj r.word (G.isNormalizingPoint_weylPoint r.simple)
  rw [r.index_eq] at h
  simpa only [transportedRankOne, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    simpleRankOne_weyl] using h

/-- The normalized homomorphism of the rank-one pair at `j`, with the upper matrix corresponding
to `j` and the lower matrix to `-j`. -/
def rootRankOne (j : J) : SpecialLinearGroup (Fin 2) k →* rationalPoints G.H := by
  classical
  exact if b.IsPos j then G.transportedRankOne j
    else (G.transportedRankOne (opp j)).comp sl2Swap

/-- Changing from the positive root to its opposite interchanges the two unipotent lines. -/
theorem rootRankOne_opposite_of_isPos {j : J} (hj : b.IsPos j) :
    G.rootRankOne (opp j) = (G.rootRankOne j).comp sl2Swap := by
  have h : ¬ b.IsPos (opp j) := fun h => (isPos_opposite (b := b) j).mp h hj
  rw [rootRankOne, ite_eq_right h, negIndex_negIndex, rootRankOne, ite_eq_left hj]

/-- The normalized root point of parameter `t` in the Chevalley group. -/
def steinbergX (j : J) (t : k) : rationalPoints G.H :=
  G.rootPt j (((D.steinbergSign j : ℤ) : k) * t)

theorem steinbergX_simple (i : b.support) (t : k) :
    G.steinbergX i t = G.rootPt i t := by
  simp [steinbergX, steinbergSign_simple]

theorem steinbergX_opposite_simple (i : b.support) (t : k) :
    G.steinbergX (opp i) t = G.rootPt (opp i) t := by
  simp only [steinbergX, steinbergSign_opposite_simple, Units.val_one, Int.cast_one, one_mul]

theorem steinbergX_zero (j : J) : G.steinbergX j 0 = 1 := by
  rw [steinbergX, mul_zero, rootPt_zero]

theorem steinbergX_add (j : J) (s t : k) :
    G.steinbergX j (s + t) = G.steinbergX j s * G.steinbergX j t := by
  unfold steinbergX rootPt
  rw [mul_add, ofAdd_add, map_mul, MonObj.mul_comp]

/-- The normalized field coordinates on the represented rational root subgroup. -/
def steinbergRootCoordEquiv [Module.Finite ℤ X] [Module.Free ℤ X]
    [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] (j : J) :
    Multiplicative k ≃* (RelativeRoot.subgroup G.t (charOf k (P.root j))).carrier U :=
  (AddEquiv.toMultiplicative
    (LinearEquiv.smulOfUnit (M := k) (signUnit (k := k) (D.steinbergSign j))).toAddEquiv).trans
      (G.rootCoordEquiv j)

theorem steinbergRootCoordEquiv_apply_coe [Module.Finite ℤ X] [Module.Free ℤ X]
    [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] (j : J) (t : k) :
    (G.steinbergRootCoordEquiv j (Multiplicative.ofAdd t) : rationalPoints G.H) =
      G.steinbergX j t := rfl

theorem rootRankOne_upper (j : J) (t : k) :
    G.rootRankOne j (sl2Upper t) = G.steinbergX j t := by
  classical
  by_cases h : b.IsPos j
  · rw [rootRankOne, ite_eq_left h, steinbergX, steinbergSign, ite_eq_left h, transportedRankOne_upper]
  · rw [rootRankOne, ite_eq_right h, MonoidHom.comp_apply, sl2Swap_upper, transportedRankOne_lower,
      negIndex_negIndex, steinbergX, steinbergSign, ite_eq_right h]

theorem rootRankOne_lower (j : J) (t : k) :
    G.rootRankOne j (sl2Lower t) = G.steinbergX (opp j) t := by
  classical
  by_cases h : b.IsPos j
  · have h' : ¬ b.IsPos (opp j) := fun hn => (isPos_opposite (b := b) j).mp hn h
    rw [rootRankOne, ite_eq_left h, steinbergX, steinbergSign, ite_eq_right h', negIndex_negIndex,
      transportedRankOne_lower]
  · have h' := (isPos_opposite (b := b) j).mpr h
    rw [rootRankOne, ite_eq_right h, MonoidHom.comp_apply, sl2Swap_lower, steinbergX, steinbergSign,
      ite_eq_left h', transportedRankOne_upper]

theorem rootRankOne_diag (j : J) (a : kˣ) :
    G.rootRankOne j (sl2Diag a) = G.corootPt j a := by
  classical
  by_cases h : b.IsPos j
  · rw [rootRankOne, ite_eq_left h, transportedRankOne_diag]
  · rw [rootRankOne, ite_eq_right h, MonoidHom.comp_apply, sl2Swap_diag, transportedRankOne_diag,
      negIndex_apply, corootPt_opposite, inv_inv]

theorem isNormalizingPoint_rootRankOne_weyl (j : J) :
    IsNormalizingPoint G.t (G.rootRankOne j sl2Weyl)
      (torusAut k (P.reflection j).toAddEquiv) := by
  classical
  by_cases h : b.IsPos j
  · rw [rootRankOne, ite_eq_left h]
    exact G.isNormalizingPoint_transportedRankOne_weyl j
  · rw [rootRankOne, ite_eq_right h, MonoidHom.comp_apply, sl2Swap_weyl, map_mul, transportedRankOne_diag]
    have hc : IsNormalizingPoint G.t (G.corootPt (opp j) (-1)) (Iso.refl _) :=
      G.corootPt_mem_centralizerPoints _ _
    have hn := (G.isNormalizingPoint_transportedRankOne_weyl (opp j)).mul hc
    rwa [Iso.refl_trans, negIndex_apply, reflection_negIndex] at hn

/-- The Weyl word `x_j(a) x_{-j}(-a⁻¹) x_j(a)`. -/
def steinbergW (j : J) (a : kˣ) : rationalPoints G.H :=
  G.steinbergX j (a : k) * G.steinbergX (opp j) (-((a⁻¹ : kˣ) : k)) * G.steinbergX j (a : k)

/-- The torus word `w_j(a) w_j(-1)`. -/
def steinbergH (j : J) (a : kˣ) : rationalPoints G.H :=
  G.steinbergW j a * G.steinbergW j (-1)

private theorem rootRankOne_sl2SteinbergW (j : J) (a : kˣ) :
    G.rootRankOne j (sl2SteinbergW a) = G.steinbergW j a := by
  simp only [sl2SteinbergW, map_mul, rootRankOne_upper, rootRankOne_lower, steinbergW]

theorem steinbergW_eq_rankOne (j : J) (a : kˣ) :
    G.steinbergW j a = G.rootRankOne j (sl2Diag a * sl2Weyl) :=
  (G.rootRankOne_sl2SteinbergW j a).symm.trans (congrArg (G.rootRankOne j) (sl2SteinbergW_eq a))

theorem steinbergW_inv (j : J) (a : kˣ) :
    (G.steinbergW j a)⁻¹ = G.steinbergW j (-a) := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [map_mul, map_one, rootRankOne_sl2SteinbergW] using
    congrArg (G.rootRankOne j) (sl2SteinbergW_mul_neg a)

theorem steinbergH_eq_corootPt (j : J) (a : kˣ) :
    G.steinbergH j a = G.corootPt j a := by
  simpa only [map_mul, rootRankOne_sl2SteinbergW, rootRankOne_diag, steinbergH] using
    congrArg (G.rootRankOne j) (sl2SteinbergW_mul_neg_one a)

theorem steinbergH_eq_eval [Module.Finite ℤ X] [Module.Free ℤ X] (j : J) (a : kˣ) :
    G.steinbergH j a = (Gm.affinePointsEquiv (𝟙 S)).symm a ≫
      (CommGroupScheme.groupHom ((chevDatum k P).coroot j)).hom.hom ≫ G.t.hom.hom :=
  (G.steinbergH_eq_corootPt j a).trans (G.corootPt_eq_eval j a)

theorem steinbergH_mul (j : J) (a c : kˣ) :
    G.steinbergH j (a * c) = G.steinbergH j a * G.steinbergH j c := by
  simp only [steinbergH_eq_corootPt, corootPt_mul]

/-- The rank-one Steinberg conjugation relation for the root defining the word. -/
theorem steinbergW_conj (j : J) (a : kˣ) (t : k) :
    G.steinbergW j a * G.steinbergX j t * G.steinbergW j (-a) =
      G.steinbergX (opp j) (-(((a⁻¹ : kˣ) : k) ^ 2) * t) := by
  have h := congrArg (G.rootRankOne j) (sl2SteinbergW_mul_upper a t)
  simp only [map_mul, rootRankOne_sl2SteinbergW, rootRankOne_upper, rootRankOne_lower] at h
  rw [h, ← G.steinbergW_inv j a, mul_inv_cancel_right]

/-- Each Weyl word induces the root reflection on the torus as a group scheme automorphism. -/
theorem isNormalizingPoint_steinbergW (j : J) (a : kˣ) :
    IsNormalizingPoint G.t (G.steinbergW j a) (torusAut k (P.reflection j).toAddEquiv) := by
  rw [steinbergW_eq_rankOne, map_mul, rootRankOne_diag]
  have hc : IsNormalizingPoint G.t (G.corootPt j a) (Iso.refl _) :=
    G.corootPt_mem_centralizerPoints j a
  simpa only [Iso.trans_refl] using hc.mul (G.isNormalizingPoint_rootRankOne_weyl j)

theorem steinbergW_mem_normalizerPoints (j : J) (a : kˣ) :
    G.steinbergW j a ∈ normalizerPoints G.t :=
  ⟨_, G.isNormalizingPoint_steinbergW j a⟩

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
