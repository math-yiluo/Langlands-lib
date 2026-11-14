import Langlands.GroupScheme.Reductive.SplitRankOneRootCellReduction
import Mathlib.Algebra.CharP.Frobenius

/-! # Characteristic powers on rank-one open cells -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootCell

variable {k : Type u} [Field k]

@[simp]
theorem pt_crd {Z : Over (Spec (CommRingCat.of k))} (a : Z ⟶ (Ga k).X) :
    pt (crd a) = a := crd_injective (crd_pt _)

@[simp]
theorem crd_mul {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ (Ga k).X) :
    crd (a * b) = crd a + crd b := by
  exact congrFun (VectorGroup.coordinates_mul a b) 0

@[simp]
theorem crd_one {Z : Over (Spec (CommRingCat.of k))} :
    crd (1 : Z ⟶ (Ga k).X) = 0 := by
  exact congrFun (congrArg Multiplicative.toAdd
    (map_one (VectorGroup.coordinates (CommRingCat.of k) 1 Z))) 0

/-- The scheme map on the additive line with coordinate `X ↦ X ^ q`. -/
def gaPower (q : ℕ) : (Ga k).X ⟶ (Ga k).X := pt (crd (𝟙 (Ga k).X) ^ q)

@[simp]
theorem crd_comp_gaPower (q : ℕ) {Z : Over (Spec (CommRingCat.of k))}
    (a : Z ⟶ (Ga k).X) : crd (a ≫ gaPower q) = crd a ^ q := by
  change (VectorGroup.coordinates _ _ _ _).toAdd 0 = _
  rw [VectorGroup.coordinates_comp]
  change a.left.appTop (crd (gaPower q)) = _
  rw [gaPower, crd_pt, map_pow]
  congr 1

@[simp]
theorem comp_gaPower (q : ℕ) {Z : Over (Spec (CommRingCat.of k))}
    (a : Z ⟶ (Ga k).X) : a ≫ gaPower q = pt (crd a ^ q) := by
  apply crd_injective
  rw [crd_comp_gaPower, crd_pt]

/-- Characteristic-power additivity holds even for tests with the zero ring of sections. -/
theorem add_pow_sections (p e : ℕ) [ExpChar k p]
    (Z : Over (Spec (CommRingCat.of k))) (a b : Γ(Z.left, ⊤)) :
    (a + b) ^ p ^ e = a ^ p ^ e + b ^ p ^ e := by
  let : Algebra k Γ(Z.left, ⊤) := ((algΓ (CommRingCat.of k)).obj Z).unop.algebra
  rcases subsingleton_or_nontrivial Γ(Z.left, ⊤) with h | h
  · exact Subsingleton.elim _ _
  · have : ExpChar Γ(Z.left, ⊤) p :=
      expChar_of_injective_algebraMap (algebraMap k Γ(Z.left, ⊤)).injective p
    exact add_pow_expChar_pow a b p e

/-- On all test schemes the additive-line power map respects addition. -/
theorem gaPower_mul (p e : ℕ) [ExpChar k p]
    {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ (Ga k).X) :
    (a * b) ≫ gaPower (p ^ e) = (a ≫ gaPower (p ^ e)) * (b ≫ gaPower (p ^ e)) := by
  apply crd_injective
  simp only [crd_comp_gaPower, crd_mul]
  exact add_pow_sections p e Z _ _

@[simp]
theorem gaPower_one (p e : ℕ) [ExpChar k p]
    (Z : Over (Spec (CommRingCat.of k))) :
    (1 : Z ⟶ (Ga k).X) ≫ gaPower (p ^ e) = 1 := by
  apply crd_injective
  simp only [crd_comp_gaPower, crd_one, zero_pow (pow_ne_zero e (expChar_ne_zero k p))]

variable {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Evaluation of a natural multiple of a character is an ordinary power. -/
theorem charValue_nsmul (χ : characterLattice T) (q : ℕ)
    {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ T.X) :
    VectorGroup.charValue (q • χ) Z t = VectorGroup.charValue χ Z t ^ q := by
  rw [VectorGroup.charValue, VectorGroup.charValue, ← Nat.cast_smul_eq_nsmul ℤ,
    comp_groupHom_zsmul, map_zpow, zpow_natCast, Units.val_pow_eq_pow_val]

/-- Pulling back the target root through the torus map gives the powered source weight. -/
theorem charValue_comp_of_root (t : T ⟶ T') (χ : characterLattice T)
    (χ' : characterLattice T') (q : ℕ) (hχ : t ≫ χ' = q • χ)
    {Z : Over (Spec (CommRingCat.of k))} (s : Z ⟶ T.X) :
    VectorGroup.charValue χ' Z (s ≫ (CommGroupScheme.groupHom t).hom.hom) =
      VectorGroup.charValue χ Z s ^ q := by
  rw [VectorGroup.charValue, ← comp_groupHom_comp, hχ]
  exact charValue_nsmul χ q s

/-- Powers intertwine the two torus actions when their characters satisfy the root equation. -/
theorem gaPower_weight (t : T ⟶ T') (χ : characterLattice T)
    (χ' : characterLattice T') (q : ℕ) (hχ : t ≫ χ' = q • χ)
    {Z : Over (Spec (CommRingCat.of k))} (s : Z ⟶ T.X) (a : Z ⟶ (Ga k).X) :
    VectorGroup.weightPointAction χ Z s a ≫ gaPower q =
      VectorGroup.weightPointAction χ' Z (s ≫ (CommGroupScheme.groupHom t).hom.hom)
        (a ≫ gaPower q) := by
  apply crd_injective
  simp only [crd_comp_gaPower, crd, VectorGroup.coordinates_weightPointAction,
    Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [charValue_comp_of_root t χ χ' q hχ]

/-- The coordinatewise power map with its prescribed torus component. -/
def powerCell (t : T ⟶ T') (q : ℕ) : Cell T ⟶ Cell T' :=
  lift (fst _ _ ≫ gaPower q)
    (lift (snd _ _ ≫ fst _ _ ≫ (CommGroupScheme.groupHom t).hom.hom)
      (snd _ _ ≫ snd _ _ ≫ gaPower q))

@[simp]
theorem lift_powerCell (t : T ⟶ T') (q : ℕ)
    {Z : Over (Spec (CommRingCat.of k))} (m p : Z ⟶ (Ga k).X) (s : Z ⟶ T.X) :
    lift m (lift s p) ≫ powerCell t q =
      lift (m ≫ gaPower q) (lift (s ≫ (CommGroupScheme.groupHom t).hom.hom)
        (p ≫ gaPower q)) := by
  simp only [powerCell, comp_lift, lift_fst_assoc, lift_snd_assoc]

/-- The cocharacter equation sends the source torus factor to the powered target factor. -/
theorem coU_comp_of_coroot (t : T ⟶ T') (χv : cocharacterLattice T)
    (χv' : cocharacterLattice T') (q : ℕ) (hχv : χv ≫ t = q • χv')
    {Z : Over (Spec (CommRingCat.of k))} (u : Γ(Z.left, ⊤)ˣ) :
    coU χv u ≫ (CommGroupScheme.groupHom t).hom.hom = coU χv' (u ^ q) := by
  rw [coU, ← comp_groupHom_comp, hχv, ← Nat.cast_smul_eq_nsmul ℤ,
    comp_groupHom_zsmul, zpow_natCast, ← MonObj.pow_comp, ← map_pow]
  rfl

/-- The reciprocal unit appearing in the rank-one relation is preserved by powers. -/
theorem pt_unit_mul_comp_gaPower (q : ℕ) {Z : Over (Spec (CommRingCat.of k))}
    (u : Γ(Z.left, ⊤)ˣ) (a : Z ⟶ (Ga k).X) :
    pt ((↑u⁻¹ : Γ(Z.left, ⊤)) * crd a) ≫ gaPower q =
      pt ((↑(u ^ q)⁻¹ : Γ(Z.left, ⊤)) * crd (a ≫ gaPower q)) := by
  apply crd_injective
  simp only [crd_comp_gaPower, crd_pt, mul_pow, Units.inv_pow_eq_pow_inv]

/-- Characteristic powers preserve the unit equation in the rank-one relation. -/
theorem pow_unit_eq (p e : ℕ) [ExpChar k p]
    {Z : Over (Spec (CommRingCat.of k))} (u : Γ(Z.left, ⊤)ˣ)
    (a b : Z ⟶ (Ga k).X) (hu : (u : Γ(Z.left, ⊤)) = 1 + crd a * crd b) :
    (↑(u ^ p ^ e) : Γ(Z.left, ⊤)) =
      1 + crd (a ≫ gaPower (p ^ e)) * crd (b ≫ gaPower (p ^ e)) := by
  rw [Units.val_pow_eq_pow_val, hu, add_pow_sections p e Z]
  simp only [one_pow, mul_pow, crd_comp_gaPower]

/-- The coordinatewise power map intertwines the two rank-one multiplication formulas. -/
theorem cellProd_powerCell (t : T ⟶ T') (χ : characterLattice T)
    (χv : cocharacterLattice T) (χ' : characterLattice T') (χv' : cocharacterLattice T')
    (p e : ℕ) [ExpChar k p] (hχ : t ≫ χ' = p ^ e • χ)
    (hχv : χv ≫ t = p ^ e • χv')
    {Z : Over (Spec (CommRingCat.of k))} (m a m' a' : Z ⟶ (Ga k).X)
    (s s' : Z ⟶ T.X) (u : Γ(Z.left, ⊤)ˣ) :
    cellProd χ χv m a m' a' s s' u ≫ powerCell t (p ^ e) =
      cellProd χ' χv' (m ≫ gaPower (p ^ e)) (a ≫ gaPower (p ^ e))
        (m' ≫ gaPower (p ^ e)) (a' ≫ gaPower (p ^ e))
        (s ≫ (CommGroupScheme.groupHom t).hom.hom)
        (s' ≫ (CommGroupScheme.groupHom t).hom.hom) (u ^ p ^ e) := by
  have hχneg : t ≫ (-χ') = p ^ e • (-χ) := by
    rw [Preadditive.comp_neg, hχ, smul_neg]
  simp only [cellProd, lift_powerCell, gaPower_mul p e,
    gaPower_weight t χ χ' (p ^ e) hχ,
    gaPower_weight t (-χ) (-χ') (p ^ e) hχneg, pt_unit_mul_comp_gaPower,
    MonObj.mul_comp, GrpObj.inv_comp, coU_comp_of_coroot t χv χv' (p ^ e) hχv]

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    {χ : characterLattice T} {χv : cocharacterLattice T}
    {χ' : characterLattice T'} {χv' : cocharacterLattice T'}
    {xp xm : Ga k ⟶ G} {xp' xm' : Ga k ⟶ G'}

/-- A source cell relation remains valid after applying a characteristic-power cell map. -/
theorem powerCell_compatible (D : IsRootCell i χ χv xp xm)
    (D' : IsRootCell i' χ' χv' xp' xm') (t : T ⟶ T')
    (p e : ℕ) [ExpChar k p] (hχ : t ≫ χ' = p ^ e • χ)
    (hχv : χv ≫ t = p ^ e • χv') :
    haveI := D.isOpenImmersion
    CellGluing.CellCompatible (Dynamic.tripleCellMultiplication xm i xp)
      (powerCell t (p ^ e) ≫ Dynamic.tripleCellMultiplication xm' i' xp') := by
  have := D.isOpenImmersion
  intro Z x y c h
  obtain ⟨m, s, a, rfl⟩ : ∃ m s a, x = lift m (lift s a) := ⟨_, _, _, eq_lift x⟩
  obtain ⟨m', s', a', rfl⟩ : ∃ m' s' a', y = lift m' (lift s' a') :=
    ⟨_, _, _, eq_lift y⟩
  obtain ⟨u, hu⟩ := D.isUnit_of_mul_eq m a m' a' s s' c h
  rw [D.mul_eq_cellProd m a m' a' s s' u hu] at h
  have hc : c = cellProd χ χv m a m' a' s s' u := (cancel_mono _).mp h.symm
  simp only [hc, ← Category.assoc, lift_powerCell,
    cellProd_powerCell t χ χv χ' χv' p e hχ hχv]
  exact D'.mul_eq_cellProd _ _ _ _ _ _ (u ^ p ^ e) (pow_unit_eq p e u a m' hu)

/-- Gluing the characteristic-power cell map gives an actual group homomorphism, with
the prescribed torus and positive and negative root maps. -/
theorem exists_powerHom (hG : IsConnectedReductive G)
    (D : IsRootCell i χ χv xp xm) (D' : IsRootCell i' χ' χv' xp' xm')
    (t : T ⟶ T') (p e : ℕ) [ExpChar k p] (hχ : t ≫ χ' = p ^ e • χ)
    (hχv : χv ≫ t = p ^ e • χv') :
    ∃ φ : G ⟶ G',
      i ≫ φ = CommGroupScheme.groupHom t ≫ i' ∧
      xm.hom.hom ≫ φ.hom.hom = gaPower (p ^ e) ≫ xm'.hom.hom ∧
      xp.hom.hom ≫ φ.hom.hom = gaPower (p ^ e) ≫ xp'.hom.hom ∧
      Dynamic.tripleCellMultiplication xm i xp ≫ φ.hom.hom =
        powerCell t (p ^ e) ≫ Dynamic.tripleCellMultiplication xm' i' xp' := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have := D.isOpenImmersion
  let hc := powerCell_compatible D D' t p e hχ hχv
  let φ := CellGluing.glueHom hc (unitPt T) unitPt_comp
  have hφ : Dynamic.tripleCellMultiplication xm i xp ≫ φ.hom.hom =
      powerCell t (p ^ e) ≫ Dynamic.tripleCellMultiplication xm' i' xp' :=
    CellGluing.cell_comp_glueHom hc (unitPt T) unitPt_comp
  refine ⟨φ, ?_, ?_, ?_, hφ⟩
  · apply Grp.hom_ext
    rw [Grp.comp_hom_hom, ← torusPt_comp (xm := xm) (xp := xp), Category.assoc, hφ]
    simp only [torusPt, ← Category.assoc, lift_powerCell, gaPower_one,
      Dynamic.lift_tripleCellMultiplication, MonObj.one_comp, one_mul, mul_one,
      Category.id_comp]
    rfl
  · have hm := congrArg (fun f => lift (𝟙 (Ga k).X) (lift 1 1) ≫ f) hφ
    simpa only [← Category.assoc, Dynamic.lift_tripleCellMultiplication,
      MonObj.one_comp, mul_one, lift_powerCell, gaPower_one, one_mul,
      Category.id_comp] using hm
  · have hp := congrArg (fun f => lift 1 (lift 1 (𝟙 (Ga k).X)) ≫ f) hφ
    simpa only [← Category.assoc, Dynamic.lift_tripleCellMultiplication,
      MonObj.one_comp, one_mul, lift_powerCell, gaPower_one,
      Category.id_comp] using hp

end Langlands.GroupScheme.RootCell
