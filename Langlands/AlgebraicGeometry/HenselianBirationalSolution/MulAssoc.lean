import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Mul

/-! # Associativity of the extended law with the law on `Y`

For the extension `μ : Y ×_S Y ⟶ G` of the law, `μ (x y, z) = μ (x, y z)` whenever `x y` and
`y z` are defined. Both sides are morphisms from the scheme of triples with `(x, y)` and `(y, z)`
in the domain, which is reduced; they agree wherever `(x y, z)` and `(x, y z)` lie in the domain,
by associativity of the law, and this open set contains the generic points. On the translates by
sections: `μ (c, y)` is the chart of `c` at `y`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}

/-- Proof-irrelevant congruence for `pullback.lift`. -/
theorem lift_congr {T X Z B : Scheme.{u}} {f₁ : X ⟶ B} {f₂ : Z ⟶ B} {a a' : T ⟶ X}
    {b b' : T ⟶ Z} (ha : a = a') (hb : b = b') {h : a ≫ f₁ = b ≫ f₂}
    {h' : a' ≫ f₁ = b' ≫ f₂} : pullback.lift a b h = pullback.lift a' b' h' := by
  subst ha hb
  rfl

/-- A point of the domain is the pair of its coordinates. -/
theorem defined_of_domain {T : Scheme.{u}} (a : T ⟶ m.domain.toScheme) :
    m.Defined (a ≫ m.domain.ι ≫ pullback.fst g g) (a ≫ m.domain.ι ≫ pullback.snd g g)
      (by simp only [Category.assoc, pullback.condition]) :=
  m.pairIn_domain_of_eq a (by apply pullback.hom_ext <;> simp)

theorem mul_eq_mulPt {T : Scheme.{u}} (a : T ⟶ m.domain.toScheme) :
    a ≫ m.mul = m.mulPt (a ≫ m.domain.ι ≫ pullback.fst g g) (a ≫ m.domain.ι ≫ pullback.snd g g)
      (by simp only [Category.assoc, pullback.condition]) (defined_of_domain a) := by
  rw [BirationalGroupLaw.mulPt]
  congr 1
  exact m.liftDom_eq _ _ _ _ a rfl rfl

namespace Triples

/-- The base of the scheme of triples. -/
abbrev qP : m.domain.toScheme ⟶ S := m.domain.ι ≫ pullback.snd g g ≫ g

/-- The scheme of triples: pairs `((y, z), (x, y))` of points of the domain. -/
abbrev T3 : Scheme.{u} :=
  pullback (m.domain.ι ≫ pullback.fst g g) (m.domain.ι ≫ pullback.snd g g)

theorem hxP : (m.domain.ι ≫ pullback.snd g g) ≫ g = qP (m := m) := by
  simp only [Category.assoc]

/-- `((y, z), (x, y)) ↦ (z, (x, y))`. -/
def sl₁ : T3 (m := m) ⟶ pullback g (qP (m := m)) :=
  sliceFst _ _ hxP m.domain.ι rfl

/-- `((y, z), (x, y)) ↦ (y z, (x, y))`. -/
def sl₂ : T3 (m := m) ⟶ pullback g (qP (m := m)) :=
  sliceFst _ _ hxP (leftT m) m.leftT_fst

theorem qP_eq_mul : qP (m := m) = m.mul ≫ g := by
  rw [m.mul_comp]
  simp only [qP, pullback.condition]

theorem qP_eq_fst : qP (m := m) = (m.domain.ι ≫ pullback.fst g g) ≫ g := by
  simp only [qP, Category.assoc, pullback.condition]

/-- `(z, (x, y)) ↦ (x y, z)`. -/
def ML : pullback g (qP (m := m)) ⟶ pullback g g :=
  pullback.map g qP g g (𝟙 Y) m.mul (𝟙 S) (by simp) (by rw [Category.comp_id, qP_eq_mul]) ≫
    (pullbackSymmetry g g).hom

/-- `(w, (x, y)) ↦ (x, w)`. -/
def MR : pullback g (qP (m := m)) ⟶ pullback g g :=
  pullback.map g qP g g (𝟙 Y) (m.domain.ι ≫ pullback.fst g g) (𝟙 S) (by simp)
    (by rw [Category.comp_id, qP_eq_fst]) ≫ (pullbackSymmetry g g).hom

/-- `(x, y, z) ↦ (x y, z)`. -/
def L : T3 (m := m) ⟶ pullback g g := sl₁ ≫ ML

/-- `(x, y, z) ↦ (x, y z)`. -/
def R : T3 (m := m) ⟶ pullback g g := sl₂ ≫ MR

theorem flat_ML [Smooth g] : Flat (ML (m := m)) := by
  have : Flat m.mul := flat_mul
  have : Flat (pullback.map g qP g g (𝟙 Y) m.mul (𝟙 S) (by simp)
      (by rw [Category.comp_id, qP_eq_mul])) :=
    MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance (by simp) qP_eq_mul
  unfold ML
  infer_instance

theorem flat_MR [Smooth g] : Flat (MR (m := m)) := by
  have : Flat (pullback.map g qP g g (𝟙 Y) (m.domain.ι ≫ pullback.fst g g) (𝟙 S) (by simp)
      (by rw [Category.comp_id, qP_eq_fst])) :=
    MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance (by simp) qP_eq_fst
  unfold MR
  infer_instance

@[reassoc (attr := simp)]
theorem L_fst : L (m := m) ≫ pullback.fst g g = pullback.snd _ _ ≫ m.mul := by
  simp [L, ML, sl₁]

@[reassoc (attr := simp)]
theorem L_snd : L (m := m) ≫ pullback.snd g g =
    pullback.fst _ _ ≫ m.domain.ι ≫ pullback.snd g g := by
  simp [L, ML, sl₁]

@[reassoc (attr := simp)]
theorem R_fst : R (m := m) ≫ pullback.fst g g =
    pullback.snd _ _ ≫ m.domain.ι ≫ pullback.fst g g := by
  simp [R, MR, sl₂]

@[reassoc (attr := simp)]
theorem R_snd : R (m := m) ≫ pullback.snd g g = pullback.fst _ _ ≫ m.mul := by
  simp [R, MR, sl₂, m.leftT_snd]

end Triples

variable [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m) [S.IsSeparated] (hL : HasSectionLifts g)

/-- `μ (x, y) = x y` in the chart `none` when `(x, y)` lies in the domain. -/
theorem lift_mulG {T : Scheme.{u}} (x y : T ⟶ Y) (h : x ≫ g = y ≫ g) (hd : m.Defined x y h) :
    pullback.lift x y h ≫ mulG H hL = m.mulPt x y h hd ≫ ch H none := by
  rw [← m.liftDom_ι x y h hd, Category.assoc, domain_mulG, BirationalGroupLaw.mulPt,
    Category.assoc]

/-- `μ (c, y)` is the chart of `c` at `y`. -/
theorem sectionPair_mulG (c : Sect g) : sectionPair c.1 c.2 ≫ mulG H hL = ch H (some c) := by
  refine ext_of_genericPoints_subset (secTrans H (some c)).dom
    (FibreGenerizationDense.genericPoints_subset (secTrans H (some c)).dom_dense) ?_
  have h2 := dom_chart H (some c) (𝟙 _)
  simp only [Category.id_comp] at h2
  have h3 : ((sectionPair c.1 c.2 ∣_ m.domain) ≫ m.mul) ≫ ch H none =
      (sectionPair c.1 c.2 ⁻¹ᵁ m.domain).ι ≫ ch H (some c) := h2.symm
  show (sectionPair c.1 c.2 ⁻¹ᵁ m.domain).ι ≫ sectionPair c.1 c.2 ≫ mulG H hL =
    (sectionPair c.1 c.2 ⁻¹ᵁ m.domain).ι ≫ ch H (some c)
  rw [← h3, ← Category.assoc, ← morphismRestrict_ι, Category.assoc, domain_mulG,
    Category.assoc]


open Triples in
/-- **Associativity of `μ` with `m`**: `μ (x y, z) = μ (x, y z)`. -/
theorem mulG_assoc : L (m := m) ≫ mulG H hL = R (m := m) ≫ mulG H hL := by
  have : IsReduced (pullback g (qP (m := m))) :=
    SmoothReducedBase.isReduced_of_smooth_of_isReduced (pullback.snd g (qP (m := m)))
  have : IsOpenImmersion (sl₁ (m := m)) := by unfold sl₁; infer_instance
  have : IsOpenImmersion (sl₂ (m := m)) := by unfold sl₂; infer_instance
  have : IsReduced (T3 (m := m)) := isReduced_of_isOpenImmersion (sl₁ (m := m))
  have : Flat (ML (m := m)) := flat_ML
  have : Flat (MR (m := m)) := flat_MR
  have : Flat (L (m := m)) := by unfold L; infer_instance
  have : Flat (R (m := m)) := by unfold R; infer_instance
  have hgen : genericPoints (T3 (m := m)) ⊆
      (L (m := m) ⁻¹ᵁ m.domain ⊓ R (m := m) ⁻¹ᵁ m.domain : (T3 (m := m)).Opens) := by
    intro x hx
    exact ⟨FibreGenerizationDense.genericPoints_subset H.strict.domain_fst
        (mapsTo_genericPoints _ (generalizingMap_of_flat _) hx),
      FibreGenerizationDense.genericPoints_subset H.strict.domain_fst
        (mapsTo_genericPoints _ (generalizingMap_of_flat _) hx)⟩
  refine ext_of_genericPoints_subset _ hgen ?_
  set W : (T3 (m := m)).Opens := L (m := m) ⁻¹ᵁ m.domain ⊓ R (m := m) ⁻¹ᵁ m.domain
  set u' := W.ι ≫ pullback.fst (m.domain.ι ≫ pullback.fst g g) (m.domain.ι ≫ pullback.snd g g)
  set uu := W.ι ≫ pullback.snd (m.domain.ι ≫ pullback.fst g g) (m.domain.ι ≫ pullback.snd g g)
  set x := uu ≫ m.domain.ι ≫ pullback.fst g g
  set y := uu ≫ m.domain.ι ≫ pullback.snd g g
  set z := u' ≫ m.domain.ι ≫ pullback.snd g g
  have hy' : u' ≫ m.domain.ι ≫ pullback.fst g g = y := by
    simp only [u', uu, y, Category.assoc]
    exact congrArg (W.ι ≫ ·) pullback.condition
  have hxy : x ≫ g = y ≫ g := by simp only [x, y, Category.assoc, pullback.condition]
  have hyz : y ≫ g = z ≫ g := by
    rw [← hy']
    simp only [z, Category.assoc, pullback.condition]
  have dxy : m.Defined x y hxy := defined_of_domain uu
  have dyz : m.Defined y z hyz := by
    have := defined_of_domain u'
    exact this.of_eq hy' rfl
  have huu : uu ≫ m.mul = m.mulPt x y hxy dxy := mul_eq_mulPt uu
  have hu' : u' ≫ m.mul = m.mulPt y z hyz dyz := by
    rw [mul_eq_mulPt u']
    exact m.mulPt_congr hy' rfl
  have hWL : W.ι ≫ L (m := m) = pullback.lift (m.mulPt x y hxy dxy) z (by simp [hxy, hyz]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, L_fst, ← Category.assoc, huu, pullback.lift_fst]
    · rw [Category.assoc, L_snd, pullback.lift_snd]
      simp only [z, u', Category.assoc]
  have hWR : W.ι ≫ R (m := m) = pullback.lift x (m.mulPt y z hyz dyz) (by simp [hxy]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, R_fst, pullback.lift_fst]
      simp only [x, uu, Category.assoc]
    · rw [Category.assoc, R_snd, ← Category.assoc, hu', pullback.lift_snd]
  have dl : m.Defined (m.mulPt x y hxy dxy) z (by simp [hxy, hyz]) := by
    rintro _ ⟨t, rfl⟩
    rw [← hWL, Scheme.Hom.comp_apply]
    exact t.2.1
  have dr : m.Defined x (m.mulPt y z hyz dyz) (by simp [hxy]) := by
    rintro _ ⟨t, rfl⟩
    rw [← hWR, Scheme.Hom.comp_apply]
    exact t.2.2
  rw [← Category.assoc, hWL, lift_mulG H hL _ _ _ dl, ← Category.assoc, hWR,
    lift_mulG H hL _ _ _ dr, m.mulPt_assoc x y z hxy hyz dxy dyz dl dr]

/-- `μ (x y, z) = μ (x, y z)` on points. -/
theorem mulG_assoc_pt {T : Scheme.{u}} (x y z : T ⟶ Y) (hxy : x ≫ g = y ≫ g)
    (hyz : y ≫ g = z ≫ g) (dxy : m.Defined x y hxy) (dyz : m.Defined y z hyz) :
    pullback.lift (m.mulPt x y hxy dxy) z (by simp [hxy, hyz]) ≫ mulG H hL =
      pullback.lift x (m.mulPt y z hyz dyz) (by simp [hxy]) ≫ mulG H hL := by
  set t : T ⟶ Triples.T3 (m := m) := pullback.lift (m.liftDom y z hyz dyz) (m.liftDom x y hxy dxy)
    (by simp)
  have hL' : t ≫ Triples.L (m := m) = pullback.lift (m.mulPt x y hxy dxy) z (by simp [hxy, hyz]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Triples.L_fst, pullback.lift_snd_assoc, pullback.lift_fst]
      rfl
    · rw [Category.assoc, Triples.L_snd, pullback.lift_fst_assoc, pullback.lift_snd,
        BirationalGroupLaw.liftDom_snd]
  have hR' : t ≫ Triples.R (m := m) = pullback.lift x (m.mulPt y z hyz dyz) (by simp [hxy]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Triples.R_fst, pullback.lift_snd_assoc, pullback.lift_fst,
        BirationalGroupLaw.liftDom_fst]
    · rw [Category.assoc, Triples.R_snd, pullback.lift_fst_assoc, pullback.lift_snd]
      rfl
  rw [← hL', ← hR', Category.assoc, Category.assoc, mulG_assoc H hL]

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
