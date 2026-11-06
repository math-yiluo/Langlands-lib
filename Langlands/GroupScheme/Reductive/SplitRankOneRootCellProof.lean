import Langlands.GroupScheme.Reductive.RankOneRootCellWeyl
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.RankOnePositiveRootProof
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof

/-! # Proof: root groups and the open cell in semisimple rank one -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneRootCellRelation

open RootCell (crd)

variable {k : Type u} [Field k]

/-! ### Coordinates -/

section Coordinates

variable {Z W : Over (Spec (CommRingCat.of k))}

theorem crd_gpt (x : Γ(Z.left, ⊤)) : crd (gpt x : Z ⟶ (Ga k).X) = x :=
  coordinates_gpt x 0

theorem gpt_crd (a : Z ⟶ (Ga k).X) : gpt (crd a) = a :=
  (eq_gpt a).symm

theorem crd_mul (a b : Z ⟶ (Ga k).X) : crd (a * b) = crd a + crd b :=
  congrFun (VectorGroup.coordinates_mul a b) 0

theorem crd_weightPointAction {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) (t : Z ⟶ S.X) (b : Z ⟶ (Ga k).X) :
    crd (VectorGroup.weightPointAction χ Z t b) = (cu χ t : Γ(Z.left, ⊤)) * crd b :=
  congrFun (VectorGroup.coordinates_weightPointAction χ Z t b) 0

theorem pb_mul (x y : Γ((base k).left, ⊤)) :
    WeylData.pb Z (x * y) = WeylData.pb Z x * WeylData.pb Z y :=
  map_mul _ x y

theorem pb_one : WeylData.pb Z (1 : Γ((base k).left, ⊤)) = 1 :=
  map_one _

theorem appTop_pb (f : W ⟶ Z) (x : Γ((base k).left, ⊤)) :
    f.left.appTop (WeylData.pb Z x) = WeylData.pb W x := by
  rw [WeylData.pb, WeylData.pb, ← comp_toBase f, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

end Coordinates

/-! ### Rescaling the additive group -/

section Scale

/-- Multiplication by a unit `c` of `k` on the points of `𝔾ₐ`. -/
def scaleEquiv (c : Γ((base k).left, ⊤)ˣ) (Z : Over (Spec (CommRingCat.of k))) :
    (Z ⟶ (Ga k).X) ≃* (Z ⟶ (Ga k).X) where
  toFun a := gpt (WeylData.pb Z (c : Γ((base k).left, ⊤)) * crd a)
  invFun a := gpt (WeylData.pb Z (↑c⁻¹ : Γ((base k).left, ⊤)) * crd a)
  left_inv a := by
    simp only
    rw [crd_gpt, ← mul_assoc, ← pb_mul, Units.inv_mul, pb_one, one_mul, gpt_crd]
  right_inv a := by
    simp only
    rw [crd_gpt, ← mul_assoc, ← pb_mul, Units.mul_inv, pb_one, one_mul, gpt_crd]
  map_mul' a b := by
    rw [crd_mul, mul_add, gpt_add]

theorem scaleEquiv_naturality (c : Γ((base k).left, ⊤)ˣ) {Z Z' : Over (Spec (CommRingCat.of k))}
    (w : Z' ⟶ Z) (a : Z ⟶ (Ga k).X) : scaleEquiv c Z' (w ≫ a) = w ≫ scaleEquiv c Z a := by
  change gpt _ = w ≫ gpt _
  rw [comp_gpt, map_mul, appTop_pb, RootCell.crd_comp]

/-- The automorphism of `𝔾ₐ` given by multiplication by a unit `c` of `k`. -/
def scaleIso (c : Γ((base k).left, ⊤)ˣ) : Ga k ≅ Ga k :=
  isoOfPoints (scaleEquiv c) (scaleEquiv_naturality c)

theorem comp_scaleIso_hom (c : Γ((base k).left, ⊤)ˣ) {Z : Over (Spec (CommRingCat.of k))}
    (a : Z ⟶ (Ga k).X) :
    a ≫ (scaleIso c).hom.hom.hom = gpt (WeylData.pb Z (c : Γ((base k).left, ⊤)) * crd a) :=
  comp_isoOfPoints_hom _ _ Z a

instance (c : Γ((base k).left, ⊤)ˣ) : IsIso (scaleIso c).hom.hom.hom :=
  ⟨⟨(scaleIso c).inv.hom.hom, congrArg (fun f => f.hom.hom) (scaleIso c).hom_inv_id,
    congrArg (fun f => f.hom.hom) (scaleIso c).inv_hom_id⟩⟩

end Scale

/-! ### The square of the Weyl point -/

/-- If the dynamic centralizer of the coroot `h` is represented by the torus, then the square
of a point normalizing the torus through the reflection `1 - α ≫ h` lies in the torus. -/
theorem exists_sq_eq_of_isNormalizingPoint {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    {α : characterLattice T} {h : cocharacterLattice T}
    (hC : (Dynamic.centralizer (CommGroupScheme.groupHom h ≫ i)).IsRepresentedBy i)
    (pair : latticePairing T α h = 2) {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : IsNormalizingPoint i n (latticeReflectionIso α h pair)) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X, n * n = z ≫ i.hom.hom := by
  have h2 : i ≫ (G.innerIso (n * n)).hom = i := by
    have h' := hn.mul hn
    rw [IsNormalizingPoint] at h'
    rw [h']
    have hσ : (latticeReflectionIso α h pair ≪≫ latticeReflectionIso α h pair).hom = 𝟙 T :=
      (latticeReflectionIso α h pair).hom_inv_id
    rw [hσ]
    exact Category.id_comp i
  have hmem : n * n ∈ (Dynamic.centralizer (CommGroupScheme.groupHom h ≫ i)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [Dynamic.mem_centralizer, Dynamic.orbit,
      comp_eq_constantPoint (fst _ (Gm (Spec (CommRingCat.of k))).X) (n * n)]
    let s := snd (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (Gm (Spec (CommRingCat.of k))).X ≫
      (CommGroupScheme.groupHom h).hom.hom
    have hx := comp_innerIso_hom G (n * n) _ (s ≫ i.hom.hom)
    have hx' : (s ≫ i.hom.hom) ≫ (G.innerIso (n * n)).hom.hom.hom = s ≫ i.hom.hom := by
      rw [Category.assoc]
      exact congrArg (fun f : T.toGrp ⟶ G => s ≫ f.hom.hom) h2
    rw [hx'] at hx
    change (s ≫ i.hom.hom) * _ * (s ≫ i.hom.hom)⁻¹ = _
    rw [mul_inv_eq_iff_eq_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hx.symm).symm
  exact ⟨(hC.pointsEquiv _).symm ⟨n * n, hmem⟩,
    (SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hC ⟨n * n, hmem⟩).symm⟩

/-! ### The rescaled negative root group -/

namespace WeylData

variable (D : WeylData k) {Z : Over (Spec (CommRingCat.of k))}

/-- The unit `β` of `k` with `xp(1) n = xm(β) γ xp(δ)`. -/
def unitβ : Γ((base k).left, ⊤)ˣ := D.cβ_isUnit.unit

/-- The rescaled negative root group `xm'(Y) = xm(β Y)`. -/
def xm' : Ga k ⟶ D.G := (scaleIso D.unitβ).hom ≫ D.xm

theorem comp_xp (a : Z ⟶ (Ga k).X) : a ≫ D.xp.hom.hom = D.A (crd a) := by
  rw [CellData.A, gpt_crd]

theorem comp_xm' (b : Z ⟶ (Ga k).X) : b ≫ D.xm'.hom.hom = D.B (pb Z D.cβ * crd b) := by
  rw [xm', Grp.comp_hom_hom, ← Category.assoc, comp_scaleIso_hom, CellData.B, unitβ,
    IsUnit.unit_spec]

theorem conj_xm' (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ D.T.X) (b : Z ⟶ (Ga k).X) :
    (t ≫ D.i.hom.hom) * (b ≫ D.xm'.hom.hom) * (t ≫ D.i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction (-D.α) Z t b ≫ D.xm'.hom.hom := by
  rw [comp_xm', comp_xm', ← CellData.I, CellData.I_mul_B, mul_inv_cancel_right,
    crd_weightPointAction, cu_neg]
  congr 1
  ring

theorem tripleCell_xm' :
    Dynamic.tripleCellMultiplication D.xm' D.i D.xp =
      ((scaleIso D.unitβ).hom.hom.hom ▷ _) ≫ D.cellMul := by
  simp only [CellData.cellMul, Dynamic.tripleCellMultiplication, MonObj.comp_mul,
    whiskerRight_fst_assoc, whiskerRight_snd_assoc, xm', Grp.comp_hom_hom]

theorem isOpenImmersion_xm' :
    IsOpenImmersion (Dynamic.tripleCellMultiplication D.xm' D.i D.xp).left := by
  have := D.open_cell
  rw [D.tripleCell_xm', Over.comp_left]
  have : IsIso ((scaleIso D.unitβ).hom.hom.hom ▷ (D.T.X ⊗ (Ga k).X)).left :=
    (inferInstance : IsIso ((Over.forget _).map
      ((scaleIso D.unitβ).hom.hom.hom ▷ (D.T.X ⊗ (Ga k).X))))
  infer_instance

/-- The rank-one relation for `xp`, `xm'` over algebraically closed points. -/
theorem relationOver_xm' (K : Type u) [Field K] [IsAlgClosed K]
    (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    RootCell.RelationOver D.i D.h D.xp D.xm' (Over.mk f) := by
  intro a b a' b' u hu ha hb
  rw [RootCell.RelationAt, comp_xp, comp_xm', comp_xm', comp_xp,
    D.rel_of_sqField (Z := Over.mk f) (sqField_Γ_Spec K) (crd a) (crd b) u hu, ha, hb,
    CellData.cellPt]
  simp only [mul_assoc, CellData.I, tH, Category.assoc]

/-- Over algebraically closed points, `xp(X) xm'(Y)` is not in the open cell when
`1 + XY = 0`. -/
theorem not_inCell_xm' (K : Type u) [Field K] [IsAlgClosed K]
    (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (a b : Over.mk f ⟶ (Ga k).X)
    (h : 1 + crd a * crd b = 0) : ¬ RootCell.InCell D.i D.xp D.xm' a b := by
  rintro ⟨c, hc⟩
  apply D.not_inCell_of_sqField (Z := Over.mk f) (sqField_Γ_Spec K) (crd a) (crd b) h
  refine ⟨c ≫ ((scaleIso D.unitβ).hom.hom.hom ▷ _), ?_⟩
  rw [Category.assoc, ← D.tripleCell_xm', hc, comp_xp, comp_xm']

/-- The root groups `xp` and `xm'` satisfy all clauses of the root-cell statement. -/
theorem isRootCell (hsep : IsSeparated D.G.X.hom) :
    RootCell.IsRootCell D.i D.α D.h D.xp D.xm' := by
  have H := RootCell.inCell_iff_and_relationOver (i := D.i) (χv := D.h) (xp := D.xp)
    (xm := D.xm') D.relationOver_xm' D.not_inCell_xm'
  exact ⟨D.hxp, D.conj_xm', D.isOpenImmersion_xm', H.1, H.2⟩

end WeylData

end RankOneRootCellRelation

open RankOneRootCellRelation in
/-- **Root groups and the open cell in semisimple rank one** (Conrad, *Reductive group
schemes*, Theorem 4.1.4 and Theorem 4.2.6, over a field). -/
theorem splitRankOneRootCell : SplitRankOneRootCellStatement.{u} := by
  intro k _ G hG T hT i hi J P hP hrank r
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  obtain ⟨xp, xm, hC, -, -, hxp, hxm, hopen⟩ := rankOne_exists_rootCell
    dynamicCentralizerReductive rankOnePositiveRootUniqueness splitRootLieLine hG hT i
    hi P hP hrank r
  have pair : latticePairing T (P.root r) (P.coroot r) = 2 := by
    rw [← hP.1]
    exact P.root_coroot_two r
  obtain ⟨n, hn⟩ := hP.exists_normalizing_latticeReflectionIso i hT r
  have hn2 := exists_sq_eq_of_isNormalizingPoint hC pair hn
  let D : WeylData k :=
    { G := G, T := T, i := i, xp := xp, xm := xm, α := P.root r, hxp := hxp, hxm := hxm,
      open_cell := hopen, h := P.coroot r, pair := pair, n := n, hn := hn, hn2 := hn2,
      irreducible := DynamicConnected.irreducibleSpace_of_smooth G }
  have hD := D.isRootCell (inferInstanceAs (IsSeparated G.X.hom))
  exact ⟨D.xp, D.xm', hD.conj_xp, hD.conj_xm, hD.isOpenImmersion, hD.exists_iff, hD.mul_eq⟩

end Langlands.GroupScheme
