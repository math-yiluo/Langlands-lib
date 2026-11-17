import Langlands.GroupScheme.Reductive.RankOneRingRelation
import Langlands.GroupScheme.Reductive.LocalSplitGeneratorRelations

/-! # Coroot-trivial torus maps and rank-one cell relations -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RingRootCell

variable {R : Type u} [CommRing R]

namespace CellData

/-- The actual torus-coordinate map of a rank-one cell. -/
def torusCellProjection (D : CellData R)
    {Q : GroupScheme (Spec (CommRingCat.of R))} (q : D.T.toGrp ⟶ Q) :
    (Ga R).X ⊗ (D.T.X ⊗ (Ga R).X) ⟶ Q.X :=
  (snd _ _ ≫ fst _ _) ≫ q.hom.hom

/-- The projection evaluates to exactly the original torus coordinate. -/
theorem lift_torusCellProjection (D : CellData R)
    {Q : GroupScheme (Spec (CommRingCat.of R))} (q : D.T.toGrp ⟶ Q)
    {Z : Over (Spec (CommRingCat.of R))} (y x : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) :
    lift (gpt y) (lift t (gpt x)) ≫ D.torusCellProjection q = t ≫ q.hom.hom := by
  simp only [torusCellProjection, ← Category.assoc, lift_snd, lift_fst]

end CellData

namespace WeylData

variable (D : WeylData R) {Q : GroupScheme (Spec (CommRingCat.of R))}
  (q : D.T.toGrp ⟶ Q)
  (hq : ∀ (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)ˣ),
    D.tH c ≫ q.hom.hom = 1)
  {Z : Over (Spec (CommRingCat.of R))}

/-- The exact negative-root translation formula whenever the Bruhat
  denominator is a unit. -/
theorem cellPt_mul_B_of_unit [IsAffine D.G.X.left]
    (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x w : Γ(Z.left, ⊤))
    (d : Γ(Z.left, ⊤)ˣ) (hd : (d : Γ(Z.left, ⊤)) = 1 + x * w) :
    D.cellPt y t x * D.B (pb Z D.cβ * w) =
      D.cellPt (y + (↑(cu D.α t)⁻¹ : Γ(Z.left, ⊤)) *
        (pb Z D.cβ * ((↑d⁻¹ : Γ(Z.left, ⊤)) * w)))
        (t * D.tH d) ((↑d⁻¹ : Γ(Z.left, ⊤)) * x) := by
  calc
    _ = D.B y * (D.I t * (D.A x * D.B (pb Z D.cβ * w))) := by
      simp only [CellData.cellPt, mul_assoc]
    _ = _ := by
      rw [D.relation x w d hd, D.I_mul_cellPt, D.B_mul_cellPt]

include hq in
/-- Killing the coroot kills the torus correction in the unit case. -/
theorem torus_quotient_eq_of_cellPt_relation_unit [IsAffine D.G.X.left]
    (y y' x x' w : Γ(Z.left, ⊤)) (t t' : Z ⟶ D.T.X)
    (d : Γ(Z.left, ⊤)ˣ) (hd : (d : Γ(Z.left, ⊤)) = 1 + x * w)
    (hxy : D.cellPt y t x * D.B (pb Z D.cβ * w) = D.cellPt y' t' x') :
    t ≫ q.hom.hom = t' ≫ q.hom.hom := by
  have ht := (D.cellPt_inj ((D.cellPt_mul_B_of_unit y t x w d hd).symm.trans hxy)).2.1
  rw [← ht, MonObj.mul_comp, hq Z d, mul_one]

open LocalSplitCell GenericLine Polynomial

private theorem denominator_notMem_genericIdeal
    {B : Type u} [CommRing B] [IsLocalRing B] (x w : B) :
    1 + Polynomial.C x * (Polynomial.C w + Polynomial.X) ∉ genericIdeal B := by
  have h : 1 + Polynomial.C x * (Polynomial.C w + Polynomial.X) ∉
      pointIdeal B (-w) := by
    rw [notMem_pointIdeal_iff]
    simp
  exact fun he => h (genericIdeal_le_pointIdeal (-w) he)

include hq in
/-- Over any local test ring, killing the coroot makes the torus cell
  value invariant under every negative-root translation remaining in the cell. -/
theorem torus_quotient_eq_of_cellPt_relation_local
    [IsAffine D.G.X.left] [IsAffine Q.X.left]
    (B : Type u) [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (y y' x x' z : Γ((Over.mk s).left, ⊤))
    (t t' : Over.mk s ⟶ D.T.X)
    (hxy : D.cellPt y t x * D.B z = D.cellPt y' t' x') :
    t ≫ q.hom.hom = t' ≫ q.hom.hom := by
  let Z := Over.mk s
  let beta : Γ(Z.left, ⊤)ˣ :=
    Units.map (toBase Z).left.appTop.hom.toMonoidHom D.unitβ.unit
  have hbeta : (beta : Γ(Z.left, ⊤)) = pb Z D.cβ := by
    change (toBase Z).left.appTop (D.unitβ.unit : Γ((base R).left, ⊤)) = _
    rw [IsUnit.unit_spec]
  let xB : B := (Scheme.ΓSpecIso (CommRingCat.of B)).hom x
  let wB : B := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    ((↑beta⁻¹ : Γ(Z.left, ⊤)) * z)
  let A₀ := AtPoint B 0
  let A₁ := Generic B
  let psi₀ : B[X] →+* A₀ := algebraMap B[X] A₀
  let psi₁ : B[X] →+* A₁ := algebraMap B[X] A₁
  let phi₀ : B →+* A₀ := psi₀.comp Polynomial.C
  let phi₁ : B →+* A₁ := psi₁.comp Polynomial.C
  let s₀ := Spec.map (CommRingCat.ofHom phi₀) ≫ s
  let s₁ := Spec.map (CommRingCat.ofHom phi₁) ≫ s
  let Z₀ := Over.mk s₀
  let Z₁ := Over.mk s₁
  let b₀ : Z₀ ⟶ Z := specHom phi₀ rfl
  let E : Z ⟶ Z₀ := specHom (evalAt (0 : B)) (specMap_evalAt_comp 0 s)
  have hEb : E ≫ b₀ = 𝟙 Z :=
    (specHom_comp_eq (by rw [← RingHom.comp_assoc, evalAt_comp_C]) _ _).trans
      (specHom_id _)
  have hks : Spec.map (CommRingCat.ofHom (toGeneric (0 : B))) ≫ s₀ = s₁ := by
    dsimp only [s₀, s₁]
    rw [specMap_comp_specMap]
    congr 2
    exact congrArg CommRingCat.ofHom <| (RingHom.comp_assoc _ _ _).symm.trans
      (congrArg (fun f : B[X] →+* A₁ => f.comp Polynomial.C) (toGeneric_comp 0))
  let k : Z₁ ⟶ Z₀ := specHom (toGeneric (0 : B)) hks
  let eta₀ : A₀ →+* Γ(Z₀.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom
  let eta₁ : A₁ →+* Γ(Z₁.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom
  let w₀ : Γ(Z₀.left, ⊤) := eta₀ (psi₀ (Polynomial.C wB + Polynomial.X))
  let g₀ : Z₀ ⟶ D.G.X :=
    (b₀ ≫ D.cellPt y t x) * D.B (pb Z₀ D.cβ * w₀)
  have hEw : E.left.appTop w₀ = (↑beta⁻¹ : Γ(Z.left, ⊤)) * z := by
    change (Spec.map (CommRingCat.ofHom (evalAt (0 : B)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv
        (psi₀ (Polynomial.C wB + Polynomial.X))) = _
    rw [specMap_appTop_ΓSpecIso_inv, evalAt_algebraMap]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero]
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id_apply _
  have hEg : E ≫ g₀ = D.cellPt y' t' x' := by
    dsimp only [g₀]
    rw [MonObj.comp_mul, ← Category.assoc E b₀, hEb, Category.id_comp,
      D.comp_B, map_mul, comp_pb, hEw, ← hbeta, Units.mul_inv_cancel_left]
    exact hxy
  have hmem : g₀.left (IsLocalRing.closedPoint A₀) ∈ Set.range D.cellMul.left := by
    have hcl : E.left (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A₀ :=
      IsLocalRing.comap_closedPoint (evalAt (0 : B))
    rw [← hcl]
    change (E ≫ g₀).left (IsLocalRing.closedPoint B) ∈ _
    rw [hEg]
    exact D.range_subset_of_inCell (D.inCell_cellPt y' t' x') ⟨_, rfl⟩
  let := D.open_cell
  obtain ⟨c₀, hc₀⟩ := exists_lift_of_localPoint_closedPoint_mem D.cellMul g₀ hmem
  obtain ⟨Y, T, X, hfactor⟩ := (D.inCell_iff g₀).mp ⟨c₀, hc₀⟩
  have hkw : k.left.appTop w₀ = eta₁ (psi₁ (Polynomial.C wB + Polynomial.X)) := by
    change (Spec.map (CommRingCat.ofHom (toGeneric (0 : B)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv
        (psi₀ (Polynomial.C wB + Polynomial.X))) = _
    rw [specMap_appTop_ΓSpecIso_inv, toGeneric_algebraMap]
    rfl
  have hbx : b₀.left.appTop x = eta₀ (psi₀ (Polynomial.C xB)) := by
    have he : (Scheme.ΓSpecIso (CommRingCat.of B)).inv xB = x :=
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id_apply _
    rw [← he]
    exact specMap_appTop_ΓSpecIso_inv phi₀ xB
  have hkx : k.left.appTop (b₀.left.appTop x) = eta₁ (psi₁ (Polynomial.C xB)) := by
    rw [hbx]
    change (Spec.map (CommRingCat.ofHom (toGeneric (0 : B)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv
        (psi₀ (Polynomial.C xB))) = _
    rw [specMap_appTop_ΓSpecIso_inv, toGeneric_algebraMap]
    rfl
  let f : B[X] := 1 + Polynomial.C xB * (Polynomial.C wB + Polynomial.X)
  have hf : f ∉ genericIdeal B := denominator_notMem_genericIdeal xB wB
  have hdunit : IsUnit (psi₁ f) :=
    IsLocalization.map_units A₁ (⟨f, hf⟩ : (genericIdeal B).primeCompl)
  let d : Γ(Z₁.left, ⊤)ˣ := Units.map eta₁.toMonoidHom hdunit.unit
  have hd : (d : Γ(Z₁.left, ⊤)) =
      1 + k.left.appTop (b₀.left.appTop x) * k.left.appTop w₀ := by
    rw [hkx, hkw]
    change eta₁ (hdunit.unit : A₁) = _
    rw [IsUnit.unit_spec]
    simp only [f, map_add, map_one, map_mul]
  have hgeneric : D.cellPt (k.left.appTop (b₀.left.appTop y)) (k ≫ b₀ ≫ t)
      (k.left.appTop (b₀.left.appTop x)) *
      D.B (pb Z₁ D.cβ * k.left.appTop w₀) =
        D.cellPt (k.left.appTop Y) (k ≫ T) (k.left.appTop X) := by
    have hh := congrArg (fun v => k ≫ v) hfactor
    dsimp only [g₀] at hh
    simp only [MonObj.comp_mul, D.comp_B, map_mul, comp_pb,
      D.comp_cellPt] at hh
    exact hh
  have heq := D.torus_quotient_eq_of_cellPt_relation_unit q hq _ _ _ _ _
    (k ≫ b₀ ≫ t) (k ≫ T) d hd hgeneric
  have heq₀ : (b₀ ≫ t) ≫ q.hom.hom = T ≫ q.hom.hom := by
    apply Over.OverMorphism.ext
    apply CellGluing.hom_ext_of_injective_specMap (toGeneric (0 : B))
      (toGeneric_injective 0)
    exact congrArg CommaMorphism.left heq
  have hEt : E ≫ T = t' := by
    have hh := congrArg (fun v => E ≫ v) hfactor
    rw [hEg, D.comp_cellPt] at hh
    exact (D.cellPt_inj hh.symm).2.1
  have hh := congrArg (fun v => E ≫ v) heq₀
  rw [← Category.assoc E (b₀ ≫ t), ← Category.assoc E b₀, hEb,
    Category.id_comp, ← Category.assoc E T, hEt] at hh
  exact hh

include hq in
/-- The torus quotient is invariant under every negative-root cell relation
  on every relative scheme test, including nonreduced tests. -/
theorem torus_quotient_eq_of_cellPt_relation
    [IsAffine D.G.X.left] [IsAffine Q.X.left]
    (y y' x x' z : Γ(Z.left, ⊤)) (t t' : Z ⟶ D.T.X)
    (hxy : D.cellPt y t x * D.B z = D.cellPt y' t' x') :
    t ≫ q.hom.hom = t' ≫ q.hom.hom := by
  apply Over.OverMorphism.ext
  apply CellGluing.hom_ext_of_localRingPoints
  intro B _ _ f
  let s := f ≫ Z.hom
  let b : Over.mk s ⟶ Z := Over.homMk f rfl
  have hb : D.cellPt (b.left.appTop y) (b ≫ t) (b.left.appTop x) *
      D.B (b.left.appTop z) =
        D.cellPt (b.left.appTop y') (b ≫ t') (b.left.appTop x') := by
    simpa only [MonObj.comp_mul, D.comp_cellPt, D.comp_B] using
      congrArg (fun v => b ≫ v) hxy
  have h := D.torus_quotient_eq_of_cellPt_relation_local q hq B s
    (b.left.appTop y) (b.left.appTop y') (b.left.appTop x)
    (b.left.appTop x') (b.left.appTop z) (b ≫ t) (b ≫ t') hb
  exact congrArg CommaMorphism.left h

end WeylData

end Langlands.GroupScheme.RingRootCell
