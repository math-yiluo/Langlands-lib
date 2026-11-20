import Langlands.GroupScheme.SimplyConnected.FactorialRankOne
import Langlands.AlgebraicGeometry.FunctionFieldChart

/-! # The translated big-cell charts and the torus characters in the function field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitFactorial

open LocalSplitCell Langlands.AlgebraicGeometry.FunctionFieldChart

/-! ### Left translations -/

section Translation

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Left translation of `G` by a point `g` over the base: `x ↦ g · x`. -/
def leftTranslation (g : 𝟙_ (Over S) ⟶ G.X) : G.X ⟶ G.X :=
  (toUnit G.X ≫ g) * 𝟙 G.X

theorem comp_leftTranslation (g : 𝟙_ (Over S) ⟶ G.X) {Z : Over S} (x : Z ⟶ G.X) :
    x ≫ leftTranslation g = (toUnit Z ≫ g) * x := by
  rw [leftTranslation, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit G.X)
    (toUnit Z), Category.comp_id]

instance isIso_leftTranslation (g : 𝟙_ (Over S) ⟶ G.X) : IsIso (leftTranslation g) := by
  refine ⟨⟨leftTranslation g⁻¹, ?_, ?_⟩⟩
  · rw [comp_leftTranslation, leftTranslation, GrpObj.comp_inv, inv_mul_cancel_left]
  · rw [comp_leftTranslation, leftTranslation, GrpObj.comp_inv, mul_inv_cancel_left]

end Translation

instance nonempty_cellSpec (k : Type u) [Field k] (I : Type u) [Fintype I] (m n : ℕ) :
    Nonempty (cellSpec k I m n).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum (CellRing k I m n)))

namespace CellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : CellData k G) {m n : ℕ} (neg : Fin m ≃ {α // ¬ D.b.IsPos α})
  (pos : Fin n ≃ {α // D.b.IsPos α})

/-! ### The translated chart -/

/-- The big-cell chart translated on the left by `u_a(1)`. -/
def tchart (a : D.J) : cellSpec k D.I m n ⟶ G.X :=
  D.chart neg pos ≫ leftTranslation (rootPoint (D.u a) (𝟙_ _) 1)

theorem comp_tchart (a : D.J) {W : Over (Spec (CommRingCat.of k))} (z : W ⟶ cellSpec k D.I m n) :
    z ≫ D.tchart neg pos a = rootPoint (D.u a) W 1 * (z ≫ D.chart neg pos) := by
  rw [tchart, ← Category.assoc, comp_leftTranslation, comp_rootPoint, map_one]

instance isOpenImmersion_tchart (a : D.J) : IsOpenImmersion (D.tchart neg pos a).left := by
  have : IsIso (leftTranslation (rootPoint (D.u a) (𝟙_ (Over (Spec (CommRingCat.of k)))) 1)).left :=
    (inferInstance : IsIso ((Over.forget _).map (leftTranslation _)))
  change IsOpenImmersion ((D.chart neg pos).left ≫ _)
  infer_instance

/-! ### The boundary localization -/

variable {neg} in
/-- The position of the opposite of a simple root among the negative roots. -/
def oppIndex {a : D.J} (ha : a ∈ D.b.support) : Fin m :=
  neg.symm ⟨D.P.reflectionPerm a a, D.not_isPos_reflectionPerm_self ha⟩

variable (n) in
/-- The boundary function `1 + y_{-a}` of the translated chart. -/
def boundaryRing {a : D.J} (ha : a ∈ D.b.support) : CellRing k D.I m n :=
  1 + negVar k D.I m n (D.oppIndex (neg := neg) ha)

variable (n) in
/-- The localization of the cell ring at the boundary function. -/
abbrev BoundaryLoc {a : D.J} (ha : a ∈ D.b.support) : Type u :=
  Localization.Away (D.boundaryRing n neg ha)

variable (n) in
/-- The spectrum of the boundary localization. -/
abbrev boundarySpec {a : D.J} (ha : a ∈ D.b.support) : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (D.BoundaryLoc n neg ha))))

instance nonempty_boundarySpec {a : D.J} (ha : a ∈ D.b.support) :
    Nonempty (D.boundarySpec n neg ha).left := by
  have h0 : D.boundaryRing n neg ha ≠ 0 :=
    (prime_one_add_negVar k D.I m n (D.oppIndex (neg := neg) ha)).ne_zero
  have : IsDomain (D.BoundaryLoc n neg ha) := IsLocalization.Away.isDomain _ h0
  exact inferInstanceAs (Nonempty (PrimeSpectrum (D.BoundaryLoc n neg ha)))

variable (n) in
/-- The open inclusion of the boundary localization into the cell spectrum. -/
def boundaryIncl {a : D.J} (ha : a ∈ D.b.support) :
    D.boundarySpec n neg ha ⟶ cellSpec k D.I m n :=
  Over.homMk (Spec.map (CommRingCat.ofHom
      (algebraMap (CellRing k D.I m n) (D.BoundaryLoc n neg ha))))
    (by
      simp only [Over.mk_hom]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

instance isOpenImmersion_boundaryIncl {a : D.J} (ha : a ∈ D.b.support) :
    IsOpenImmersion (D.boundaryIncl n neg ha).left := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (CellRing k D.I m n) (D.BoundaryLoc n neg ha))))
  infer_instance

theorem pointRing_boundaryIncl {a : D.J} (ha : a ∈ D.b.support) (x : CellRing k D.I m n) :
    pointRing (D.boundaryIncl n neg ha) x =
      (Scheme.ΓSpecIso (CommRingCat.of (D.BoundaryLoc n neg ha))).inv
        (algebraMap (CellRing k D.I m n) (D.BoundaryLoc n neg ha) x) := by
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (CellRing k D.I m n) (D.BoundaryLoc n neg ha)))
  exact (congrArg (fun f => f.hom x) h).symm

variable (n) in
/-- The boundary function as a unit on the boundary localization. -/
def boundaryUnit {a : D.J} (ha : a ∈ D.b.support) : (Γ((D.boundarySpec n neg ha).left, ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (D.BoundaryLoc n neg ha))).inv.hom.toMonoidHom
    (IsLocalization.Away.algebraMap_isUnit (S := D.BoundaryLoc n neg ha)
      (D.boundaryRing n neg ha)).unit

theorem boundaryUnit_val {a : D.J} (ha : a ∈ D.b.support) :
    (D.boundaryUnit n neg ha : Γ((D.boundarySpec n neg ha).left, ⊤)) =
      pointRing (D.boundaryIncl n neg ha) (D.boundaryRing n neg ha) := by
  rw [pointRing_boundaryIncl]
  rfl

/-- **Comparison of the two charts on the boundary localization.** Over the locus where
`1 + y_{-a}` is invertible, the translated chart factors through the big-cell chart, and the
torus coordinate is multiplied by `a∨(1 + y_{-a})`. -/
theorem exists_boundary_comparison {a : D.J} (ha : a ∈ D.b.support) :
    ∃ ψ : D.boundarySpec n neg ha ⟶ cellSpec k D.I m n,
      ψ ≫ D.chart neg pos = D.boundaryIncl n neg ha ≫ D.tchart neg pos a ∧
      ψ ≫ specTorus k D.I m n = cocharPoint (D.P.coroot a) _ (D.boundaryUnit n neg ha) *
        (D.boundaryIncl n neg ha ≫ specTorus k D.I m n) := by
  obtain ⟨v', w', h⟩ := D.exists_translate_cellPoint ha neg pos (D.boundarySpec n neg ha)
    (fun r => pointRing (D.boundaryIncl n neg ha) (negVar k D.I m n r))
    (D.boundaryIncl n neg ha ≫ specTorus k D.I m n)
    (fun r => pointRing (D.boundaryIncl n neg ha) (posVar k D.I m n r))
    1 (D.boundaryUnit n neg ha)
    (by rw [boundaryUnit_val, boundaryRing, map_add, map_one, one_mul]; rfl)
  obtain ⟨x, hx⟩ := (LocalSplitBigCell.coordTriple_bijective k D.I m n (D.boundarySpec n neg ha)).2
    (v', cocharPoint (D.P.coroot a) _ (D.boundaryUnit n neg ha) *
      (D.boundaryIncl n neg ha ≫ specTorus k D.I m n), w')
  obtain ⟨ψ, hψ⟩ := (bijective_comp_cellCoordHom (D.boundarySpec n neg ha)).2 x
  have hψ' : ψ ≫ cellCoordHom k D.I m n = x := hψ
  simp only [LocalSplitBigCell.coordTriple, Prod.mk.injEq] at hx
  refine ⟨ψ, ?_, ?_⟩
  · have hL : ψ ≫ D.chart neg pos = cellPoint D.i D.u (fun r => (neg r : D.J))
        (fun r => (pos r : D.J)) _ v' (cocharPoint (D.P.coroot a) _ (D.boundaryUnit n neg ha) *
          (D.boundaryIncl n neg ha ≫ specTorus k D.I m n)) w' := by
      rw [chart, ← Category.assoc, hψ', comp_cellMap, hx.1, hx.2.1, hx.2.2]
    rw [hL, comp_tchart, comp_chart, h]
  · have h2 := coordTriple_comp_cellCoordHom ψ
    rw [hψ'] at h2
    simp only [LocalSplitBigCell.coordTriple, Prod.mk.injEq] at h2
    rw [← h2.2.1, hx.2.1]

/-! ### Torus characters on the charts -/

variable (m n) in
/-- The torus character `t ↦ ∏ᵢ tᵢ ^ χᵢ`, as a unit of the cell ring. -/
def charUnit (χ : D.I → ℤ) : (CellRing k D.I m n)ˣ :=
  ∏ i, torusVar k D.I m n i ^ χ i

variable (m n) in
/-- The torus character as a global function on the cell spectrum. -/
def charSection (χ : D.I → ℤ) : Γ((cellSpec k D.I m n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CellRing k D.I m n))).inv (D.charUnit m n χ : CellRing k D.I m n)

variable (n) in
/-- The boundary function as a global function on the cell spectrum. -/
def boundarySection {a : D.J} (ha : a ∈ D.b.support) : Γ((cellSpec k D.I m n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CellRing k D.I m n))).inv (D.boundaryRing n neg ha)

theorem unitsMap_pointRing_charUnit {W : Over (Spec (CommRingCat.of k))}
    (z : W ⟶ cellSpec k D.I m n) (χ : D.I → ℤ) :
    Units.map (pointRing z).toMonoidHom (D.charUnit m n χ) =
      ∏ i, splitTorus.pointsEquiv D.I W (z ≫ specTorus k D.I m n) i ^ χ i := by
  rw [charUnit, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow]
  congr 1
  apply Units.ext
  rw [Units.coe_map, pointsEquiv_comp_specTorus]
  rfl

private theorem zpow_finset_sum' {α M : Type*} [CommGroup M] (t : M) (s : Finset α)
    (f : α → ℤ) : t ^ (∑ j ∈ s, f j) = ∏ j ∈ s, t ^ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

private theorem map_units_mul_zpow {R L : Type*} [CommRing R] [Field L] (f : R →+* L)
    (x y : Rˣ) (e : ℤ) : f ((x * y ^ e : Rˣ) : R) = f x * f y ^ e := by
  rw [Units.val_mul, map_mul]
  congr 1
  have h := congrArg (fun w : Lˣ => (w : L)) (map_zpow (Units.map f.toMonoidHom) y e)
  simp only [Units.coe_map, Units.val_zpow_eq_zpow_val] at h
  exact h

/-- **Torus characters across the boundary.** In the function field of `G`, a torus character
read on the big-cell chart equals the same character read on the translated chart times the
`⟨χ, a∨⟩`-th power of the boundary function `1 + y_{-a}`. -/
theorem toFunctionField_charSection [IsIntegral G.X.left] {a : D.J} (ha : a ∈ D.b.support)
    (χ : D.I → ℤ) :
    toFunctionField (D.chart neg pos).left (D.charSection m n χ) =
      toFunctionField (D.tchart neg pos a).left (D.charSection m n χ) *
        toFunctionField (D.tchart neg pos a).left (D.boundarySection n neg ha) ^
          coPairing χ (D.P.coroot a) := by
  obtain ⟨ψ, h1, h2⟩ := D.exists_boundary_comparison neg pos ha
  have hψ1 : ψ.left ≫ (D.chart neg pos).left =
      (D.boundaryIncl n neg ha).left ≫ (D.tchart neg pos a).left := by
    rw [← Over.comp_left, h1, Over.comp_left]
  have : IsOpenImmersion (ψ.left ≫ (D.chart neg pos).left) := by
    rw [hψ1]
    infer_instance
  have : IsOpenImmersion ψ.left := IsOpenImmersion.of_comp ψ.left (D.chart neg pos).left
  have hunit : Units.map (pointRing ψ).toMonoidHom (D.charUnit m n χ) =
      Units.map (pointRing (D.boundaryIncl n neg ha)).toMonoidHom (D.charUnit m n χ) *
        D.boundaryUnit n neg ha ^ coPairing χ (D.P.coroot a) := by
    rw [unitsMap_pointRing_charUnit, unitsMap_pointRing_charUnit, h2, map_mul, cocharPoint,
      MulEquiv.apply_symm_apply, coPairing, zpow_finset_sum']
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm]
  have hval : ψ.left.appTop (D.charSection m n χ) =
      ((Units.map (pointRing (D.boundaryIncl n neg ha)).toMonoidHom (D.charUnit m n χ) *
        D.boundaryUnit n neg ha ^ coPairing χ (D.P.coroot a) :
          (Γ((D.boundarySpec n neg ha).left, ⊤))ˣ) : Γ((D.boundarySpec n neg ha).left, ⊤)) := by
    rw [← hunit]
    rfl
  rw [← toFunctionField_comp (D.chart neg pos).left ψ.left, toFunctionField_congr _ hψ1, hval,
    map_units_mul_zpow, Units.coe_map, boundaryUnit_val]
  change toFunctionField _ ((D.boundaryIncl n neg ha).left.appTop (D.charSection m n χ)) *
      toFunctionField _ ((D.boundaryIncl n neg ha).left.appTop (D.boundarySection n neg ha)) ^ _ = _
  rw [toFunctionField_comp, toFunctionField_comp]

end CellData

end Langlands.GroupScheme.SplitFactorial
