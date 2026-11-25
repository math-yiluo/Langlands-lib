/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath

/-!
# The Frobenius lift of base point data

For base point data `B` of a Weil group `W` (`AlgebraicGeometry.WeilGroup.BasePointData`), the
path `β : F_t ≅ F_{t ≫ Fr}` pushes down to an element `frobAut` of `π₁(C₀, s)` which lies in the
Weil group with degree one: it acts on the geometric fibres of the constant covers as the
geometric Frobenius (`AlgebraicGeometry.WeilGroup.BasePointData.mem_weilGroup_frobAut`).
Conjugation by it is the transport of `π₁(C, t)` along `Fr` and `β`
(`AlgebraicGeometry.WeilGroup.BasePointData.geomAut_frobConj`), and the iterated paths `β_m`
push down to its powers (`AlgebraicGeometry.WeilGroup.BasePointData.downAut_frobPathPow`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace CategoryTheory

/-- Solving `eqToIso a ≪≫ Y ≪≫ eqToIso b = eqToIso c ≪≫ X ≪≫ eqToIso d` for `X`. -/
lemma eqToIso_trans_trans_eq {𝒞 : Type*} [Category 𝒞] {A A₁ A₂ B B₁ B₂ : 𝒞} (a : A = A₁)
    (b : B₁ = B) (c : A = A₂) (d : B₂ = B) (X : A₂ ≅ B₂) (Y : A₁ ≅ B₁)
    (h : eqToIso a ≪≫ Y ≪≫ eqToIso b = eqToIso c ≪≫ X ≪≫ eqToIso d) :
    X = eqToIso (c.symm.trans a) ≪≫ Y ≪≫ eqToIso (b.trans d.symm) := by
  subst a b c d
  simpa using h.symm

/-- The inverse of `eqToIso p` is `eqToIso p.symm`. -/
lemma eqToIso_symm' {𝒞 : Type*} [Category 𝒞] {A B : 𝒞} (p : A = B) :
    (eqToIso p).symm = eqToIso p.symm := by
  subst p
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The path induced along `g` by the path induced along an endomorphism `f` over `Y`
(`f ≫ g = g`) is the path induced along `g`, up to the identifications `y ≫ f ≫ g = y ≫ g`. -/
lemma pullbackPathIso_pullbackPathIso_of_comp_eq {f : X ⟶ X} {g : X ⟶ Y} (hf : f ≫ g = g)
    {y z : Spec (.of Ω) ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso g (pullbackPathIso f τ) =
      eqToIso (by rw [Category.assoc, hf]) ≪≫ pullbackPathIso g τ ≪≫
        eqToIso (by rw [Category.assoc, hf]) := by
  have h := pullbackPathIso_comp f g τ
  rw [pullbackPathIso_congr hf] at h
  exact eqToIso_trans_trans_eq _ _ _ _ _ _ h

/-- The point underlying the image of a point under `eqToIso` of an equality of geometric
points is unchanged. -/
lemma eqToIso_hom_app_left {y z : Spec (.of Ω) ⟶ X} (h : y = z) (P : X.FiniteEtale)
    (x : (fiber y).obj P) : ((eqToIso (congrArg fiber h)).hom.app P x).left = x.left := by
  subst h
  rfl

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.WeilGroup.BasePointData

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} (B : BasePointData W)

/-- Changing the path in `downAut` multiplies by the image of a loop at `t`. -/
lemma downAut_eq_mul_geomAut {y : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber}
    (δ δ' : fiber B.t ≅ fiber y) (h : y ≫ p.geometricFiberProj = B.t ≫ p.geometricFiberProj) :
    B.downAut δ h = B.downAut δ' h * B.geomAut (.of (δ ≪≫ δ'.symm)) := by
  rw [geomAut_apply, downAut, downAut, ← map_mul]
  congr 1
  apply Aut.ext
  simp only [Aut.mul_asIso]
  rw [← Iso.trans_assoc, ← pullbackPathIso_trans]
  simp

/-- **The Frobenius lift has degree one**: the push-down of `β : F_t ≅ F_{t ≫ Fr}` acts on the
geometric fibres of the constant covers as the geometric Frobenius. -/
theorem mem_weilGroup_frobAut :
    haveI := W.geometricallyConnected
    (B.frobAut, Multiplicative.ofAdd (1 : ℤ)) ∈ weilGroup p W.basePoint W.fundamentalGroup := by
  have := W.geometricallyConnected
  have := W.connectedSpace
  refine (mem_weilGroup_iff p W.basePoint W.fundamentalGroup).2 fun A y ↦ ?_
  simp only [toAdd_ofAdd, zpow_one]
  apply ((ConcreteCategory.isIso_iff_bijective _).1
    (inferInstance : IsIso ((fiber W.basePoint).map (arithmeticFrobenius p A).hom))).1
  rw [fiber_map_arithmeticFrobenius_geometricFrobenius]
  obtain ⟨y', rfl⟩ : ∃ y', B.path.hom.app _ y' = y :=
    ⟨B.path.inv.app _ y, ConcreteCategory.congr_hom (B.path.inv_hom_id_app _) y⟩
  rw [← toAut_hom_app_apply (F := fiber W.basePoint) (G := W.fundamentalGroup)]
  rw [show toAut (fiber W.basePoint) W.fundamentalGroup B.frobAut =
    toAutMulEquiv (fiber W.basePoint) W.fundamentalGroup B.frobAut from rfl]
  rw [frobAut, downAut, toAutMulEquiv_toπ]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [ConcreteCategory.comp_apply]
  rw [show B.path.inv.app _ (B.path.hom.app _ y') = y' from
    ConcreteCategory.congr_hom (B.path.hom_inv_id_app _) y', ← ConcreteCategory.comp_apply,
    ← B.path.hom.naturality, ConcreteCategory.comp_apply]
  refine congrArg (B.path.hom.app _) ?_
  obtain ⟨z, rfl⟩ : ∃ z : (fiber B.t).obj ((pullback p.geometricFiberProj).obj (constantCover p A)),
      (pullbackFiberIso p.geometricFiberProj B.t).hom.app _ z = y' :=
    ⟨(pullbackFiberIso p.geometricFiberProj B.t).inv.app _ y',
      ConcreteCategory.congr_hom ((pullbackFiberIso _ _).inv_hom_id_app _) y'⟩
  apply fiber_ext
  rw [fiber_map_left, eqToIso_hom_app_left (by
    rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj])]
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    pullbackFiberIso_hom_app_left]
  rw [show (pullbackFiberIso p.geometricFiberProj B.t).inv.app _
      ((pullbackFiberIso p.geometricFiberProj B.t).hom.app _ z) = z from
    ConcreteCategory.congr_hom ((pullbackFiberIso _ _).hom_inv_id_app _) z]
  erw [path_section B.frobPath _ _ (sectionOfPoint_snd p A _ _) z
    (left_eq_sectionOfPoint p B.ht A z)]
  conv_rhs => rw [left_eq_sectionOfPoint p B.ht A z]
  apply Limits.pullback.hom_ext
  · simp [-constantCover_obj_hom, arithmeticFrobenius, constantCoverIso]
  · have key := comp_specMap_frobenius A (pointOfFiber p A z)
    simp only [pointOfFiber, Category.assoc] at key
    simp [-constantCover_obj_hom, arithmeticFrobenius, constantCoverIso, key]

/-- Conjugation by the Frobenius lift is the transport of loops at `t` along `Fr` and `β`:
for a loop `g` at `t`, the loop `β ≫ Fr_* g ≫ β⁻¹` maps to `frobAut⁻¹ (geomAut g) frobAut`. -/
theorem geomAut_frobConj (g : Aut (fiber B.t)) :
    B.geomAut (.of (B.frobPath ≪≫ pullbackPathIso p.geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm)) = B.frobAut⁻¹ * B.geomAut g * B.frobAut := by
  rw [geomAut_apply, geomAut_apply, frobAut, downAut, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Aut.ext
  simp only [Aut.mul_asIso, Aut.inv_asIso]
  rw [pullbackPathIso_trans, pullbackPathIso_trans, pullbackPathIso_symm,
    pullbackPathIso_pullbackPathIso_of_comp_eq
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj p)]
  simp only [Iso.trans_symm, eqToIso_symm', Iso.trans_assoc]

/-- The iterated path `β_m` pushes down to the `m`-th power of the Frobenius lift. -/
theorem downAut_frobPathPow (m : ℕ)
    (h : (B.t ≫ (p.geometricGaloisFrobenius ^ m).asIso.hom) ≫ p.geometricFiberProj =
      B.t ≫ p.geometricFiberProj) :
    B.downAut (B.frobPathPow m) h = B.frobAut ^ m := by
  induction m with
  | zero =>
    have h0 : B.t = B.t ≫ (p.geometricGaloisFrobenius ^ 0).asIso.hom := by
      rw [pow_zero]
      rfl
    rw [pow_zero B.frobAut, downAut, frobPathPow, pullbackPathIso_eqToIso _ h0, eqToIso_trans,
      eqToIso_refl]
    exact map_one B.toπ
  | succ m ih =>
    have hm : (B.t ≫ (p.geometricGaloisFrobenius ^ m).asIso.hom) ≫ p.geometricFiberProj =
        B.t ≫ p.geometricFiberProj := by
      rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
    have H : (B.t ≫ p.geometricGaloisFrobenius.asIso.hom) ≫
        (p.geometricGaloisFrobenius ^ m).asIso.hom =
        B.t ≫ (p.geometricGaloisFrobenius ^ (m + 1)).asIso.hom := by
      rw [pow_succ, Aut.mul_asIso, Iso.trans_hom, Category.assoc]
    rw [pow_succ' B.frobAut m, ← ih hm, frobAut]
    unfold downAut
    rw [← map_mul]
    congr 1
    apply Aut.ext
    simp only [Aut.mul_asIso]
    rw [frobPathPow, pullbackPathIso_trans, pullbackPathIso_trans,
      pullbackPathIso_pullbackPathIso_of_comp_eq
        (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj p m),
      pullbackPathIso_eqToIso _ H]
    simp only [Iso.trans_assoc, eqToIso_trans]

end AlgebraicGeometry.WeilGroup.BasePointData
