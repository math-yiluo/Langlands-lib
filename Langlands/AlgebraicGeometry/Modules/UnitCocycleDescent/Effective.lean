import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Affine
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Frame
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.StalkCriterion
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentStatements
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # Effective descent of unit cocycles to line bundles -/

universe u

open CategoryTheory AlgebraicGeometry Opposite Langlands.SchemeModule
  Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Scheme.UnitCocycleDescent

section Transpose

variable {U X Y : Scheme.{u}} (p : X ⟶ Y) {M : Y.Modules}

/-- The transpose along `f ≫ p` of a map `p^* M ⟶ 𝒪_X` pulled back along `f`. -/
lemma homEquiv_pullbackComp_inv_comp (f : U ⟶ X)
    (φ : (Scheme.Modules.pullback p).obj M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ p)).homEquiv _ _
        ((Scheme.Modules.pullbackComp f p).inv.app M ≫ (Scheme.Modules.pullback f).map φ ≫
          (pullbackUnitIso f).hom) =
      (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _ φ ≫
        (Scheme.Modules.pushforward p).map (unitToPushforwardUnit f) ≫
          (Scheme.Modules.pushforwardComp f p).hom.app _ := by
  have he := homEquiv_comp_map (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction f) φ (pullbackUnitIso f).hom
  rw [pullbackUnitAdjunction] at he
  have hc := homEquiv_conjugate ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ p)) (Scheme.Modules.pullbackComp f p).inv
    ((Scheme.Modules.pullback f).map φ ≫ (pullbackUnitIso f).hom)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, he] at hc
  rw [hc, Category.assoc]

/-- Sections of the transpose along `f ≫ p` of a map pulled back along `f`. -/
lemma homEquiv_pullbackComp_inv_comp_app (f : U ⟶ X)
    (φ : (Scheme.Modules.pullback p).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (W : Y.Opens) (s : Γ(M, W)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ p)).homEquiv _ _
        ((Scheme.Modules.pullbackComp f p).inv.app M ≫ (Scheme.Modules.pullback f).map φ ≫
          (pullbackUnitIso f).hom)).app W s =
      f.app (p ⁻¹ᵁ W)
        (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _ φ).app W s) := by
  rw [homEquiv_pullbackComp_inv_comp]
  rfl

/-- Sections of the transpose of a map precomposed with the comparison of pullbacks along
equal morphisms. -/
lemma homEquiv_pullbackCongr_hom_app {g₁ g₂ : U ⟶ Y} (e : g₁ = g₂)
    (k : (Scheme.Modules.pullback g₂).obj M ⟶ SheafOfModules.unit U.ringCatSheaf)
    (W : Y.Opens) (s : Γ(M, W)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g₁).homEquiv _ _
        ((Scheme.Modules.pullbackCongr e).hom.app M ≫ k)).app W s =
      U.presheaf.map (homOfLE (le_of_eq (by rw [e])) : g₁ ⁻¹ᵁ W ⟶ g₂ ⁻¹ᵁ W).op
        (((Scheme.Modules.pullbackPushforwardAdjunction g₂).homEquiv _ _ k).app W s) := by
  subst e
  simp only [Scheme.Modules.pullbackCongr]
  erw [Category.id_comp]
  exact (ConcreteCategory.congr_hom (U.presheaf.map_id (op (g₁ ⁻¹ᵁ W))) _).symm

end Transpose

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  (c : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → Γ(U, ⊤)ˣ)

/-- The map `p^* L ⟶ 𝒪_X` adjoint to the inclusion `L ⟶ p_* 𝒪_X` of the cocycle sheaf. -/
noncomputable def cocycleTriv :
    (Scheme.Modules.pullback p).obj (cocycleModule p c) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm (cocycleSubmodule p c).ι

/-- The transpose of `cocycleTriv` sends a cocycle section to itself. -/
lemma homEquiv_cocycleTriv_app (W : Y.Opens) (s : Γ(cocycleModule p c, W)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _ (cocycleTriv p c)).app W s =
      (s : ↥((cocycleSubmodule p c).obj (op W))).1 := by
  rw [cocycleTriv, Equiv.apply_symm_apply]
  rfl

variable {p c}

/-- With the local units of a unit cocycle, the cocycle sheaf is locally free of rank one. -/
theorem isLocallyFreeRankOne_cocycleModule
    (hA : Langlands.Algebra.UnitCocycleLocalUnitsStatement.{u})
    [IsAffineHom p] [Flat p] [Surjective p] (hnat : IsNatural p c)
    (hmul : IsMultiplicative p c) : IsLocallyFreeRankOne (cocycleModule p c) := fun y ↦ by
  obtain ⟨W, σ, hy, hσ, hu⟩ := exists_unit_cocycleSection hA hnat hmul y
  exact ⟨W, hy, nonempty_restrict_iso_unit p c σ hσ hu⟩

/-- With the local units of a unit cocycle, `cocycleTriv` is an isomorphism. -/
theorem isIso_cocycleTriv (hA : Langlands.Algebra.UnitCocycleLocalUnitsStatement.{u})
    [IsAffineHom p] [Flat p] [Surjective p] (hnat : IsNatural p c)
    (hmul : IsMultiplicative p c) : IsIso (cocycleTriv p c) := by
  refine isIso_of_isUnit_app_locally
    ((isLocallyFreeRankOne_cocycleModule hA hnat hmul).pullback p) _ fun x ↦ ?_
  obtain ⟨W, σ, hy, hσ, hu⟩ := exists_unit_cocycleSection hA hnat hmul (p x)
  let s : Γ(cocycleModule p c, W) := (⟨σ, hσ⟩ : (cocycleSubmodule p c).obj (op W))
  refine ⟨p ⁻¹ᵁ W,
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (cocycleModule p c)).app W s,
    hy, ?_⟩
  have h := homEquiv_cocycleTriv_app p c W s
  rw [Adjunction.homEquiv_unit] at h
  have h' : (cocycleTriv p c).app (p ⁻¹ᵁ W)
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (cocycleModule p c)).app W s) =
        σ := h
  rw [h']
  exact hu

/-- The comparison scalars of `cocycleTriv` are the given units. -/
theorem structureAutScalar_cocycleTriv [IsIso (cocycleTriv p c)] {U : Scheme.{u}}
    (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    structureAutScalar (equalCompositeUnitAut p a b h (asIso (cocycleTriv p c))) = c U a b h := by
  have key : (Scheme.Modules.pullbackCongr h).hom.app (cocycleModule p c) ≫
      (Scheme.Modules.pullbackComp b p).inv.app (cocycleModule p c) ≫ (Scheme.Modules.pullback b).map (cocycleTriv p c) ≫
        (pullbackUnitIso b).hom =
      ((Scheme.Modules.pullbackComp a p).inv.app (cocycleModule p c) ≫ (Scheme.Modules.pullback a).map (cocycleTriv p c) ≫
        (pullbackUnitIso a).hom) ≫ structureMulHom (c U a b h : Γ(U, ⊤)) := by
    apply ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ p)).homEquiv _ _).injective
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    conv_rhs => rw [Adjunction.homEquiv_naturality_right]
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.pushforward_map_app]
    rw [homEquiv_pullbackCongr_hom_app, homEquiv_pullbackComp_inv_comp_app,
      homEquiv_pullbackComp_inv_comp_app, homEquiv_cocycleTriv_app]
    refine Eq.trans ?_ (structureMulHom_app (c U a b h : Γ(U, ⊤)) ((a ≫ p) ⁻¹ᵁ W) _).symm
    have hs := (s : ↥((cocycleSubmodule p c).obj (op W))).2 U a b h (a ⁻¹ᵁ p ⁻¹ᵁ W) le_rfl
      (preimage_preimage_eq p h W).le
    rw [← Scheme.Hom.app_eq_appLE] at hs
    exact hs.symm.trans (mul_comm _ _)
  have hE : (equalCompositeUnitAut p a b h (asIso (cocycleTriv p c))).hom =
      structureMulHom (c U a b h : Γ(U, ⊤)) := by
    rw [equalCompositeUnitAut_hom, equalCompositeIso_hom]
    calc _ = ((pullbackUnitIso a).inv ≫ (Scheme.Modules.pullback a).map (inv (cocycleTriv p c)) ≫
            (Scheme.Modules.pullbackComp a p).hom.app (cocycleModule p c)) ≫
          ((Scheme.Modules.pullbackCongr h).hom.app (cocycleModule p c) ≫
            (Scheme.Modules.pullbackComp b p).inv.app (cocycleModule p c) ≫ (Scheme.Modules.pullback b).map (cocycleTriv p c) ≫
              (pullbackUnitIso b).hom) := by
          simp only [asIso_hom, asIso_inv, Category.assoc]
      _ = structureMulHom (c U a b h : Γ(U, ⊤)) := by
          rw [key]
          simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
          rw [← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
            Category.id_comp, Iso.inv_hom_id_assoc]
  apply Units.ext
  change structureEndValue (equalCompositeUnitAut p a b h (asIso (cocycleTriv p c))).hom ⊤ = _
  rw [hE, structureEndValue_mulHom]

/-- Effective descent of unit cocycles, given the local units of a unit cocycle along
faithfully flat algebras. -/
theorem unitCocycleDescentEffective_of_localUnits
    (hA : Langlands.Algebra.UnitCocycleLocalUnitsStatement.{u}) :
    UnitCocycleDescentEffectiveStatement.{u} := by
  intro X Y p _ _ _ c hnat hmul
  have := isIso_cocycleTriv hA hnat hmul
  exact ⟨⟨cocycleModule p c, isLocallyFreeRankOne_cocycleModule hA hnat hmul⟩,
    asIso (cocycleTriv p c), fun U a b h ↦ structureAutScalar_cocycleTriv a b h⟩

end Langlands.Scheme.UnitCocycleDescent
