import Langlands.AlgebraicGeometry.Picard.DualNumberStructure
import Langlands.AlgebraicGeometry.Picard.DualNumberUnits

/-! # The actual zero-section unit kernel -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.GroupScheme.GeneralLinear.DualNumber

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Restriction to the actual zero section, with the original open as target. -/
def reductionMap (U : X.Opens) :
    Γ(thickening f, projection f ⁻¹ᵁ U) ⟶ Γ(X, U) :=
  (closedPoint f).appLE _ U (by
    rw [← Scheme.Hom.comp_preimage, closedPoint_projection, Scheme.Hom.id_preimage])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma projection_reductionMap (U : X.Opens) :
    (projection f).app U ≫ reductionMap f U = 𝟙 _ := by
  rw [reductionMap, (projection f).app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have hid : ∀ (g : X ⟶ X), g = 𝟙 X →
      ∀ h : U ≤ g ⁻¹ᵁ U, g.appLE U U h = 𝟙 _ := by
    rintro g rfl h
    simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp,
      homOfLE_refl, op_id] using X.presheaf.map_id (op U)
  exact hid _ (closedPoint_projection f) _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma testSectionMap_reductionMap (U : X.Opens) :
    testSectionMap f U ≫ reductionMap f U =
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom ≫ baseSectionMap f U := by
  unfold testSectionMap reductionMap baseSectionMap
  rw [Category.assoc, Scheme.Hom.appLE_comp_appLE]
  simp only [closedPoint_structure]
  rw [Scheme.Hom.comp_appLE]
  change (Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).appTop ≫
      f.appLE ⊤ U _ = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

@[simp]
lemma reductionMap_epsilon (U : X.Opens) :
    reductionMap f U (epsilonSection f U) = 0 := by
  have h := congrArg (fun r ↦ r.hom (DualNumber.eps : DualNumber k))
    (testSectionMap_reductionMap f U)
  change reductionMap f U (epsilonSection f U) =
    baseSectionMap f U (DualNumber.eps : DualNumber k).fst at h
  simpa using h

@[simp]
lemma reductionMap_projection_apply (U : X.Opens) (a : Γ(X, U)) :
    reductionMap f U ((projection f).app U a) = a :=
  congrArg (fun r ↦ r.hom a) (projection_reductionMap f U)

/-- The actual zero section is first-coordinate reduction in canonical coordinates. -/
lemma reductionMap_sectionMap (U : X.Opens) :
    (reductionMap f U).hom.comp (sectionMap f U) =
      (TrivSqZeroExt.fstHom Γ(X, U) Γ(X, U) Γ(X, U)).toRingHom := by
  apply RingHom.ext
  intro z
  change reductionMap f U (sectionMap f U z) = z.fst
  rw [sectionMap_apply, map_add, map_mul, reductionMap_epsilon,
    mul_zero, add_zero, reductionMap_projection_apply]

@[simp]
lemma reductionMap_sectionEquiv (U : X.Opens) (z : DualNumber Γ(X, U)) :
    reductionMap f U (sectionEquiv f U z) = z.fst :=
  DFunLike.congr_fun (reductionMap_sectionMap f U) z

/-- Reduction of actual units along the actual zero section. -/
def unitReduction (U : X.Opens) :
    Γ(thickening f, projection f ⁻¹ᵁ U)ˣ →* Γ(X, U)ˣ :=
  Units.map (reductionMap f U).hom.toMonoidHom

/-- The actual group of units restricting to one on the zero section. -/
abbrev UnitKernel (U : X.Opens) := (unitReduction f U).ker

/-- The section-ring equivalence restricts to the two actual reduction kernels. -/
def splitKernelEquiv (U : X.Opens) :
    DualNumberUnits.Kernel Γ(X, U) ≃* UnitKernel f U where
  toFun g := ⟨Units.mapEquiv (sectionEquiv f U).toMulEquiv g.val, by
    apply Units.ext
    change reductionMap f U (sectionEquiv f U (g.val : DualNumber Γ(X, U))) = 1
    rw [reductionMap_sectionEquiv]
    exact DualNumberUnits.fst_eq_one g⟩
  invFun g := ⟨(Units.mapEquiv (sectionEquiv f U).toMulEquiv).symm g.val, by
    apply Units.ext
    change ((sectionEquiv f U).symm (g.val : Γ(thickening f, projection f ⁻¹ᵁ U))).fst = 1
    rw [← reductionMap_sectionEquiv f U, RingEquiv.apply_symm_apply]
    exact congrArg (fun a : Γ(X, U)ˣ ↦ (a : Γ(X, U))) g.property⟩
  left_inv g := Subtype.ext ((Units.mapEquiv (sectionEquiv f U).toMulEquiv).left_inv g.val)
  right_inv g := Subtype.ext ((Units.mapEquiv (sectionEquiv f U).toMulEquiv).right_inv g.val)
  map_mul' g h := Subtype.ext ((Units.mapEquiv (sectionEquiv f U).toMulEquiv).map_mul g.val h.val)

/-- Coefficients add exactly as actual units restricting to one multiply. -/
def unitKernelEquiv (U : X.Opens) :
    Multiplicative Γ(X, U) ≃* UnitKernel f U :=
  DualNumberUnits.kernelEquiv.trans (splitKernelEquiv f U)

@[simp]
lemma unitKernelEquiv_val (U : X.Opens) (a : Γ(X, U)) :
    ((unitKernelEquiv f U (Multiplicative.ofAdd a)).val :
      Γ(thickening f, projection f ⁻¹ᵁ U)) =
        1 + (projection f).app U a * epsilonSection f U := by
  change sectionEquiv f U
    ((DualNumberUnits.kernelEquiv (Multiplicative.ofAdd a)).val : DualNumber Γ(X, U)) = _
  rw [DualNumberUnits.kernelEquiv_val, sectionEquiv_apply, sectionMap_apply]
  simp

lemma sectionEquiv_naturality {U V : X.Opens} (h : V ≤ U) (z : DualNumber Γ(X, U)) :
    (thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op (sectionEquiv f U z) =
      sectionEquiv f V (coefficientMap (X.presheaf.map (homOfLE h).op).hom z) :=
  (DFunLike.congr_fun (sectionMap_naturality f h) z).symm

@[reassoc]
lemma reductionMap_naturality {U V : X.Opens} (h : V ≤ U) :
    (thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op ≫ reductionMap f V =
      reductionMap f U ≫ X.presheaf.map (homOfLE h).op := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  obtain ⟨z, rfl⟩ := (sectionEquiv f U).surjective a
  change reductionMap f V ((thickening f).presheaf.map
    ((Opens.map (projection f).base).map (homOfLE h)).op (sectionEquiv f U z)) =
    X.presheaf.map (homOfLE h).op (reductionMap f U (sectionEquiv f U z))
  rw [sectionEquiv_naturality, reductionMap_sectionEquiv, reductionMap_sectionEquiv]
  rfl

/-- Actual restriction of a unit that restricts to one on the zero section. -/
def unitKernelMap {U V : X.Opens} (h : V ≤ U) : UnitKernel f U →* UnitKernel f V where
  toFun g := ⟨Units.map ((thickening f).presheaf.map
      ((Opens.map (projection f).base).map (homOfLE h)).op).hom.toMonoidHom g.val, by
    apply Units.ext
    change reductionMap f V
      ((thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op
          (g.val : Γ(thickening f, projection f ⁻¹ᵁ U))) = 1
    have hn := congrArg (fun r ↦ r.hom (g.val : Γ(thickening f, projection f ⁻¹ᵁ U)))
      (reductionMap_naturality f h)
    change reductionMap f V
      ((thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op
          (g.val : Γ(thickening f, projection f ⁻¹ᵁ U))) =
      X.presheaf.map (homOfLE h).op
        (reductionMap f U (g.val : Γ(thickening f, projection f ⁻¹ᵁ U))) at hn
    rw [hn]
    have hg := congrArg (fun a : Γ(X, U)ˣ ↦ (a : Γ(X, U))) g.property
    change reductionMap f U (g.val : Γ(thickening f, projection f ⁻¹ᵁ U)) = 1 at hg
    rw [hg, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g t := Subtype.ext (map_mul _ g.val t.val)

@[simp]
lemma unitKernelMap_equiv {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    unitKernelMap f h (unitKernelEquiv f U (Multiplicative.ofAdd a)) =
      unitKernelEquiv f V (Multiplicative.ofAdd (X.presheaf.map (homOfLE h).op a)) := by
  apply Subtype.ext
  apply Units.ext
  change (thickening f).presheaf.map
    ((Opens.map (projection f).base).map (homOfLE h)).op
      ((unitKernelEquiv f U (Multiplicative.ofAdd a)).val : _) = _
  rw [unitKernelEquiv_val, map_add, map_one, map_mul, unitKernelEquiv_val]
  have hp := congrArg (fun r ↦ r.hom a) ((projection f).naturality (homOfLE h).op)
  have he := congrArg (fun r ↦ r.hom (DualNumber.eps : DualNumber k))
    (testSectionMap_naturality f h)
  exact congrArg (1 + ·) (congrArg₂ (· * ·) hp.symm he)

/-- Additive notation for the actual multiplicative kernel. -/
def unitKernelAddEquiv (U : X.Opens) :
    Γ(X, U) ≃+ Additive (UnitKernel f U) where
  toFun a := Additive.ofMul (unitKernelEquiv f U (Multiplicative.ofAdd a))
  invFun g := ((unitKernelEquiv f U).symm g.toMul).toAdd
  left_inv a := congrArg Multiplicative.toAdd
    ((unitKernelEquiv f U).left_inv (Multiplicative.ofAdd a))
  right_inv g := congrArg Additive.ofMul ((unitKernelEquiv f U).right_inv g.toMul)
  map_add' a b := congrArg Additive.ofMul
    ((unitKernelEquiv f U).map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

/-- Reduction is surjective already on sections over each open. -/
lemma unitReduction_surjective (U : X.Opens) : Function.Surjective (unitReduction f U) := by
  intro g
  refine ⟨Units.map ((projection f).app U).hom.toMonoidHom g, ?_⟩
  apply Units.ext
  exact reductionMap_projection_apply f U (g : Γ(X, U))

/-- Actual unit reduction kernels, written additively, with actual restriction maps. -/
def unitKernelPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (Additive (UnitKernel f U.unop))
  map h := AddCommGrpCat.ofHom (unitKernelMap f h.unop.le).toAdditive
  map_id U := by
    apply AddCommGrpCat.ext
    intro g
    change Additive.ofMul (unitKernelMap f le_rfl g.toMul) = g
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun r ↦ r.hom (g.toMul.val : Γ(thickening f, projection f ⁻¹ᵁ U.unop)))
      ((actualPresheaf f).map_id U)
  map_comp {U V W} a b := by
    apply AddCommGrpCat.ext
    intro g
    change Additive.ofMul (unitKernelMap f (a ≫ b).unop.le g.toMul) =
      Additive.ofMul (unitKernelMap f b.unop.le (unitKernelMap f a.unop.le g.toMul))
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun r ↦ r.hom (g.toMul.val : Γ(thickening f, projection f ⁻¹ᵁ U.unop)))
      ((actualPresheaf f).map_comp a b)

/-- The additive structure presheaf is naturally the actual unit reduction kernel. -/
def unitKernelPresheafIso :
    X.presheaf ⋙ DualNumberUnits.ringAdditiveFunctor ≅ unitKernelPresheaf f :=
  NatIso.ofComponents (fun U ↦
    { hom := AddCommGrpCat.ofHom (unitKernelAddEquiv f U.unop).toAddMonoidHom
      inv := AddCommGrpCat.ofHom (unitKernelAddEquiv f U.unop).symm.toAddMonoidHom
      hom_inv_id := by
        apply AddCommGrpCat.ext
        intro a
        exact (unitKernelAddEquiv f U.unop).left_inv a
      inv_hom_id := by
        apply AddCommGrpCat.ext
        intro g
        exact (unitKernelAddEquiv f U.unop).right_inv g }) (by
    intro U V h
    ext a
    exact congrArg Additive.ofMul (unitKernelMap_equiv f h.unop.le a).symm)

/-- The actual sectionwise kernel satisfies the sheaf condition. -/
lemma unitKernelPresheaf_isSheaf : (unitKernelPresheaf f).IsSheaf := by
  apply TopCat.Presheaf.isSheaf_of_iso (unitKernelPresheafIso f)
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  change TopCat.Presheaf.IsSheaf (X.presheaf ⋙ forget CommRingCat)
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget CommRingCat) X.presheaf).mp X.sheaf.property

/-- The sheaf of units on the actual thickening reducing to one on the zero section. -/
def unitKernelSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨unitKernelPresheaf f, unitKernelPresheaf_isSheaf f⟩

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
