import Langlands.AlgebraicGeometry.Picard.DualNumberScaling
import Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismUnits
import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions

/-! # Actual infinitesimal automorphisms of line bundles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.AlgebraicGeometry.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The canonical identification of units over inverse-image top with global units. -/
def topUnitsEquiv :
    Γ(thickening f, projection f ⁻¹ᵁ ⊤)ˣ ≃* Γ(thickening f, ⊤)ˣ := by
  rw [Scheme.Hom.preimage_top]

set_option backward.isDefEq.respectTransparency false in
/-- On global sections the open-wise reduction is the actual zero-section map. -/
lemma reductionMap_top : reductionMap f ⊤ = (closedPoint f).appTop := by
  change (closedPoint f).appTop ≫
    X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Actual pullback of automorphisms along the actual zero section. -/
def automorphismReduction (L : LineBundle (thickening f)) :
    Aut L →* Aut ((LineBundle.pullback (closedPoint f)).obj L) :=
  (LineBundle.pullback (closedPoint f)).mapAut L

/-- Actual automorphisms that become the identity on the zero section. -/
abbrev InfinitesimalAut (L : LineBundle (thickening f)) :=
  (automorphismReduction f L).ker

/-- The actual scalar comparison commutes with actual automorphism reduction. -/
lemma automorphismReduction_unitAutEquiv (L : LineBundle (thickening f))
    (r : Γ(thickening f, projection f ⁻¹ᵁ ⊤)ˣ) :
    automorphismReduction f L (LineBundle.unitAutEquiv L (topUnitsEquiv f r)) =
      LineBundle.unitAutEquiv ((LineBundle.pullback (closedPoint f)).obj L)
        (unitReduction f ⊤ r) := by
  change (LineBundle.pullback (closedPoint f)).mapIso
    (LineBundle.unitAutEquiv L (topUnitsEquiv f r)) = _
  rw [LineBundle.pullback_mapIso_unitAutEquiv]
  congr 1
  change Units.map (closedPoint f).appTop.hom.toMonoidHom r =
    Units.map (reductionMap f ⊤).hom.toMonoidHom r
  rw [reductionMap_top]
  rfl

/-- The actual global unit kernel is the actual infinitesimal automorphism group. -/
def unitKernelAutEquiv (L : LineBundle (thickening f)) :
    UnitKernel f ⊤ ≃* InfinitesimalAut f L where
  toFun r := ⟨LineBundle.unitAutEquiv L (topUnitsEquiv f r.val), by
    change automorphismReduction f L
      (LineBundle.unitAutEquiv L (topUnitsEquiv f r.val)) = 1
    rw [automorphismReduction_unitAutEquiv, r.property, map_one]⟩
  invFun a := ⟨(topUnitsEquiv f).symm ((LineBundle.unitAutEquiv L).symm a.val), by
    change unitReduction f ⊤
      ((topUnitsEquiv f).symm ((LineBundle.unitAutEquiv L).symm a.val)) = 1
    apply (LineBundle.unitAutEquiv ((LineBundle.pullback (closedPoint f)).obj L)).injective
    rw [← automorphismReduction_unitAutEquiv, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, a.property, map_one]⟩
  left_inv r := Subtype.ext
    (((topUnitsEquiv f).trans (LineBundle.unitAutEquiv L)).left_inv r.val)
  right_inv a := Subtype.ext
    (((topUnitsEquiv f).trans (LineBundle.unitAutEquiv L)).right_inv a.val)
  map_mul' r s := Subtype.ext
    (((topUnitsEquiv f).trans (LineBundle.unitAutEquiv L)).map_mul r.val s.val)

/-- Infinitesimal automorphisms are exactly multiplication by `1 + ε a`. -/
def infinitesimalAutEquiv (L : LineBundle (thickening f)) :
    Multiplicative Γ(X, ⊤) ≃* InfinitesimalAut f L :=
  (unitKernelEquiv f ⊤).trans (unitKernelAutEquiv f L)

/-- The comparison retains its actual scalar automorphism formula. -/
lemma infinitesimalAutEquiv_val (L : LineBundle (thickening f)) (a : Γ(X, ⊤)) :
    (infinitesimalAutEquiv f L (Multiplicative.ofAdd a)).val =
      LineBundle.unitAutEquiv L (topUnitsEquiv f (coefficientUnit f ⊤ a)) :=
  rfl

/-- Every automorphism of the reduced line bundle lifts, with no properness assumption. -/
lemma automorphismReduction_surjective (L : LineBundle (thickening f)) :
    Function.Surjective (automorphismReduction f L) := by
  intro a
  obtain ⟨r, hr⟩ := unitReduction_surjective f ⊤
    ((LineBundle.unitAutEquiv ((LineBundle.pullback (closedPoint f)).obj L)).symm a)
  refine ⟨LineBundle.unitAutEquiv L (topUnitsEquiv f r), ?_⟩
  rw [automorphismReduction_unitAutEquiv, hr, MulEquiv.apply_symm_apply]

/-- The commutative law is proved for the existing automorphism composition operation. -/
instance infinitesimalAutCommGroup (L : LineBundle (thickening f)) :
    CommGroup (InfinitesimalAut f L) :=
  { (inferInstance : Group (InfinitesimalAut f L)) with
    mul_comm := fun a b ↦ (infinitesimalAutEquiv f L).symm.injective (by
      rw [map_mul, map_mul, mul_comm]) }

/-- Actual infinitesimal automorphisms in additive notation are actual global functions. -/
def infinitesimalAutAddEquiv (L : LineBundle (thickening f)) :
    Additive (InfinitesimalAut f L) ≃+ FieldGlobalFunctions.sections f :=
  (infinitesimalAutEquiv f L).symm.toAdditive

/-- Scalar multiplication acts on the unique infinitesimal scalar coefficient. -/
instance infinitesimalAutSMul (L : LineBundle (thickening f)) :
    SMul k (Additive (InfinitesimalAut f L)) where
  smul c a := (infinitesimalAutAddEquiv f L).symm
    (c • infinitesimalAutAddEquiv f L a)

/-- The module laws preserve actual composition as the additive operation. -/
instance infinitesimalAutModule (L : LineBundle (thickening f)) :
    Module k (Additive (InfinitesimalAut f L)) :=
  Function.Injective.module k (infinitesimalAutAddEquiv f L).toAddMonoidHom
    (infinitesimalAutAddEquiv f L).injective
    (fun c a ↦ (infinitesimalAutAddEquiv f L).apply_symm_apply
      (c • infinitesimalAutAddEquiv f L a))

/-- Actual infinitesimal automorphisms are linearly the actual global functions. -/
def infinitesimalAutLinearEquiv (L : LineBundle (thickening f)) :
    Additive (InfinitesimalAut f L) ≃ₗ[k] FieldGlobalFunctions.sections f :=
  { infinitesimalAutAddEquiv f L with
    map_smul' := fun c a ↦ (infinitesimalAutAddEquiv f L).apply_symm_apply
      (c • infinitesimalAutAddEquiv f L a) }

set_option backward.isDefEq.respectTransparency false in
/-- On global sections the open-wise scaling is the actual scheme pullback. -/
lemma scaleSectionMap_top (c : k) :
    scaleSectionMap f c ⊤ = (scale f c).appTop := by
  change (scale f c).appTop ≫
    (thickening f).presheaf.map (𝟙 (Opposite.op (⊤ : (thickening f).Opens))) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient field acts on global functions through the given structure map. -/
lemma baseSectionMap_top :
    baseSectionMap f ⊤ = DerivedSections.structureRingHom f := by
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (f.appTop ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens)))) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Actual epsilon-scaling pullback multiplies the infinitesimal coefficient.
The target is the automorphism group of the actually pulled-back line bundle. -/
lemma pullback_infinitesimalAutEquiv (c : k) (L : LineBundle (thickening f))
    (a : Γ(X, ⊤)) :
    (LineBundle.pullback (scale f c)).mapIso
        (infinitesimalAutEquiv f L (Multiplicative.ofAdd a)).val =
      (infinitesimalAutEquiv f ((LineBundle.pullback (scale f c)).obj L)
        (Multiplicative.ofAdd (baseSectionMap f ⊤ c * a))).val := by
  erw [infinitesimalAutEquiv_val, LineBundle.pullback_mapIso_unitAutEquiv,
    infinitesimalAutEquiv_val]
  apply congrArg (LineBundle.unitAutEquiv ((LineBundle.pullback (scale f c)).obj L))
  have h := scaleSectionMap_coefficientUnit f c ⊤ a
  rw [scaleSectionMap_top] at h
  exact h

/-- The intrinsic automorphism module is the actual derived structure-sheaf H⁰. -/
def infinitesimalAutH0LinearEquiv (L : LineBundle (thickening f)) :
    Additive (InfinitesimalAut f L) ≃ₗ[k]
      (DerivedSections.relativeCohomology f 0).obj
        (SheafOfModules.unit X.ringCatSheaf) :=
  (infinitesimalAutLinearEquiv f L).trans
    ((DerivedSections.relativeCohomologyZeroIso f).app
      (SheafOfModules.unit X.ringCatSheaf)).toLinearEquiv.symm

/-- Properness makes the actual infinitesimal automorphism module finite dimensional. -/
theorem finiteDimensional_infinitesimalAut [IsProper f]
    (L : LineBundle (thickening f)) :
    FiniteDimensional k (Additive (InfinitesimalAut f L)) := by
  let := FieldGlobalFunctions.finite f
  exact Module.Finite.equiv (infinitesimalAutLinearEquiv f L).symm

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
