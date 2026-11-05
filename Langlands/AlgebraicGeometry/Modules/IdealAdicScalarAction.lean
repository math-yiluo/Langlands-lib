import Langlands.AlgebraicGeometry.Modules.IdealAdicQuotientDescent
import Langlands.AlgebraicGeometry.Modules.IdealAdicLayers
import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence

/-! # Base scalars acting on module sheaves, and transport of ideal multiples -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- Multiplication by a base scalar on a presheaf of modules. -/
def smulPresheaf (a : R) (P : X.PresheafOfModules) : P ⟶ P where
  app U := by
    letI : CommRing (X.ringCatSheaf.obj.obj U) := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom
      (LinearMap.lsmul (X.ringCatSheaf.obj.obj U) (P.obj U) (scalar f U.unop a))
  naturality {U V} i := by
    ext m
    change scalar f V.unop a • P.map i m = P.map i (scalar f U.unop a • m)
    rw [P.map_smul]
    change _ = X.presheaf.map i (scalar f U.unop a) • P.map i m
    rw [scalar_naturality]

/-- Multiplication by a base scalar on a module sheaf. -/
def smulEnd (a : R) (M : X.Modules) : M ⟶ M :=
  ⟨smulPresheaf f a M.val⟩

lemma smulEnd_app_apply (a : R) (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (smulEnd f a M).app U x = scalar f U a • x :=
  rfl

/-- Morphisms of module sheaves commute with base scalars. -/
@[reassoc]
lemma smulEnd_naturality (a : R) {M N : X.Modules} (φ : M ⟶ N) :
    smulEnd f a M ≫ φ = φ ≫ smulEnd f a N := by
  ext U x
  change φ.app U (scalar f U a • x) = scalar f U a • φ.app U x
  exact φ.app_smul (scalar f U a) x

/-- Scalars of the ideal vanish after the quotient projection. -/
@[reassoc (attr := simp)]
lemma smulEnd_projection (J : Ideal R) (M : X.Modules) {a : R} (ha : a ∈ J) :
    smulEnd f a M ≫ projection f J M = 0 := by
  have h := (inclusion_comp_eq_zero_iff f J (projection f J M)).1 (cokernel.condition _)
  ext U x
  exact h U a ha x

/-- Scalars of the ideal factor through the ideal multiple. -/
def smulToMultiple (J : Ideal R) (M : X.Modules) {a : R} (ha : a ∈ J) :
    M ⟶ multiple f J M :=
  Abelian.monoLift (inclusion f J M) (smulEnd f a M) (smulEnd_projection f J M ha)

@[reassoc (attr := simp)]
lemma smulToMultiple_inclusion (J : Ideal R) (M : X.Modules) {a : R} (ha : a ∈ J) :
    smulToMultiple f J M ha ≫ inclusion f J M = smulEnd f a M :=
  Abelian.monoLift_comp _ _ _

section Tensor

local instance : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

lemma smulPresheaf_whiskerRight (a : R) (P Q : X.PresheafOfModules) :
    smulPresheaf f a P ⊗ₘ 𝟙 Q = smulPresheaf f a (P ⊗ Q) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  rfl

lemma sheafify_map_smulPresheaf (a : R) (P : X.PresheafOfModules) :
    (sheafify X).map (smulPresheaf f a P) = smulEnd f a ((sheafify X).obj P) := by
  apply ((sheafifyAdjunction X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [← (sheafifyAdjunction X).unit.naturality (smulPresheaf f a P)]
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (((sheafifyAdjunction X).unit.app P).app U).hom.map_smul (scalar f U.unop a) x

/-- Tensoring with a fixed module sheaf commutes with base scalars. -/
lemma tensorBy_map_smulEnd (N : X.Modules) (a : R) (M : X.Modules) :
    (tensorBy N).map (smulEnd f a M) = smulEnd f a ((tensorBy N).obj M) := by
  change (sheafify X).map (smulPresheaf f a M.val ⊗ₘ 𝟙 N.val) = _
  rw [smulPresheaf_whiskerRight, sheafify_map_smulPresheaf]
  rfl

end Tensor

section Transport

variable (E : X.Modules ≌ X.Modules)
  (hE : ∀ (a : R) (A : X.Modules), E.functor.map (smulEnd f a A) = smulEnd f a (E.functor.obj A))
  (J : Ideal R) {M M' : X.Modules} (e : E.functor.obj M ≅ M')

include hE in
lemma transport_inclusion_projection :
    (E.functor.map (inclusion f J M) ≫ e.hom) ≫ projection f J M' = 0 := by
  let adj := E.toAdjunction
  apply (adj.homEquiv _ _).injective
  have h0 : ∀ (A B : X.Modules), adj.homEquiv A B 0 = 0 := by
    intro A B
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  rw [Category.assoc, adj.homEquiv_naturality_left, h0, inclusion_comp_eq_zero_iff]
  intro U a ha m
  have h : smulEnd f a M ≫ adj.homEquiv _ _ (e.hom ≫ projection f J M') = 0 := by
    rw [← adj.homEquiv_naturality_left, hE, smulEnd_naturality_assoc,
      smulEnd_projection f J M' ha, comp_zero, h0]
  exact congrArg (fun φ => φ.app U m) h

include hE in
lemma inclusion_transport_cokernel :
    inclusion f J M' ≫ cokernel.π (E.functor.map (inclusion f J M) ≫ e.hom) = 0 := by
  rw [inclusion_comp_eq_zero_iff]
  intro U a ha x
  have h : smulEnd f a M' ≫ cokernel.π (E.functor.map (inclusion f J M) ≫ e.hom) = 0 := by
    have hs : smulEnd f a M' = e.inv ≫ E.functor.map (smulToMultiple f J M ha) ≫
        (E.functor.map (inclusion f J M) ≫ e.hom) := by
      rw [← Category.assoc (E.functor.map _), ← E.functor.map_comp, smulToMultiple_inclusion, hE,
        smulEnd_naturality, Iso.inv_hom_id_assoc]
    rw [hs]
    simp only [Category.assoc, cokernel.condition, comp_zero]
  exact congrArg (fun φ => φ.app U x) h

/-- An equivalence commuting with base scalars carries ideal multiples to ideal multiples. -/
def multipleTransportIso : E.functor.obj (multiple f J M) ≅ multiple f J M' where
  hom := Abelian.monoLift (inclusion f J M') (E.functor.map (inclusion f J M) ≫ e.hom)
    (transport_inclusion_projection f E hE J e)
  inv := Abelian.monoLift (E.functor.map (inclusion f J M) ≫ e.hom) (inclusion f J M')
    (inclusion_transport_cokernel f E hE J e)
  hom_inv_id := by
    rw [← cancel_mono (E.functor.map (inclusion f J M) ≫ e.hom)]
    simp
  inv_hom_id := by
    rw [← cancel_mono (inclusion f J M')]
    simp

@[reassoc (attr := simp)]
lemma multipleTransportIso_hom_inclusion :
    (multipleTransportIso f E hE J e).hom ≫ inclusion f J M' =
      E.functor.map (inclusion f J M) ≫ e.hom :=
  Abelian.monoLift_comp _ _ _

/-- An equivalence commuting with base scalars carries ideal layers to ideal layers. -/
def layerTransportIso {I K : Ideal R} (h : I ≤ K) :
    E.functor.obj (layer f h M) ≅ layer f h M' :=
  PreservesCokernel.iso E.functor (multipleMap f h M) ≪≫
    cokernel.mapIso _ _ (multipleTransportIso f E hE I e) (multipleTransportIso f E hE K e) (by
      rw [← cancel_mono (inclusion f K M')]
      simp only [Category.assoc, multipleTransportIso_hom_inclusion, multipleMap_inclusion]
      rw [← E.functor.map_comp_assoc, multipleMap_inclusion])

end Transport

/-- Twisting the layers of the structure sheaf by a line bundle gives the layers of the
line bundle. -/
def layerTwistIso (N : X.Modules) (hN : Picard.IsLocallyFreeRankOne N)
    {I K : Ideal R} (h : I ≤ K) :
    (tensorBy N).obj (layer f h (structureSheaf X)) ≅ layer f h N :=
  haveI := tensorBy_isEquivalence N hN
  layerTransportIso f (tensorBy N).asEquivalence (tensorBy_map_smulEnd f N) (tensorLeftUnitor N) h

end Langlands.AlgebraicGeometry.Modules.IdealAdic
