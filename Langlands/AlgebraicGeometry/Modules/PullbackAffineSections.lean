import Langlands.AlgebraicGeometry.SectionPullback
import Langlands.AlgebraicGeometry.Modules.LocalizationSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.AffinePullbackQuasicoherent
import Langlands.AlgebraicGeometry.Modules.AffineSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent

/-! # Sections of the actual module pullback over affine opens -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace Langlands.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- Restriction along an equality of opens is bijective on sections. -/
lemma bijective_map_of_eq (F : X.Modules) {U V : X.Opens} (h : U = V) (hle : V ≤ U) :
    Function.Bijective (F.presheaf.map (homOfLE hle).op) := by
  subst h
  have : (homOfLE hle).op = 𝟙 (op U) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  exact Function.bijective_id

/-- Section pullback along an open immersion is bijective over opens inside its range. -/
lemma sectionPullback_bijective_of_isOpenImmersion (j : Z ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (W : X.Opens) (hW : W ≤ j.opensRange) :
    Function.Bijective (sectionPullback j F W) := by
  have h := Langlands.AlgebraicGeometry.Modules.DerivedSections.pullback_unit_app_comp_restrictFunctorIsoPullback_inv
    j F W
  have hb : Function.Bijective
      (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).inv.app F).app
        (j ⁻¹ᵁ W) ∘ sectionPullback j F W) := by
    change Function.Bijective ⇑(((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      j).unit.app F).app W ≫
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).inv.app F).app
          (j ⁻¹ᵁ W))
    rw [h]
    apply bijective_map_of_eq
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact (inf_eq_right.mpr hW).symm
  have hi : Function.Bijective
      (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).inv.app F).app
        (j ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  exact (Function.Bijective.of_comp_iff' hi _).mp hb

/-- Section pullback followed by restriction to a smaller open. -/
def sectionPullbackLE (f : X ⟶ Y) (M : Y.Modules) {U : X.Opens} {V : Y.Opens}
    (h : U ≤ f ⁻¹ᵁ V) (m : Γ(M, V)) : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, U) :=
  ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op
    (sectionPullback f M V m)

lemma sectionPullbackLE_self (f : X ⟶ Y) (M : Y.Modules) (V : Y.Opens) (m : Γ(M, V)) :
    sectionPullbackLE f M (le_refl (f ⁻¹ᵁ V)) m = sectionPullback f M V m := by
  have : (homOfLE (le_refl (f ⁻¹ᵁ V))).op = 𝟙 (op (f ⁻¹ᵁ V)) := rfl
  rw [sectionPullbackLE, this, CategoryTheory.Functor.map_id]
  rfl

lemma sectionPullbackLE_add (f : X ⟶ Y) (M : Y.Modules) {U : X.Opens} {V : Y.Opens}
    (h : U ≤ f ⁻¹ᵁ V) (m m' : Γ(M, V)) :
    sectionPullbackLE f M h (m + m') = sectionPullbackLE f M h m + sectionPullbackLE f M h m' := by
  simp only [sectionPullbackLE, map_add]

lemma sectionPullbackLE_zero (f : X ⟶ Y) (M : Y.Modules) {U : X.Opens} {V : Y.Opens}
    (h : U ≤ f ⁻¹ᵁ V) : sectionPullbackLE f M h 0 = 0 := by
  simp only [sectionPullbackLE, map_zero]

lemma sectionPullbackLE_smul (f : X ⟶ Y) (M : Y.Modules) {U : X.Opens} {V : Y.Opens}
    (h : U ≤ f ⁻¹ᵁ V) (r : Γ(Y, V)) (m : Γ(M, V)) :
    sectionPullbackLE f M h (r • m) = f.appLE V U h r • sectionPullbackLE f M h m := by
  simp only [sectionPullbackLE, LinearMap.map_smulₛₗ, AlgebraicGeometry.Scheme.Modules.map_smul]
  rfl

lemma map_sectionPullbackLE (f : X ⟶ Y) (M : Y.Modules) {U U' : X.Opens} {V : Y.Opens}
    (h : U ≤ f ⁻¹ᵁ V) (i : U' ≤ U) (m : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE i).op
      (sectionPullbackLE f M h m) = sectionPullbackLE f M (i.trans h) m := by
  simp only [sectionPullbackLE]
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

lemma sectionPullbackLE_restrict (f : X ⟶ Y) (M : Y.Modules) {U : X.Opens} {V V' : Y.Opens}
    (j : V' ≤ V) (h : U ≤ f ⁻¹ᵁ V') (m : Γ(M, V)) :
    sectionPullbackLE f M h (M.presheaf.map (homOfLE j).op m) =
      sectionPullbackLE f M (h.trans fun _ hx => j hx) m := by
  rw [sectionPullbackLE, sectionPullback_restrict, ← ConcreteCategory.comp_apply,
    ← CategoryTheory.Functor.map_comp]
  rfl

/-- Restricted section pullback is bijective along an open immersion when the source open is
the full inverse image of an open inside the range. -/
lemma sectionPullbackLE_bijective_of_isOpenImmersion (j : Z ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {W : Z.Opens} {V : X.Opens} (hV : V ≤ j.opensRange)
    (h : W ≤ j ⁻¹ᵁ V) (hW : j ⁻¹ᵁ V = W) :
    Function.Bijective (sectionPullbackLE j F h) :=
  (bijective_map_of_eq _ hW h).comp (sectionPullback_bijective_of_isOpenImmersion j F V hV)

lemma pullbackCongr_hom_sectionPullbackLE {g g' : X ⟶ Y} (hg : g = g') (M : Y.Modules)
    {U : X.Opens} {V : Y.Opens} (h : U ≤ g ⁻¹ᵁ V) (h' : U ≤ g' ⁻¹ᵁ V) (m : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hg).hom.app M).app U
      (sectionPullbackLE g M h m) = sectionPullbackLE g' M h' m := by
  subst hg
  rfl

lemma pullbackCongr_inv_sectionPullbackLE {g g' : X ⟶ Y} (hg : g = g') (M : Y.Modules)
    {U : X.Opens} {V : Y.Opens} (h : U ≤ g ⁻¹ᵁ V) (h' : U ≤ g' ⁻¹ᵁ V) (m : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hg).inv.app M).app U
      (sectionPullbackLE g' M h' m) = sectionPullbackLE g M h m := by
  subst hg
  rfl

lemma pullbackComp_hom_sectionPullbackLE {X' : AlgebraicGeometry.Scheme.{u}} (a : X' ⟶ X)
    (b : X ⟶ Y) (M : Y.Modules) {W : X'.Opens} {U : X.Opens} {V : Y.Opens}
    (hU : U ≤ b ⁻¹ᵁ V) (hW : W ≤ a ⁻¹ᵁ U) (hW' : W ≤ (a ≫ b) ⁻¹ᵁ V) (m : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp a b).hom.app M).app W
      (sectionPullbackLE a ((AlgebraicGeometry.Scheme.Modules.pullback b).obj M) hW
        (sectionPullbackLE b M hU m)) =
      sectionPullbackLE (a ≫ b) M hW' m := by
  change ((AlgebraicGeometry.Scheme.Modules.pullbackComp a b).hom.app M).app W
    (sectionPullbackLE a _ hW
      (((AlgebraicGeometry.Scheme.Modules.pullback b).obj M).presheaf.map (homOfLE hU).op
        (sectionPullback b M V m))) = _
  rw [sectionPullbackLE_restrict]
  exact (PresheafOfModules.naturality_apply
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp a b).hom.app M).val
    (homOfLE hW').op _).trans
    (congrArg _ (sectionPullback_comp a b M V m))

lemma pullbackComp_inv_sectionPullbackLE {X' : AlgebraicGeometry.Scheme.{u}} (a : X' ⟶ X)
    (b : X ⟶ Y) (M : Y.Modules) {W : X'.Opens} {U : X.Opens} {V : Y.Opens}
    (hU : U ≤ b ⁻¹ᵁ V) (hW : W ≤ a ⁻¹ᵁ U) (hW' : W ≤ (a ≫ b) ⁻¹ᵁ V) (m : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp a b).inv.app M).app W
      (sectionPullbackLE (a ≫ b) M hW' m) =
      sectionPullbackLE a ((AlgebraicGeometry.Scheme.Modules.pullback b).obj M) hW
        (sectionPullbackLE b M hU m) := by
  rw [← pullbackComp_hom_sectionPullbackLE a b M hU hW hW' m, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app,
    Scheme.Modules.Hom.id_app]
  rfl

lemma squarePullbackIso_hom_sectionPullbackLE {X' Y' : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y) (hs : p' ≫ t = s ≫ p)
    (M : Y.Modules) {W : X'.Opens} {U : X.Opens} {V' : Y'.Opens} {V : Y.Opens}
    (hV' : V' ≤ t ⁻¹ᵁ V) (hU : U ≤ p ⁻¹ᵁ V) (hW : W ≤ p' ⁻¹ᵁ V') (hW' : W ≤ s ⁻¹ᵁ U)
    (m : Γ(M, V)) :
    (squarePullbackIso p p' s t hs M).hom.app W
      (sectionPullbackLE p' ((AlgebraicGeometry.Scheme.Modules.pullback t).obj M) hW
        (sectionPullbackLE t M hV' m)) =
      sectionPullbackLE s ((AlgebraicGeometry.Scheme.Modules.pullback p).obj M) hW'
        (sectionPullbackLE p M hU m) := by
  have h1 : W ≤ (p' ≫ t) ⁻¹ᵁ V := fun _ hx => hV' (hW hx)
  have h2 : W ≤ (s ≫ p) ⁻¹ᵁ V := fun _ hx => hU (hW' hx)
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [pullbackComp_hom_sectionPullbackLE p' t M hV' hW h1,
    pullbackCongr_hom_sectionPullbackLE hs M h1 h2,
    pullbackComp_inv_sectionPullbackLE s p M hU hW' h2]

/-- The canonical chart of an affine open induces the inverse `Γ`-`Spec` isomorphism on
sections over the open. -/
lemma isAffineOpen_fromSpec_appLE_top {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [AlgebraicGeometry.Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  have : (eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h).op =
      𝟙 (op (⊤ : (Spec Γ(X, U)).Opens)) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The `R`-module structure on global sections over `Spec R`. -/
lemma moduleSpecΓFunctor_smul {R : CommRingCat.{u}} (N : (Spec R).Modules) (r : R)
    (n : (moduleSpecΓFunctor (R := R)).obj N) :
    (r • n : (moduleSpecΓFunctor (R := R)).obj N) =
      ((AlgebraicGeometry.Scheme.ΓSpecIso R).inv r • (show Γ(N, ⊤) from n) : Γ(N, ⊤)) := by
  erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]

section TensorMap

variable (f : X ⟶ Y) (M : Y.Modules) {U : X.Opens} {V : Y.Opens} (h : U ≤ f ⁻¹ᵁ V)

/-- Restricted section pullback as a linear map into the restriction of scalars along
`f.appLE V U h`. -/
def sectionPullbackLELinear :
    ModuleCat.of Γ(Y, V) Γ(M, V) ⟶ (ModuleCat.restrictScalars (f.appLE V U h).hom).obj
      (ModuleCat.of Γ(X, U) Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, U)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (f.appLE V U h).hom).obj
      (ModuleCat.of Γ(X, U) Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, U)))
    { toFun := sectionPullbackLE f M h
      map_add' := sectionPullbackLE_add f M h
      map_smul' := fun r m => sectionPullbackLE_smul f M h r m }

/-- The canonical scalar-extension map
`Γ(X, U) ⊗_{Γ(Y, V)} Γ(M, V) ⟶ Γ(f^* M, U)`, `s ⊗ m ↦ s • (f^* m)|_U`. -/
def pullbackTensorMap :
    (ModuleCat.extendScalars (f.appLE V U h).hom).obj (ModuleCat.of Γ(Y, V) Γ(M, V)) ⟶
      ModuleCat.of Γ(X, U) Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, U) :=
  ((ModuleCat.extendRestrictScalarsAdj (f.appLE V U h).hom).homEquiv _ _).symm
    (sectionPullbackLELinear f M h)

lemma pullbackTensorMap_one_tmul (m : Γ(M, V)) :
    pullbackTensorMap f M h ((1 : Γ(X, U)) ⊗ₜ[Γ(Y, V), (f.appLE V U h).hom] m) =
      sectionPullbackLE f M h m := by
  have hh := congrArg (fun k => k m)
    (((ModuleCat.extendRestrictScalarsAdj (f.appLE V U h).hom).homEquiv _ _).apply_symm_apply
      (sectionPullbackLELinear f M h))
  exact hh

lemma pullbackTensorMap_tmul (s : Γ(X, U)) (m : Γ(M, V)) :
    pullbackTensorMap f M h (s ⊗ₜ[Γ(Y, V), (f.appLE V U h).hom] m) =
      s • sectionPullbackLE f M h m := by
  have hs : (s ⊗ₜ[Γ(Y, V), (f.appLE V U h).hom] m :
      (ModuleCat.extendScalars (f.appLE V U h).hom).obj (ModuleCat.of Γ(Y, V) Γ(M, V))) =
      s • ((1 : Γ(X, U)) ⊗ₜ[Γ(Y, V), (f.appLE V U h).hom] m) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [hs, map_smul, pullbackTensorMap_one_tmul]

/-- The actual pullback unit on global sections over `Spec R` is section pullback. -/
lemma affineSectionsPullbackMap_eq {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : (Spec R).Modules)
    (hT : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤) (n : (moduleSpecΓFunctor (R := R)).obj N) :
    affineSectionsPullbackMap φ N n = sectionPullbackLE (Spec.map φ) N hT n := by
  rw [sectionPullbackLE]
  have : (homOfLE hT).op = 𝟙 (op (Spec.map φ ⁻¹ᵁ ⊤)) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

end TensorMap

section Bijective

variable {f} {M}

/-- Section pullback along the canonical chart of an affine open, as a linear map into global
sections over its spectrum. -/
def fromSpecSectionsLinear (M : Y.Modules) {V : Y.Opens} (hV : IsAffineOpen V) :
    ModuleCat.of Γ(Y, V) Γ(M, V) ⟶ (moduleSpecΓFunctor (R := Γ(Y, V))).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback hV.fromSpec).obj M) :=
  ModuleCat.ofHom (Y := (moduleSpecΓFunctor (R := Γ(Y, V))).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback hV.fromSpec).obj M))
    { toFun := sectionPullbackLE hV.fromSpec M hV.fromSpec_preimage_self.ge
      map_add' := sectionPullbackLE_add _ M _
      map_smul' := fun r m => by
        refine (sectionPullbackLE_smul _ M _ r m).trans ?_
        rw [isAffineOpen_fromSpec_appLE_top]
        exact (moduleSpecΓFunctor_smul _ r _).symm }

lemma fromSpecSectionsLinear_apply (M : Y.Modules) {V : Y.Opens} (hV : IsAffineOpen V)
    (m : Γ(M, V)) :
    fromSpecSectionsLinear M hV m =
      sectionPullbackLE hV.fromSpec M hV.fromSpec_preimage_self.ge m :=
  rfl

lemma fromSpecSectionsLinear_bijective (M : Y.Modules) {V : Y.Opens} (hV : IsAffineOpen V) :
    Function.Bijective (fromSpecSectionsLinear M hV) :=
  sectionPullbackLE_bijective_of_isOpenImmersion hV.fromSpec M hV.opensRange_fromSpec.ge _
    hV.fromSpec_preimage_self

/-- Over affine opens, the canonical map `Γ(X, U) ⊗_{Γ(Y, V)} Γ(M, V) ⟶ Γ(f^* M, U)` is
bijective for quasi-coherent `M`. -/
theorem pullbackTensorMap_bijective (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]
    {U : X.Opens} {V : Y.Opens} (h : U ≤ f ⁻¹ᵁ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Function.Bijective (pullbackTensorMap f M h) := by
  have hs : Spec.map (f.appLE V U h) ≫ hV.fromSpec = hU.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hU h
  have hx : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have hc : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hT : (⊤ : (Spec Γ(X, U)).Opens) ≤ Spec.map (f.appLE V U h) ⁻¹ᵁ ⊤ := le_top
  have heL : IsIso (fromSpecSectionsLinear M hV) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (fromSpecSectionsLinear_bijective M hV)
  have hTb : Function.Bijective
      ((ModuleCat.extendScalars (f.appLE V U h).hom).map (fromSpecSectionsLinear M hV)) :=
    ConcreteCategory.bijective_of_isIso _
  have hσ : Function.Bijective (affineScalarSectionsMap (f.appLE V U h)
      ((AlgebraicGeometry.Scheme.Modules.pullback hV.fromSpec).obj M)) :=
    ConcreteCategory.bijective_of_isIso _
  have hsq : Function.Bijective
      ((squarePullbackIso f (Spec.map (f.appLE V U h)) hU.fromSpec hV.fromSpec hs M).hom.app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  have hψ : Function.Bijective
      (sectionPullbackLE hU.fromSpec ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) hc) :=
    sectionPullbackLE_bijective_of_isOpenImmersion hU.fromSpec _ hU.opensRange_fromSpec.ge _
      hU.fromSpec_preimage_self
  have key : ∀ z,
      sectionPullbackLE hU.fromSpec ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        hc (pullbackTensorMap f M h z) =
      (squarePullbackIso f (Spec.map (f.appLE V U h)) hU.fromSpec hV.fromSpec hs M).hom.app ⊤
        (affineScalarSectionsMap (f.appLE V U h)
          ((AlgebraicGeometry.Scheme.Modules.pullback hV.fromSpec).obj M)
          ((ModuleCat.extendScalars (f.appLE V U h).hom).map (fromSpecSectionsLinear M hV) z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, sectionPullbackLE_add, ha, hb, map_add, map_add, map_add]
    | tmul s m =>
      have h1 : (ModuleCat.extendScalars (f.appLE V U h).hom).map (fromSpecSectionsLinear M hV)
          (s ⊗ₜ[Γ(Y, V), (f.appLE V U h).hom] m) =
          ((show Γ(X, U) from s) •
              ((1 : Γ(X, U)) ⊗ₜ[Γ(Y, V), (f.appLE V U h).hom] fromSpecSectionsLinear M hV m) :
            (ModuleCat.extendScalars (f.appLE V U h).hom).obj ((moduleSpecΓFunctor
              (R := Γ(Y, V))).obj
                ((AlgebraicGeometry.Scheme.Modules.pullback hV.fromSpec).obj M))) := by
        rw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.smul_tmul, mul_one]
      rw [h1, map_smul, moduleSpecΓFunctor_smul, Scheme.Modules.Hom.app_smul,
        affineScalarSectionsMap_one_tmul, affineSectionsPullbackMap_eq _ _ hT,
        fromSpecSectionsLinear_apply,
        squarePullbackIso_hom_sectionPullbackLE f (Spec.map (f.appLE V U h)) hU.fromSpec
          hV.fromSpec hs M hx h hT hc m]
      erw [pullbackTensorMap_tmul]
      rw [sectionPullbackLE_smul, isAffineOpen_fromSpec_appLE_top]
  have hcomp : Function.Bijective
      (sectionPullbackLE hU.fromSpec ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) hc ∘
        pullbackTensorMap f M h) := by
    rw [show sectionPullbackLE hU.fromSpec ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        hc ∘ pullbackTensorMap f M h = _ from funext key]
    exact hsq.comp (hσ.comp hTb)
  exact (Function.Bijective.of_comp_iff' hψ _).mp hcomp

end Bijective

end Langlands.Scheme.Modules
