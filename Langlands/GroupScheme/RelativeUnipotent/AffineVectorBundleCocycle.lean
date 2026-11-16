import Langlands.GroupScheme.RelativeUnipotent.AffineSectionCoordinates
import Langlands.AlgebraicGeometry.AffineModuleCocycle
import Langlands.GroupScheme.TorsorCocycle

/-! # Affine cocycles in vector-bundle groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeUnipotent.AffineVectorBundleCocycle

open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.AffineAdditiveCocycle
open AffineSectionCoordinates

variable {S : Scheme.{u}} [IsAffine S] (M : S.Modules)

instance specOver_isAffine {C : CommRingCat.{u}} (φ : Γ(S, ⊤) ⟶ C) :
    IsAffine (specOver φ).left := inferInstanceAs (IsAffine (Spec C))

lemma specOver_appTop {C : CommRingCat.{u}} (φ : Γ(S, ⊤) ⟶ C) :
    (specOver φ).hom.appTop ≫ (Scheme.ΓSpecIso C).hom = φ := by
  have hS : S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(S, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop S]
    change S.isoSpec.inv.appTop ≫ S.isoSpec.hom.appTop = _
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp
  change (Spec.map φ ≫ S.isoSpec.inv).appTop ≫ _ = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, hS, Category.id_comp]

omit [IsAffine S] in
/-- The tensor restriction maps respect composition on all test schemes. -/
lemma tensorPullback_comp {T W Z : Over S} (a : Z ⟶ W) (b : W ⟶ T) (z : Points M T) :
    pullback M (a ≫ b) z = pullback M a (pullback M b z) := by
  let : Algebra Γ(S, ⊤) Γ(T.left, ⊤) :=
    (T.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul r m =>
      change (a ≫ b).left.appTop r ⊗ₜ[Γ(S, ⊤), (Z.hom.appLE ⊤ ⊤ le_top).hom] m =
        a.left.appTop (b.left.appTop r) ⊗ₜ[Γ(S, ⊤), (Z.hom.appLE ⊤ ⊤ le_top).hom] m
      rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Every test scheme maps naturally to the spectrum of its global functions. -/
def toAffine (T : Over S) : T ⟶ specOver T.hom.appTop :=
  Over.homMk T.left.toSpecΓ (by
    simp only [specOver, Over.mk_hom]
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id])

omit [IsAffine S] in
lemma point_compatibility {T U : Over S} (a : T ⟶ U) :
    U.hom.appTop ≫ a.left.appTop = T.hom.appTop := by
  rw [← Scheme.Hom.comp_appTop, Over.w a]

lemma toAffine_comp_specPoint {T U : Over S} [IsAffine U.left] (a : T ⟶ U) :
    toAffine T ≫ specPoint U T.hom.appTop a.left.appTop (point_compatibility a) = a := by
  apply Over.OverMorphism.ext
  change T.left.toSpecΓ ≫ Spec.map a.left.appTop ≫ U.left.isoSpec.inv = a.left
  rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- Natural additive cocycles with values in pullback sections of one sheaf. -/
structure SectionCocycle (U : Over S) where
  toFun : ∀ {Z : Over S}, (Z ⟶ U) → (Z ⟶ U) →
    GlobalSections ((Scheme.Modules.pullback Z.hom).obj M)
  naturality : ∀ {Z W : Over S} (t : W ⟶ Z) (a b : Z ⟶ U),
    toFun (t ≫ a) (t ≫ b) = sectionPullback M t (toFun a b)
  cocycle : ∀ {Z : Over S} (a b c : Z ⟶ U),
    toFun a c = toFun a b + toFun b c

namespace SectionCocycle

variable [M.IsQuasicoherent] {U : Over S} [IsAffine U.left] (α : SectionCocycle M U)

local instance coverAlgebra : Algebra Γ(S, ⊤) Γ(U.left, ⊤) := U.hom.appTop.hom.toAlgebra

omit [IsAffine S] [IsAffine U.left] in
/-- The structural ring maps commute with algebra points of the affine cover. -/
lemma algebraPoint_commutes
    (C : Type u) [CommRing C] [Algebra Γ(S, ⊤) C]
    (a : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] C) :
    U.hom.appTop ≫ CommRingCat.ofHom a.toRingHom =
      CommRingCat.ofHom (algebraMap Γ(S, ⊤) C) := by
  ext r
  exact a.commutes r

/-- Spectrum coordinates using an already supplied algebra structure. -/
def algebraCoordinates (C : Type u) [CommRing C] [Algebra Γ(S, ⊤) C] :
    Points M (specOver (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C))) ≃+
      C ⊗[Γ(S, ⊤)] GlobalSections M := by
  let φ : Γ(S, ⊤) ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)
  letI : Algebra Γ(S, ⊤) Γ(Spec (CommRingCat.of C), ⊤) :=
    ((specOver φ).hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let e : Γ(Spec (CommRingCat.of C), ⊤) ≃ₐ[Γ(S, ⊤)] C :=
    { (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        change (Scheme.ΓSpecIso (CommRingCat.of C)).hom
          ((specOver φ).hom.appLE ⊤ ⊤ le_top r) = φ r
        have htop : (specOver φ).hom.appLE ⊤ ⊤ le_top = (specOver φ).hom.appTop := by
          simp [Scheme.Hom.appLE]
        rw [htop]
        exact congrArg (fun f => f r) (specOver_appTop φ) }
  exact (TensorProduct.congr e.toLinearEquiv
    (LinearEquiv.refl Γ(S, ⊤) (GlobalSections M))).toAddEquiv

omit [M.IsQuasicoherent] in
@[simp]
lemma algebraCoordinates_tmul (C : Type u) [CommRing C] [Algebra Γ(S, ⊤) C]
    (r : Γ(Spec (CommRingCat.of C), ⊤)) (m : GlobalSections M) :
    algebraCoordinates M C
      (r ⊗ₜ[Γ(S, ⊤), ((specOver (CommRingCat.ofHom
        (algebraMap Γ(S, ⊤) C))).hom.appLE ⊤ ⊤ le_top).hom] m) =
      (Scheme.ΓSpecIso (CommRingCat.of C)).hom r ⊗ₜ[Γ(S, ⊤)] m := rfl

/-- The spectrum map of an algebra homomorphism over the affine base. -/
def algebraSpecMap {C D : Type u} [CommRing C] [CommRing D]
    [Algebra Γ(S, ⊤) C] [Algebra Γ(S, ⊤) D] (f : C →ₐ[Γ(S, ⊤)] D) :
    specOver (CommRingCat.ofHom (algebraMap Γ(S, ⊤) D)) ⟶
      specOver (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    have hφ : CommRingCat.ofHom (algebraMap Γ(S, ⊤) C) ≫ CommRingCat.ofHom f.toRingHom =
        CommRingCat.ofHom (algebraMap Γ(S, ⊤) D) := by
      ext r
      exact f.commutes r
    simp only [specOver, Over.mk_hom, ← Category.assoc, ← Spec.map_comp, hφ])

lemma algebraSpecMap_comp_specPoint {C D : Type u} [CommRing C] [CommRing D]
    [Algebra Γ(S, ⊤) C] [Algebra Γ(S, ⊤) D] (f : C →ₐ[Γ(S, ⊤)] D)
    (a : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] C) :
    algebraSpecMap f ≫ specPoint U _ (CommRingCat.ofHom a.toRingHom) (algebraPoint_commutes C a) =
      specPoint U _ (CommRingCat.ofHom (f.comp a).toRingHom) (algebraPoint_commutes D (f.comp a)) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ U.left.isoSpec.inv = _
  rw [← Spec.map_comp_assoc]
  rfl

omit [M.IsQuasicoherent] in
lemma algebraCoordinates_natural {C D : Type u} [CommRing C] [CommRing D]
    [Algebra Γ(S, ⊤) C] [Algebra Γ(S, ⊤) D] (f : C →ₐ[Γ(S, ⊤)] D)
    (z : Points M (specOver (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)))) :
    algebraCoordinates M D (pullback M (algebraSpecMap f) z) =
      Langlands.AlgebraicGeometry.AffineModuleCocycle.map Γ(S, ⊤) (GlobalSections M)
        f (algebraCoordinates M C z) := by
  let : Algebra Γ(S, ⊤) Γ(Spec (CommRingCat.of C), ⊤) :=
    ((specOver (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C))).hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul r m =>
      change (Scheme.ΓSpecIso (CommRingCat.of D)).hom
          ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop r) ⊗ₜ[Γ(S, ⊤)] m =
        f ((Scheme.ΓSpecIso (CommRingCat.of C)).hom r) ⊗ₜ[Γ(S, ⊤)] m
      exact congrArg (fun d => d ⊗ₜ[Γ(S, ⊤)] m)
        (congrArg (fun g => g r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom)))

/-- The section cocycle as an algebra-point function with module coefficients. -/
def algebraFun (C : Type u) [CommRing C] [Algebra Γ(S, ⊤) C]
    (a b : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] C) : C ⊗[Γ(S, ⊤)] GlobalSections M :=
  algebraCoordinates M C ((equiv M (specOver
    (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)))).symm
    (α.toFun (specPoint U _ (CommRingCat.ofHom a.toRingHom) (algebraPoint_commutes C a))
      (specPoint U _ (CommRingCat.ofHom b.toRingHom) (algebraPoint_commutes C b))))

lemma algebraFun_cocycle (C : Type u) [CommRing C] [Algebra Γ(S, ⊤) C]
    (a b c : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] C) :
    α.algebraFun M C a c = α.algebraFun M C a b + α.algebraFun M C b c := by
  rw [algebraFun, algebraFun, algebraFun,
    α.cocycle _ (specPoint U _ (CommRingCat.ofHom b.toRingHom) (algebraPoint_commutes C b)),
    map_add, map_add]

lemma algebraFun_natural {C D : Type u} [CommRing C] [CommRing D]
    [Algebra Γ(S, ⊤) C] [Algebra Γ(S, ⊤) D] (f : C →ₐ[Γ(S, ⊤)] D)
    (a b : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] C) :
    α.algebraFun M D (f.comp a) (f.comp b) =
      Langlands.AlgebraicGeometry.AffineModuleCocycle.map Γ(S, ⊤) (GlobalSections M)
        f (α.algebraFun M C a b) := by
  rw [algebraFun, algebraFun, ← algebraSpecMap_comp_specPoint f a,
    ← algebraSpecMap_comp_specPoint f b, α.naturality, equiv_symm_natural]
  exact algebraCoordinates_natural M f _

/-- The natural section cocycle in the published Amitsur coefficient interface. -/
def algebraCocycle : Langlands.AlgebraicGeometry.AffineModuleCocycle.Cocycle
    Γ(S, ⊤) Γ(U.left, ⊤) (GlobalSections M) where
  toFun := α.algebraFun M
  naturality := α.algebraFun_natural M
  cocycle := α.algebraFun_cocycle M

set_option maxHeartbeats 2400000 in
/-- A quasi-coherent section cocycle on an affine faithfully flat cover of an
  affine base is the coboundary of one section on the cover. -/
theorem exists_coboundary [Flat U.hom] [Surjective U.hom] :
    ∃ β : GlobalSections ((Scheme.Modules.pullback U.hom).obj M),
      ∀ {Z : Over S} (a b : Z ⟶ U),
        α.toFun a b = sectionPullback M a β - sectionPullback M b β := by
  have : Module.FaithfullyFlat Γ(S, ⊤) Γ(U.left, ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine U.hom).mp
      ⟨inferInstance, inferInstance⟩
  obtain ⟨β, hβ⟩ := (α.algebraCocycle M).exists_coboundary
  let gammaTensor := (algebraCoordinates M Γ(U.left, ⊤)).symm β
  let f := toSection M U (pullback M (toAffine U) gammaTensor)
  refine ⟨f, fun {Z} a b => ?_⟩
  let : Algebra Γ(S, ⊤) Γ(Z.left, ⊤) := Z.hom.appTop.hom.toAlgebra
  let aR : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z.left, ⊤) :=
    { toRingHom := a.left.appTop.hom
      commutes' := by
        intro r
        exact congrArg (fun g => g r) (point_compatibility a) }
  let bR : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z.left, ⊤) :=
    { toRingHom := b.left.appTop.hom
      commutes' := by
        intro r
        exact congrArg (fun g => g r) (point_compatibility b) }
  let a' := specPoint U Z.hom.appTop a.left.appTop (point_compatibility a)
  let b' := specPoint U Z.hom.appTop b.left.appTop (point_compatibility b)
  have hinv : (equiv M (specOver Z.hom.appTop)).symm (α.toFun a' b') =
      pullback M (algebraSpecMap aR) gammaTensor - pullback M (algebraSpecMap bR) gammaTensor := by
    apply (algebraCoordinates M Γ(Z.left, ⊤)).injective
    rw [map_sub, algebraCoordinates_natural, algebraCoordinates_natural]
    have hγ : algebraCoordinates M Γ(U.left, ⊤) gammaTensor = β := AddEquiv.apply_symm_apply _ _
    rw [hγ]
    exact hβ Γ(Z.left, ⊤) aR bR
  have hspec : α.toFun a' b' = toSection M (specOver Z.hom.appTop)
      (pullback M (algebraSpecMap aR) gammaTensor - pullback M (algebraSpecMap bR) gammaTensor) := by
    rw [← hinv]
    exact ((equiv M (specOver Z.hom.appTop)).apply_symm_apply _).symm
  have hnat := α.naturality (toAffine Z) a' b'
  have ha : toAffine Z ≫ a' = a := toAffine_comp_specPoint a
  have hb : toAffine Z ≫ b' = b := toAffine_comp_specPoint b
  rw [ha, hb] at hnat
  have ht (c : Z ⟶ U) (cR : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z.left, ⊤))
      (hc : cR.toRingHom = c.left.appTop.hom) :
      toAffine Z ≫ algebraSpecMap cR = c ≫ toAffine U := by
    apply Over.OverMorphism.ext
    change Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom cR.toRingHom) =
      c.left ≫ U.left.toSpecΓ
    rw [hc]
    exact (Scheme.toSpecΓ_naturality c.left).symm
  rw [hnat, hspec, ← toSection_natural, map_sub, map_sub]
  change toSection M Z (pullback M (toAffine Z) (pullback M (algebraSpecMap aR) gammaTensor)) -
      toSection M Z (pullback M (toAffine Z) (pullback M (algebraSpecMap bR) gammaTensor)) =
    sectionPullback M a (toSection M U (pullback M (toAffine U) gammaTensor)) -
      sectionPullback M b (toSection M U (pullback M (toAffine U) gammaTensor))
  rw [← toSection_natural, ← toSection_natural]
  have hp (c : Z ⟶ U) (cR : Γ(U.left, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z.left, ⊤))
      (hc : cR.toRingHom = c.left.appTop.hom) :
      pullback M (toAffine Z) (pullback M (algebraSpecMap cR) gammaTensor) =
        pullback M c (pullback M (toAffine U) gammaTensor) := by
    calc
      _ = pullback M (toAffine Z ≫ algebraSpecMap cR) gammaTensor :=
        (tensorPullback_comp M (toAffine Z) (algebraSpecMap cR) gammaTensor).symm
      _ = pullback M (c ≫ toAffine U) gammaTensor :=
        congrArg (fun k => pullback M k gammaTensor) (ht c cR hc)
      _ = _ := tensorPullback_comp M c (toAffine U) gammaTensor
  exact congrArg₂ (fun x y => toSection M Z x - toSection M Z y)
    (hp a aR rfl) (hp b bR rfl)

end SectionCocycle

/-- Every natural cocycle in an actual vector-bundle additive group is trivial
  on an affine flat surjective cover of an affine base. -/
theorem cocycle_isTrivial {V : GroupScheme S} (hV : IsVectorBundleAdditive V)
    {U : Over S} [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle V U) : ξ.IsTrivial := by
  obtain ⟨_, _, M, ⟨q, hq, _⟩, e, he⟩ := hV
  let := hq
  let : M.IsLocallyFree := q.isLocallyFree
  let α : SectionCocycle M U :=
    { toFun := fun a b => (e _ (ξ.toFun a b)).toAdd
      naturality := fun t a b => by
        rw [ξ.naturality]
        exact he _ _ t _
      cocycle := fun a b c => by
        rw [ξ.cocycle a b c, map_mul, toAdd_mul] }
  obtain ⟨β, hβ⟩ := α.exists_coboundary M
  refine ⟨(e U).symm (Multiplicative.ofAdd β), fun {Z} a b => ?_⟩
  apply (e Z).injective
  apply Multiplicative.toAdd.injective
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
    he, he, MulEquiv.apply_symm_apply, toAdd_ofAdd, ← sub_eq_add_neg]
  exact hβ a b

end Langlands.GroupScheme.RelativeUnipotent.AffineVectorBundleCocycle
