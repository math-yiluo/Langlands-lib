import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-!
# Points of closed immersions along injective algebra maps

Let `f : X → Y` be a closed immersion of algebraic spaces over `Spec C` and `φ : A → B` an
injective `C`-algebra map. A `B`-valued point of `X` whose image in `Y` comes from an
`A`-valued point of `Y` comes from an `A`-valued point of `X`: the pullback of `f` along the
`A`-point is a closed subscheme of `Spec A` through which `Spec B → Spec A` factors, and an
injective ring map has no kernel, so the closed subscheme is all of `Spec A`.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ClosedImmersionPoints

variable {C : Type u} [CommRing C] {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}

/-- `Spec` of an injective ring map is injective on global sections. -/
theorem injective_appTop_spec {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop := by
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ) := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
    exact hφ hab
  rw [← hn] at h2
  intro a b hab
  apply h2
  change (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom φ)).appTop a) =
    (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom φ)).appTop b)
  rw [hab]

/-- **Closed immersions along injective algebra maps.** -/
theorem exists_changeRing_eq (f : X ⟶ Y) (hf : IsClosedImmersion (hom f)) {A B : Type u}
    [CommRing A] [CommRing B] [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B)
    (hφ : Function.Injective φ) {x : RingPoints C X B} {y : RingPoints C Y A}
    (h : RingPoints.map f x = RingPoints.changeRing φ y) :
    ∃ x' : RingPoints C X A, RingPoints.changeRing φ x' = x ∧ RingPoints.map f x' = y := by
  have hr : IsRepresentableMorphism (hom f) := hf.1
  let a : (schemeYoneda _).obj (ringTest C A) ⟶ Y.presheaf := uliftYonedaEquiv.{u + 1}.symm y
  have hcl : _root_.AlgebraicGeometry.IsClosedImmersion (hr.snd a).left :=
    hf.2 a _ _ (hr.isPullback a)
  obtain ⟨p, hp₁, hp₂⟩ := exists_app_of_isPullback (hr.isPullback a) (ringTest C B) x
    (ULift.up (ringTestMap C φ)) h
  have hz : p.down ≫ hr.snd a = ringTestMap C φ := congrArg ULift.down hp₂
  have : IsAffine (ringTest C A).left := inferInstanceAs (IsAffine (Spec _))
  have hcomp : p.down.left ≫ (hr.snd a).left = Spec.map (CommRingCat.ofHom φ.toRingHom) :=
    congrArg CommaMorphism.left hz
  have hinj : Function.Injective (hr.snd a).left.appTop := by
    intro u v huv
    apply injective_appTop_spec φ.toRingHom hφ
    have e : (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop =
        (hr.snd a).left.appTop ≫ p.down.left.appTop := by
      rw [← Scheme.Hom.comp_appTop, hcomp]
      rfl
    rw [e]
    change p.down.left.appTop ((hr.snd a).left.appTop u) =
      p.down.left.appTop ((hr.snd a).left.appTop v)
    rw [huv]
  have : IsIso (hr.snd a).left :=
    _root_.AlgebraicGeometry.IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  let s : ringTest C A ⟶ hr.pullback a := Over.homMk (inv (hr.snd a).left) (by
    rw [IsIso.inv_comp_eq, ← Over.w (hr.snd a)])
  have hs : s ≫ hr.snd a = 𝟙 _ := by
    ext1
    simp [s]
  have hmono : Mono (hr.snd a) := by
    have : Mono (hr.snd a).left := inferInstance
    exact Over.mono_of_mono_left _
  have hzs : ringTestMap C φ ≫ s = p.down := by
    rw [← cancel_mono (hr.snd a), Category.assoc, hs, Category.comp_id, hz]
  let sp : ((schemeYoneda _).obj (hr.pullback a)).obj (op (ringTest C A)) := ULift.up s
  refine ⟨(hr.fst a).app (op (ringTest C A)) sp, ?_, ?_⟩
  · have hnat := NatTrans.naturality_apply (hr.fst a) (ringTestMap C φ).op sp
    refine hnat.symm.trans ?_
    rw [← hp₁]
    congr 1
    exact congrArg ULift.up hzs
  · have hw := congrArg (fun ψ => ψ.app (op (ringTest C A)) sp) (hr.isPullback a).w
    refine hw.trans ?_
    have h2 : ((schemeYoneda _).map (hr.snd a)).app (op (ringTest C A)) sp =
        (ULift.up (𝟙 (ringTest C A)) : ((schemeYoneda _).obj (ringTest C A)).obj
          (op (ringTest C A))) :=
      congrArg ULift.up hs
    change a.app _ (((schemeYoneda _).map (hr.snd a)).app (op (ringTest C A)) sp) = y
    rw [h2]
    exact uliftYonedaEquiv.{u + 1}.apply_symm_apply y

/-- A closed immersion is injective on points. -/
theorem map_injective (f : X ⟶ Y) (hf : IsClosedImmersion (hom f)) {B : Type u} [CommRing B]
    [Algebra C B] : Function.Injective (RingPoints.map f : RingPoints C X B → RingPoints C Y B) := by
  intro x₁ x₂ h
  have hr : IsRepresentableMorphism (hom f) := hf.1
  let a : (schemeYoneda _).obj (ringTest C B) ⟶ Y.presheaf :=
    uliftYonedaEquiv.{u + 1}.symm (RingPoints.map f x₁)
  have hcl : _root_.AlgebraicGeometry.IsClosedImmersion (hr.snd a).left :=
    hf.2 a _ _ (hr.isPullback a)
  have ha : a.app (op (ringTest C B)) (ULift.up (𝟙 _)) = RingPoints.map f x₁ :=
    uliftYonedaEquiv.{u + 1}.apply_symm_apply _
  obtain ⟨p₁, hp₁, hq₁⟩ := exists_app_of_isPullback (hr.isPullback a) (ringTest C B) x₁
    (ULift.up (𝟙 _)) ha.symm
  obtain ⟨p₂, hp₂, hq₂⟩ := exists_app_of_isPullback (hr.isPullback a) (ringTest C B) x₂
    (ULift.up (𝟙 _)) (ha.trans h).symm
  have hmono : Mono (hr.snd a) := by
    have : Mono (hr.snd a).left := inferInstance
    exact Over.mono_of_mono_left _
  have h₁ : p₁.down ≫ hr.snd a = 𝟙 _ := congrArg ULift.down hq₁
  have h₂ : p₂.down ≫ hr.snd a = 𝟙 _ := congrArg ULift.down hq₂
  have hp : p₁ = p₂ := congrArg ULift.up ((cancel_mono (hr.snd a)).mp (h₁.trans h₂.symm))
  rw [← hp₁, ← hp₂, hp]

end ClosedImmersionPoints

end Langlands.AlgebraicGeometry.AlgebraicSpace
