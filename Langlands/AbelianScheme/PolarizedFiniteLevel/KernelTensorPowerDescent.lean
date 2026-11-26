import Langlands.AbelianScheme.PolarizedFiniteLevel.KernelScalarCocycle
import Langlands.AbelianScheme.PolarizedFiniteLevel.KernelTranslationPower
import Langlands.AlgebraicGeometry.Modules.LineBundleDescentEffectiveProof
import Langlands.AbelianScheme.IsogenySpecialization

/-! # Effective descent of a tensor power along an isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.KernelTranslation

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {A B : AbelianScheme S} (q : A ⟶ B)

private abbrev qOver : A.X ⟶ B.X := (groupHom q).hom.hom

private def difference {T : Over S} (x y : T ⟶ A.X)
    (h : x ≫ qOver q = y ≫ qOver q) : T ⟶ (kernel q).X :=
  (GroupScheme.kernelPointsEquiv (groupHom q) T).symm
    ⟨x⁻¹ * y, by
      change (x⁻¹ * y) ≫ qOver q = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, h, inv_mul_cancel]⟩

private lemma difference_inclusion {T : Over S} (x y : T ⟶ A.X)
    (h : x ≫ qOver q = y ≫ qOver q) : difference q x y h ≫ inclusion q = x⁻¹ * y :=
  congrArg Subtype.val ((GroupScheme.kernelPointsEquiv (groupHom q) T).apply_symm_apply _)

private lemma act_difference {T : Over S} (x y : T ⟶ A.X)
    (h : x ≫ qOver q = y ≫ qOver q) : act q x (difference q x y h) = y := by
  rw [act, difference_inclusion, mul_inv_cancel_left]

private lemma difference_precomp {T U : Over S} (a : U ⟶ T) (x y : T ⟶ A.X)
    (h : x ≫ qOver q = y ≫ qOver q) (h' : (a ≫ x) ≫ qOver q = (a ≫ y) ≫ qOver q) :
    difference q (a ≫ x) (a ≫ y) h' = a ≫ difference q x y h := by
  apply (cancel_mono (inclusion q)).mp
  rw [difference_inclusion, Category.assoc, difference_inclusion, MonObj.comp_mul, GrpObj.comp_inv]

private lemma difference_mul {T : Over S} (x y z : T ⟶ A.X)
    (h : x ≫ qOver q = y ≫ qOver q) (h' : y ≫ qOver q = z ≫ qOver q)
    (h'' : x ≫ qOver q = z ≫ qOver q) :
    difference q x y h * difference q y z h' = difference q x z h'' := by
  apply (cancel_mono (inclusion q)).mp
  rw [MonObj.mul_comp, difference_inclusion, difference_inclusion, difference_inclusion,
    mul_assoc, mul_inv_cancel_left]

variable {q} {L : LineBundle A.X.left} (α : Lift q L)
  (b : Γ((kernel q).X.left, ⊤)ˣ) (n : ℕ)

private abbrev coefficient {T : Over S} (k : T ⟶ (kernel q).X) : Γ(T.left, ⊤)ˣ :=
  Units.map k.left.appTop.hom.toMonoidHom b

private lemma coefficient_precomp {T U : Over S} (a : U ⟶ T) (k : T ⟶ (kernel q).X) :
    coefficient b (a ≫ k) = Units.map a.left.appTop.hom.toMonoidHom (coefficient b k) := by
  apply Units.ext
  change (a.left ≫ k.left).appTop _ = a.left.appTop (k.left.appTop _)
  rw [Scheme.Hom.comp_appTop]
  rfl

private def corrected {T : Over S} (x y : T ⟶ A.X) (h : x ≫ qOver q = y ≫ qOver q) :
    (Scheme.Modules.pullback x.left).obj (tensorPow L.obj n) ⟶
      (Scheme.Modules.pullback y.left).obj (tensorPow L.obj n) :=
  let k := difference q x y h
  (coefficient b k : Γ(T.left, ⊤)) • pullbackPowerMap n (step α k x y (act_difference q x y h))

private instance corrected_isIso {T : Over S} (x y : T ⟶ A.X) (h : x ≫ qOver q = y ≫ qOver q) :
    IsIso (corrected α b n x y h) := by
  let k := difference q x y h
  let r := coefficient b k
  let f := pullbackPowerMap n (step α k x y (act_difference q x y h))
  refine ⟨⟨(↑(r⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • inv f, ?_, ?_⟩⟩
  · change ((r : Γ(T.left, ⊤)) • f) ≫ ((↑(r⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • inv f) = _
    rw [Linear.smul_comp, Linear.comp_smul, ← mul_smul, IsIso.hom_inv_id, Units.mul_inv, one_smul]
  · change ((↑(r⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • inv f) ≫ ((r : Γ(T.left, ⊤)) • f) = _
    rw [Linear.smul_comp, Linear.comp_smul, ← mul_smul, IsIso.inv_hom_id, Units.inv_mul, one_smul]

private lemma corrected_precomp {T U : Over S} (a : U ⟶ T) (x y : T ⟶ A.X)
    (h : x ≫ qOver q = y ≫ qOver q) (h' : (a ≫ x) ≫ qOver q = (a ≫ y) ≫ qOver q) :
    transport a.left (u' := (a ≫ x).left) (v' := (a ≫ y).left) rfl rfl (corrected α b n x y h) =
      corrected α b n (a ≫ x) (a ≫ y) h' := by
  let k := difference q x y h
  have hk : act q (a ≫ x) (a ≫ k) = a ≫ y := by
    rw [← difference_precomp q a x y h h', act_difference]
  have hh := step_precomp α a k x y (act_difference q x y h) hk
  unfold corrected
  dsimp only
  have hc := difference_precomp q a x y h h'
  have he : step α (difference q (a ≫ x) (a ≫ y) h') (a ≫ x) (a ≫ y)
      (act_difference q (a ≫ x) (a ≫ y) h') = step α (a ≫ k) (a ≫ x) (a ≫ y) hk := by
    congr 1
  rw [transport_smul, ← pullbackPowerMap_transport, hh, he, hc, coefficient_precomp]
  rfl

private lemma scaled_power_comp {U X : Scheme.{u}} {M : X.Modules} {x y z : U ⟶ X}
    (n : ℕ) (f : (Scheme.Modules.pullback x).obj M ⟶ (Scheme.Modules.pullback y).obj M)
    (g : (Scheme.Modules.pullback y).obj M ⟶ (Scheme.Modules.pullback z).obj M)
    (j : (Scheme.Modules.pullback x).obj M ⟶ (Scheme.Modules.pullback z).obj M)
    (r s c t : Γ(U, ⊤)) (h : f ≫ g = c • j) (ht : r * s * c ^ n = t) :
    (r • pullbackPowerMap n f) ≫ (s • pullbackPowerMap n g) = t • pullbackPowerMap n j := by
  rw [Linear.smul_comp, Linear.comp_smul, ← mul_smul, ← pullbackPowerMap_comp, h,
    pullbackPowerMap_smul, ← mul_smul, ht]

set_option maxHeartbeats 1500000 in
private lemma corrected_comp
    (hb : ∀ {T : Over S} (k l : T ⟶ (kernel q).X), coefficient b (k * l) =
      coefficient b k * coefficient b l * scalar α k l ^ n)
    {T : Over S} (x y z : T ⟶ A.X) (h : x ≫ qOver q = y ≫ qOver q)
    (h' : y ≫ qOver q = z ≫ qOver q) (h'' : x ≫ qOver q = z ≫ qOver q) :
    corrected α b n x y h ≫ corrected α b n y z h' = corrected α b n x z h'' := by
  let k := difference q x y h
  let l := difference q y z h'
  let m := difference q x z h''
  have hkl : k * l = m := difference_mul q x y z h h' h''
  have hz : act q x (k * l) = z := by rw [hkl, act_difference]
  have ht : step α (k * l) x z hz = step α m x z (act_difference q x z h'') := by
    congr 1
  let f := step α k x y (act_difference q x y h)
  let g := step α l y z (act_difference q y z h')
  let j := step α m x z (act_difference q x z h'')
  have hs : f ≫ g = (scalar α k l : Γ(T.left, ⊤)) • j :=
    (step_comp α k l x y z (act_difference q x y h) (act_difference q y z h') hz).trans
      (congrArg ((scalar α k l : Γ(T.left, ⊤)) • ·) ht)
  have hc : coefficient b k * coefficient b l * scalar α k l ^ n = coefficient b m :=
    (hb k l).symm.trans (congrArg (coefficient b) hkl)
  have hd : (coefficient b k : Γ(T.left, ⊤)) * (coefficient b l : Γ(T.left, ⊤)) *
      (scalar α k l : Γ(T.left, ⊤)) ^ n = coefficient b m := congrArg Units.val hc
  exact @scaled_power_comp T.left A.X.left L.obj x.left y.left z.left n f g j _ _ _ _ hs hd

variable (q) in
private lemma base_eq {U : Scheme.{u}} {x y : U ⟶ A.X.left} (h : x ≫ hom q = y ≫ hom q) :
    x ≫ A.X.hom = y ≫ A.X.hom := by
  simpa only [Category.assoc, Over.w (qOver q)] using congrArg (· ≫ B.X.hom) h

variable (q) in
private abbrev pairBase : Over S := Over.mk (pullback.fst (hom q) (hom q) ≫ A.X.hom)

variable (q) in
private abbrev first : pairBase q ⟶ A.X := Over.homMk (pullback.fst (hom q) (hom q)) rfl

variable (q) in
private abbrev second : pairBase q ⟶ A.X :=
  Over.homMk (pullback.snd (hom q) (hom q)) (base_eq q pullback.condition.symm)

variable (q) in
private lemma pair_condition : first q ≫ qOver q = second q ≫ qOver q :=
  Over.OverMorphism.ext pullback.condition

private def datum {U : Scheme.{u}} (x y : U ⟶ A.X.left) (h : x ≫ hom q = y ≫ hom q) :
    (Scheme.Modules.pullback x).obj (tensorPow L.obj n) ≅
      (Scheme.Modules.pullback y).obj (tensorPow L.obj n) := by
  let f := corrected α b n (first q) (second q) (pair_condition q)
  let : IsIso f := corrected_isIso α b n (first q) (second q) (pair_condition q)
  let t := pullback.lift x y h
  have hx : t ≫ (first q).left = x := pullback.lift_fst _ _ _
  have hy : t ≫ (second q).left = y := pullback.lift_snd _ _ _
  let : IsIso (transport t hx hy f) := transport_isIso t hx hy f
  exact asIso (transport t hx hy f)

private lemma datum_precomp {U V : Scheme.{u}} (a : V ⟶ U) (x y : U ⟶ A.X.left)
    (h : x ≫ hom q = y ≫ hom q) (h' : (a ≫ x) ≫ hom q = (a ≫ y) ≫ hom q) :
    (datum α b n (a ≫ x) (a ≫ y) h').hom =
      (Scheme.Modules.pullbackComp a x).inv.app (tensorPow L.obj n) ≫
        (Scheme.Modules.pullback a).map (datum α b n x y h).hom ≫
          (Scheme.Modules.pullbackComp a y).hom.app (tensorPow L.obj n) := by
  rw [← transport_rfl a]
  symm
  exact transport_transport_eq (pullback.lift x y h) a (by
    apply pullback.hom_ext <;> simp) _ _ rfl rfl _ _ _

private lemma datum_on_points {T : Over S} (x y : T ⟶ A.X) (h : x ≫ qOver q = y ≫ qOver q) :
    (datum α b n x.left y.left (congrArg CommaMorphism.left h)).hom = corrected α b n x y h := by
  let h' := congrArg CommaMorphism.left h
  let a : T ⟶ pairBase q := Over.homMk (pullback.lift x.left y.left h') (by
    change pullback.lift x.left y.left h' ≫ pullback.fst (hom q) (hom q) ≫ A.X.hom = T.hom
    rw [pullback.lift_fst_assoc, Over.w])
  have hx : a ≫ first q = x := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have hy : a ≫ second q = y := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  -- Transport along the two chosen projection equations is the same comparison.
  have hs (x' y' : T ⟶ A.X) (hx' : a ≫ first q = x') (hy' : a ≫ second q = y')
      (hxy' : x' ≫ qOver q = y' ≫ qOver q) :
      transport a.left (congrArg CommaMorphism.left hx') (congrArg CommaMorphism.left hy')
        (corrected α b n (first q) (second q) (pair_condition q)) = corrected α b n x' y' hxy' := by
    cases hx'
    cases hy'
    exact corrected_precomp α b n a (first q) (second q) (pair_condition q) hxy'
  exact hs x y hx hy h

private lemma datum_comp
    (hb : ∀ {T : Over S} (k l : T ⟶ (kernel q).X), coefficient b (k * l) =
      coefficient b k * coefficient b l * scalar α k l ^ n)
    {U : Scheme.{u}} (x y z : U ⟶ A.X.left) (h : x ≫ hom q = y ≫ hom q)
    (h' : y ≫ hom q = z ≫ hom q) (h'' : x ≫ hom q = z ≫ hom q) :
    (datum α b n x y h).hom ≫ (datum α b n y z h').hom = (datum α b n x z h'').hom := by
  let T := Over.mk (x ≫ A.X.hom)
  let x' : T ⟶ A.X := Over.homMk x rfl
  let y' : T ⟶ A.X := Over.homMk y (base_eq q h.symm)
  let z' : T ⟶ A.X := Over.homMk z (base_eq q h''.symm)
  have hxy : x' ≫ qOver q = y' ≫ qOver q := Over.OverMorphism.ext h
  have hyz : y' ≫ qOver q = z' ≫ qOver q := Over.OverMorphism.ext h'
  have hxz : x' ≫ qOver q = z' ≫ qOver q := Over.OverMorphism.ext h''
  exact (congrArg₂ (· ≫ ·) (datum_on_points α b n x' y' hxy)
    (datum_on_points α b n y' z' hyz)).trans
      ((corrected_comp α b n hb x' y' z' hxy hyz hxz).trans (datum_on_points α b n x' z' hxz).symm)

/-- An isomorphism along universal kernel translation gives effective descent of its `n`th
power when the full kernel is killed by `n` and the ground field is algebraically closed. -/
theorem exists_descended_power {K : Type u} [Field K] [IsAlgClosed K]
    {A B : AbelianScheme (Spec (CommRingCat.of K))} (q : A ⟶ B) (hq : IsIsogeny q)
    {L : LineBundle A.X.left} (α : Lift q L) (n : ℕ)
    (h : ∀ {T : Over (Spec (CommRingCat.of K))} (k : T ⟶ (kernel q).X), k ^ n = 1) :
    ∃ M : LineBundle B.X.left, Nonempty ((LineBundle.pullback (hom q)).obj M ≅
      (⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne _ L n⟩ : LineBundle A.X.left)) := by
  have hfin : IsFinite (kernel q).X.hom :=
    MorphismProperty.of_isPullback (GroupScheme.kernel_isPullback_scheme (groupHom q)) hq.1
  let : IsAffineHom (kernel q).X.hom := by infer_instance
  let : IsFinite (hom q) := hq.1
  let c : GroupScheme.UnitTwoCocycle (kernel q) := ⟨scalar α, scalar_precomp α, scalar_cocycle α⟩
  obtain ⟨b, hb⟩ := c.exists_correction_of_exponent n h
  obtain ⟨M, hM, ⟨e⟩⟩ := lineBundleDescentEffective _ _ (hom q) inferInstance hq.2.1 hq.2.2
    (tensorPow L.obj n) (tensorPow_isLocallyFreeRankOne _ L n) (fun _ => datum α b n)
    (fun _ _ => datum_precomp α b n) (fun _ => datum_comp α b n (fun {T} => hb T))
  exact ⟨⟨M, hM⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

end Langlands.AbelianScheme.KernelTranslation
