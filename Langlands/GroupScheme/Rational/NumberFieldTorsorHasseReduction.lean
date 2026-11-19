import Langlands.GroupScheme.CocycleTorsor
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction

/-! # Torsor rational points and the number-field Hasse kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Cocycle

variable {S S' : Scheme.{u}} {G : GroupScheme S} {U X : Over S} [ModObj G.X X]

/-- A trivialization over the new base gives a point of the torsor over that base. -/
theorem exists_point_of_baseChange_isTrivial (ξ : Cocycle G U) (u : U ⟶ X)
    (hu : ∀ {Z : Over S} (a c : Z ⟶ U), ξ.toFun a c • (c ≫ u) = a ≫ u)
    (b : S' ⟶ S) (V : Over S') (r : (Over.map b).obj V ⟶ U) [EffectiveEpi V.hom]
    (h : (ξ.baseChange b V r).IsTrivial) : ∃ x : S' ⟶ X.left, x ≫ X.hom = b := by
  obtain ⟨f, hf⟩ := ξ.exists_of_baseChange_isTrivial b V r h
  let v : (Over.map b).obj V ⟶ X := f⁻¹ • (r ≫ u)
  have hv {T : Scheme.{u}} (a c : T ⟶ V.left) (he : a ≫ V.hom = c ≫ V.hom) :
      a ≫ v.left = c ≫ v.left := by
    let Z : Over S := Over.mk (a ≫ V.hom ≫ b)
    let a' : Z ⟶ (Over.map b).obj V := Over.homMk a rfl
    let c' : Z ⟶ (Over.map b).obj V := Over.homMk c (by
      change c ≫ V.hom ≫ b = a ≫ V.hom ≫ b
      rw [← Category.assoc, ← he, Category.assoc])
    have hact : (a' ≫ f)⁻¹ • ((a' ≫ r) ≫ u) = (c' ≫ f)⁻¹ • ((c' ≫ r) ≫ u) := by
      rw [← hu (a' ≫ r) (c' ≫ r), hf a' c' he, smul_smul,
        ← mul_assoc, inv_mul_cancel, one_mul]
    have key : a' ≫ v = c' ≫ v := by
      simpa only [v, ModObj.comp_smul, GrpObj.comp_inv, Category.assoc] using hact
    exact congrArg (fun m => m.left) key
  let x := EffectiveEpi.desc V.hom v.left hv
  refine ⟨x, ?_⟩
  apply (cancel_epi V.hom).mp
  rw [← Category.assoc, show V.hom ≫ x = v.left from EffectiveEpi.fac _ _ _]
  exact Over.w v

end Cocycle

/-- The local-to-global rational-point assertion for affine smooth torsors of `G`. -/
def NumberFieldTorsorHasseFor (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of F))) (_ : ModObj G.X X),
    IsIso (ModObj.leftSMul G.X X) → IsAffine X.left → Smooth X.hom → Surjective X.hom →
    (∀ v : Global.Place F,
      ∃ x : Spec (CommRingCat.of (Global.placeCompletion F v)) ⟶ X.left,
        x ≫ X.hom = algebraBaseMap F (Global.placeCompletion F v)) →
    ∃ x : Spec (CommRingCat.of F) ⟶ X.left, x ≫ X.hom = 𝟙 _

/-- The rational-point form of the arithmetic Hasse theorem for simply connected torsors. -/
def NumberFieldSimplyConnectedTorsorHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G → NumberFieldTorsorHasseFor F G

/-- The rational-point form of the arithmetic Hasse theorem for adjoint torsors. -/
def NumberFieldAdjointTorsorHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsAdjoint G → NumberFieldTorsorHasseFor F G

private theorem isTrivial_of_torsorHasse
    {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsSemisimple G)
    (h : NumberFieldTorsorHasseFor F G) (ξ : Cocycle G (Over.mk (algebraBaseMap F L)))
    (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  let U := Over.mk (algebraBaseMap F L)
  let ξ' : Cocycle G U := ξ
  have hξ' : ξ'.LocallyTrivial := hξ
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc F L
  let : Surjective U.hom := hs
  let : Flat U.hom := hf
  let : QuasiCompact U.hom := hqc
  let : IsAffine U.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of L)))
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let X := CocycleTorsor.torsor ξ'
  let : ModObj G.X X := CocycleTorsor.modObj ξ'
  have hX : IsIso (ModObj.leftSMul G.X X) := CocycleTorsor.isIso_leftSMul ξ'
  let u := CocycleTorsor.point ξ'
  have hu {Z : Over (Spec (CommRingCat.of F))} (a c : Z ⟶ U) :
      ξ'.toFun a c • (c ≫ u) = a ≫ u := CocycleTorsor.toFun_smul_point ξ' a c
  have hl (v : Global.Place F) :
      ∃ x : Spec (CommRingCat.of (Global.placeCompletion F v)) ⟶ X.left,
        x ≫ X.hom = algebraBaseMap F (Global.placeCompletion F v) := by
    let b := algebraBaseMap F (Global.placeCompletion F v)
    let V := (Over.pullback b).obj U
    let : Surjective V.hom := inferInstanceAs (Surjective (pullback.snd U.hom b))
    let : Flat V.hom := inferInstanceAs (Flat (pullback.snd U.hom b))
    let : QuasiCompact V.hom := inferInstanceAs (QuasiCompact (pullback.snd U.hom b))
    exact ξ'.exists_point_of_baseChange_isTrivial u (fun a c => hu a c) b V
      ((Over.mapPullbackAdj b).counit.app U) (hξ' v)
  obtain ⟨x, hx⟩ := h X (CocycleTorsor.modObj ξ') hX
    (inferInstanceAs (IsAffine (CocycleTorsor.torsor ξ').left))
    (CocycleTorsor.smooth_hom ξ') (CocycleTorsor.surjective_hom ξ') hl
  exact ξ'.isTrivial_of_torsor_section hX u (fun a c => hu a c) x hx

/-- The simply connected torsor theorem gives the kernel on each actual finite Galois cover. -/
theorem numberFieldSimplyConnectedGaloisHasseKernel_of_torsor
    (h : NumberFieldSimplyConnectedTorsorHasseStatement.{u}) :
    NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ hξ
  exact isTrivial_of_torsorHasse hG.isSemisimple (h F G hG) ξ hξ

/-- The adjoint torsor theorem gives the kernel on each actual finite Galois cover. -/
theorem numberFieldAdjointGaloisHasseKernel_of_torsor
    (h : NumberFieldAdjointTorsorHasseStatement.{u}) :
    NumberFieldAdjointGaloisHasseKernelStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ hξ
  exact isTrivial_of_torsorHasse hG.isSemisimple (h F G hG) ξ hξ

end Langlands.GroupScheme
