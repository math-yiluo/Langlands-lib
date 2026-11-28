import Langlands.AbelianScheme.LieBaseChange
import Langlands.GroupScheme.Lie.FiniteLocalFrames
import Langlands.AlgebraicGeometry.Picard.MumfordProductEulerCharacteristic
import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeIsIso

/-! # Translation of the relative cotangent sheaf of an abelian scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CategoryTheory.Limits hiding pullback
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.Scheme AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The relative cotangent sheaf is the pullback of the cotangent sheaf at the
identity, via translation on the actual self-product. -/
def relativeDifferentialsIsoPullbackCotangent :
    relativeDifferentials A.X.hom ≅ (pullback A.X.hom).obj
      (GroupScheme.cotangentAtIdentity A.toGrp) := by
  let B := (baseChange A.X.hom).obj A
  let p := A.X.hom
  let P := Limits.pullback p p
  let p₁ := Limits.pullback.fst p p
  let p₂ := Limits.pullback.snd p p
  let j : A.X.left ⟶ P := GroupScheme.identitySection B.toGrp
  have hj₁ : j ≫ p₁ = p ≫ GroupScheme.identitySection A.toGrp :=
    GroupScheme.identitySection_baseChange_fst p A.toGrp
  have hj₂ : j ≫ p₂ = 𝟙 A.X.left := GroupScheme.identitySection_comp B.toGrp
  let jo : A.X ⟶ mumfordProduct A := Over.homMk j (by
    change j ≫ p₁ ≫ p = p
    rw [← Category.assoc, hj₁, Category.assoc, GroupScheme.identitySection_comp, Category.comp_id])
  have hjFirst : jo ≫ mumfordFirst A = 1 := by
    apply Over.OverMorphism.ext
    change j ≫ p₁ = (1 : A.X ⟶ A.X).left
    rw [hj₁]
    rfl
  have hjSecond : jo ≫ mumfordSecond A = 𝟙 A.X := by
    apply Over.OverMorphism.ext
    exact hj₂
  let t : P ≅ P := (Over.forget S).mapIso (mumfordShearIso A)
  have ht₁ : t.hom ≫ p₁ = mumfordAddition A := mumfordShear_left_fst A
  have ht₂ : t.hom ≫ p₂ = p₂ := mumfordShear_left_snd A
  have hjt₁ : (j ≫ t.hom) ≫ p₁ = 𝟙 A.X.left := by
    rw [Category.assoc, ht₁]
    change (jo ≫ (mumfordFirst A * mumfordSecond A)).left = _
    rw [MonObj.comp_mul, hjFirst, hjSecond, one_mul]
    rfl
  let Ω := relativeDifferentials p
  let Ω₂ := relativeDifferentials p₂
  let : IsIso (relativeDifferentialsBaseChangeMap p p) :=
    relativeDifferentialsBaseChangeIsIso S _ _ p p
  let d : (pullback p₁).obj Ω ≅ Ω₂ := asIso (relativeDifferentialsBaseChangeMap p p)
  have hw : t.hom ≫ p₂ = p₂ ≫ 𝟙 A.X.left := ht₂.trans (Category.comp_id p₂).symm
  let : IsIso (relativeDifferentialsSquareMap t.hom (𝟙 A.X.left) hw) :=
    relativeDifferentialsOpenImmersionIsIso P P _ _ p₂ p₂ t.hom (𝟙 A.X.left)
      inferInstance inferInstance hw
  let dt : (pullback t.hom).obj Ω₂ ≅ Ω₂ :=
    asIso (relativeDifferentialsSquareMap t.hom (𝟙 A.X.left) hw)
  let restrictJ : (pullback j).obj Ω₂ ≅ (pullback p).obj
      (GroupScheme.cotangentAtIdentity A.toGrp) :=
    (pullback j).mapIso d.symm ≪≫ (pullbackComp j p₁).app Ω ≪≫
      (pullbackCongr hj₁).app Ω ≪≫ (pullbackComp p (GroupScheme.identitySection A.toGrp)).symm.app Ω
  let restrictJT : (pullback (j ≫ t.hom)).obj Ω₂ ≅ Ω :=
    (pullback (j ≫ t.hom)).mapIso d.symm ≪≫ (pullbackComp (j ≫ t.hom) p₁).app Ω ≪≫
      (pullbackCongr hjt₁).app Ω ≪≫ (pullbackId A.X.left).app Ω
  exact restrictJT.symm ≪≫ (pullbackComp j t.hom).symm.app Ω₂ ≪≫ (pullback j).mapIso dt ≪≫ restrictJ

section LocalBase

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (B : AbelianScheme (Spec (CommRingCat.of R)))

/-- Over a local affine base the cotangent sheaf at the identity has a
finite free frame on the whole spectrum. -/
theorem exists_finiteFreeCotangentAtIdentity :
    ∃ κ : Type u, Finite κ ∧ Nonempty (
      SheafOfModules.free κ ≅ GroupScheme.cotangentAtIdentity B.toGrp) := by
  let T := Spec (CommRingCat.of R)
  let G : GroupScheme T := B.toGrp
  let M := G.cotangentAtIdentity
  obtain ⟨q, hq, hfin⟩ := G.cotangentAtIdentity_hasFiniteLocalBasis (show Smooth G.X.hom from inferInstance)
  have hclosed : IsLocalRing.closedPoint R ∈ ⨆ i, q.X i :=
    (_root_.Opens.coversTop_iff T q.X).mp q.coversTop ▸
      (show IsLocalRing.closedPoint R ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hclosed
  let κ := (q.generators i).I
  have htop : q.X i = ⊤ := by
    apply top_unique
    intro x _
    exact (IsLocalRing.specializes_closedPoint x).mem_open (q.X i).isOpen hi
  let : IsIso (q.generators i).π := hq.isIso i
  have hf : Finite κ := (hfin.isFiniteType i).finite
  have H : Nonempty (SheafOfModules.free (R := T.ringCatSheaf.over (⊤ : T.Opens)) κ ≅
      M.over (⊤ : T.Opens)) := by
    have H₀ : Nonempty (SheafOfModules.free (R := T.ringCatSheaf.over (q.X i)) κ ≅
        M.over (q.X i)) := ⟨asIso (q.generators i).π⟩
    exact htop ▸ H₀
  obtain ⟨e⟩ := H
  let W : T.Opens := ⊤
  let pres : PreservesColimitsOfShape (Discrete κ) (Scheme.Modules.overEquiv W).functor :=
    (Scheme.Modules.overEquiv W).toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  let e₁ : SheafOfModules.free (R := W.toScheme.ringCatSheaf) κ ≅ M.restrict W.ι :=
    @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ (Scheme.Modules.overEquiv W).functor κ pres
      (W.sheafOfModulesEquivOverUnit T.ringCatSheaf).symm ≪≫
      (Scheme.Modules.overEquiv W).functor.mapIso e ≪≫ (Scheme.Modules.overFunctorEquiv W).app M
  let j := T.topIso.inv
  let : (SheafOfModules.pushforward j.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction j).isRightAdjoint
  let e₂ : SheafOfModules.free (R := T.ringCatSheaf) κ ≅ M :=
    (SheafOfModules.pullbackObjFreeIso j.toRingCatSheafHom κ).symm ≪≫
      (pullback j).mapIso (e₁ ≪≫ (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M) ≪≫
      (pullbackComp j W.ι).app M ≪≫ (pullbackCongr (Scheme.toIso_inv_ι T)).app M ≪≫
      (pullbackId T).app M
  exact ⟨κ, hf, ⟨e₂⟩⟩

/-- A finite free frame of the cotangent sheaf at the identity over a local spectrum. -/
def finiteFreeCotangentFrame :
    Σ κ : Type u, Subtype (fun _ : SheafOfModules.free κ ≅ GroupScheme.cotangentAtIdentity B.toGrp =>
      Finite κ) :=
  let c := Classical.indefiniteDescription _ (exists_finiteFreeCotangentAtIdentity B)
  ⟨c.val, ⟨Classical.choice c.property.2, c.property.1⟩⟩

/-- Over a local affine base the translate of a cotangent frame at the
identity gives a finite free relative differential sheaf. -/
theorem exists_finiteFreeRelativeDifferentials :
    ∃ κ : Type u, Finite κ ∧ Nonempty (
      SheafOfModules.free (R := B.X.left.ringCatSheaf) κ ≅ relativeDifferentials B.X.hom) := by
  let c := finiteFreeCotangentFrame B
  let : (SheafOfModules.pushforward B.X.hom.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction B.X.hom).isRightAdjoint
  exact ⟨c.1, c.2.property, ⟨(SheafOfModules.pullbackObjFreeIso B.X.hom.toRingCatSheafHom c.1).symm ≪≫
    (pullback B.X.hom).mapIso c.2.val ≪≫ (relativeDifferentialsIsoPullbackCotangent B).symm⟩⟩

end LocalBase

end Langlands.AbelianScheme
