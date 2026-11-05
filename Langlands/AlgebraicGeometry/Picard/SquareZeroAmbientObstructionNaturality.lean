import Langlands.AlgebraicGeometry.Picard.UnitH1PullbackComposition
import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction

/-! # Actual Picard obstruction under a quotient of the ambient thickening -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2000

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroAmbientObstructionNaturality

open NilpotentUnitReduction SquareZeroUnitKernels StructureKernelModule
open SquareZeroUnitExactSequence SquareZeroUnitCohomology UnitSheafPushforward
open Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic

variable {X Y Z : Scheme.{u}} (b : Y ⟶ X) (j : Z ⟶ Y)

/-- Apply the actual ambient structure map to a section of the larger kernel. -/
def kernelModuleMap : kernelModule (j ≫ b) ⟶ (Scheme.Modules.pushforward b).obj (kernelModule j) :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun a ↦ ⟨(b.app U.unop).hom a.val, a.property⟩
          map_zero' := by apply Subtype.ext; exact map_zero _
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _ }
      naturality := by
        intro U V h
        ext a
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (b.c.naturality h) a.val }
    (by
      intro U r a
      apply Subtype.ext
      exact map_mul _ _ _)⟩

@[simp]
lemma kernelModuleMap_app (U : X.Opens) (a : Γ(kernelModule (j ≫ b), U)) :
    ((kernelModuleMap b j).app U a).val = (b.app U).hom a.val := rfl

/-- The same actual kernel map on underlying abelian sheaves, pushed to `X`. -/
def sequenceKernelMap :
    schemeAdditiveKernelSheaf (j ≫ b) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).obj (schemeAdditiveKernelSheaf j) :=
  (toAbSheaf X).map (kernelModuleMap b j)

/-- Reduction of ambient structure units along the actual quotient. -/
def sequenceMiddleMap :
    unitsSheaf X.presheaf X.sheaf.property ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).obj
        (unitsSheaf Y.presheaf Y.sheaf.property) :=
  unitsReduction b

/-- The inner unit sheaf is unchanged after composing the pushforwards. -/
def sequenceQuotientMap :
    unitsSheaf ((Opens.map (j ≫ b).base).op ⋙ Z.presheaf)
        (TopCat.Sheaf.pushforward_sheaf_of_sheaf (j ≫ b).base Z.sheaf.property) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).obj
        (unitsSheaf ((Opens.map j.base).op ⋙ Z.presheaf)
          (TopCat.Sheaf.pushforward_sheaf_of_sheaf j.base Z.sheaf.property)) :=
  𝟙 _

variable [IsClosedImmersion j] [IsClosedImmersion (j ≫ b)]
  (hj : j.ker ^ 2 = ⊥) (hjb : (j ≫ b).ker ^ 2 = ⊥)

lemma sequenceKernelMap_comm :
    sequenceKernelMap b j ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).map (schemeOneAdd j hj) =
      schemeOneAdd (j ≫ b) hjb ≫ sequenceMiddleMap b := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  apply Additive.toMul.injective
  apply Units.ext
  change 1 + (b.app U.unop).hom a.val = (b.app U.unop).hom (1 + a.val)
  rw [map_add, map_one]

omit [IsClosedImmersion j] [IsClosedImmersion (j ≫ b)] in
lemma sequenceQuotientMap_comm :
    sequenceMiddleMap b ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).map (unitsReduction j) =
      unitsReduction (j ≫ b) ≫ sequenceQuotientMap b j := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  rfl

/-- The actual morphism from the larger ambient unit sequence to the pushed quotient sequence. -/
def unitSequenceMap : schemeUnitSequence (j ≫ b) hjb ⟶
    (schemeUnitSequence j hj).map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base) :=
  ShortComplex.homMk (sequenceKernelMap b j) (sequenceMiddleMap b)
    (sequenceQuotientMap b j) (sequenceKernelMap_comm b j hj hjb)
    (sequenceQuotientMap_comm b j)

variable [IsClosedImmersion b] (hb : IsNilpotent b.ker)

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The actual ideal-cohomology comparison induced by quotienting the ambient ring. -/
def idealCohomologyMap (n : ℕ) :
    idealCohomology (j ≫ b) n →+ idealCohomology j n :=
  (idealCohomologyAddEquiv j n).toAddMonoidHom.comp
    ((cohomologyPushforwardEquiv (nilpotentClosedImmersionTopIso b hb)
      (schemeAdditiveKernelSheaf j) n).toAddMonoidHom.comp
        ((Sheaf.H.map (sequenceKernelMap b j) n).comp
          (idealCohomologyAddEquiv (j ≫ b) n).symm.toAddMonoidHom))

private lemma quotientCohomologyComparison (n : ℕ) (y : unitCohomology Z n) :
    cohomologyPushforwardEquiv (nilpotentClosedImmersionTopIso b hb)
        (unitsSheaf ((Opens.map j.base).op ⋙ Z.presheaf)
          (TopCat.Sheaf.pushforward_sheaf_of_sheaf j.base Z.sheaf.property)) n
        ((nilpotentUnitsCohomologyPushforwardEquiv (j ≫ b) ⟨2, hjb⟩ n).symm y) =
      (nilpotentUnitsCohomologyPushforwardEquiv j ⟨2, hj⟩ n).symm y := by
  apply (nilpotentUnitsCohomologyPushforwardEquiv j ⟨2, hj⟩ n).injective
  rw [AddEquiv.apply_symm_apply]
  have hc := cohomologyPushforwardEquiv_comp
    (nilpotentClosedImmersionTopIso j ⟨2, hj⟩)
    (nilpotentClosedImmersionTopIso b hb)
    (unitsSheaf Z.presheaf Z.sheaf.property) n
    ((nilpotentUnitsCohomologyPushforwardEquiv (j ≫ b) ⟨2, hjb⟩ n).symm y)
  have heq := UnitH1Pullback.nilpotentClosedImmersionTopIso_comp b j hb ⟨2, hjb⟩ ⟨2, hj⟩
  have hcongr (e e' : Z.toTopCat ≅ X.toTopCat) (h : e = e') :
      HEq (cohomologyPushforwardEquiv e (unitsSheaf Z.presheaf Z.sheaf.property) n)
        (cohomologyPushforwardEquiv e' (unitsSheaf Z.presheaf Z.sheaf.property) n) := by
    cases h
    rfl
  have hc' := eq_of_heq (hcongr
    (nilpotentClosedImmersionTopIso j ⟨2, hj⟩ ≪≫ nilpotentClosedImmersionTopIso b hb)
    (nilpotentClosedImmersionTopIso (j ≫ b) ⟨2, hjb⟩) heq)
  rw [hc'] at hc
  exact hc.trans ((nilpotentUnitsCohomologyPushforwardEquiv
    (j ≫ b) ⟨2, hjb⟩ n).apply_symm_apply y)

set_option maxHeartbeats 800000 in
/-- Actual unit-sequence boundaries commute with quotienting the ambient thickening. -/
lemma boundaryMap_naturality (n : ℕ) (y : unitCohomology Z n) :
    boundaryMap j hj n y =
      idealCohomologyMap b j hb (n + 1) (boundaryMap (j ≫ b) hjb n y) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base
  have : P.IsEquivalence :=
    (sheafPushforwardEquivalence (C := AddCommGrpCat.{u})
      (nilpotentClosedImmersionTopIso b hb)).isEquivalence_functor
  let a := (nilpotentUnitsCohomologyPushforwardEquiv (j ≫ b) ⟨2, hjb⟩ n).symm y
  have hd := Sheaf.H.δ_naturality n (n + 1) rfl
    (schemeUnitSequence_shortExact (j ≫ b) hjb)
    ((schemeUnitSequence_shortExact j hj).map_of_exact P)
    (unitSequenceMap b j hj hjb) a
  change Sheaf.H.δ ((schemeUnitSequence_shortExact j hj).map_of_exact P)
      n (n + 1) rfl (Sheaf.H.map (𝟙 _) n a) =
    Sheaf.H.map (sequenceKernelMap b j) (n + 1)
      (Sheaf.H.δ (schemeUnitSequence_shortExact (j ≫ b) hjb)
        n (n + 1) rfl a) at hd
  rw [Sheaf.H.map_id_apply] at hd
  have hp := cohomologyPushforwardEquiv_δ (nilpotentClosedImmersionTopIso b hb)
    (schemeUnitSequence_shortExact j hj) n (n + 1) rfl a
  dsimp only [schemeUnitSequence, a] at hp
  rw [quotientCohomologyComparison b j hj hjb hb n y] at hp
  change idealCohomologyAddEquiv j (n + 1)
      (Sheaf.H.δ (schemeUnitSequence_shortExact j hj) n (n + 1) rfl
        ((nilpotentUnitsCohomologyPushforwardEquiv j ⟨2, hj⟩ n).symm y)) =
    idealCohomologyAddEquiv j (n + 1)
    (cohomologyPushforwardEquiv (nilpotentClosedImmersionTopIso b hb)
      (schemeAdditiveKernelSheaf j) (n + 1)
      (Sheaf.H.map (sequenceKernelMap b j) (n + 1)
        ((idealCohomologyAddEquiv (j ≫ b) (n + 1)).symm
          (idealCohomologyAddEquiv (j ≫ b) (n + 1)
            (Sheaf.H.δ (schemeUnitSequence_shortExact (j ≫ b) hjb)
              n (n + 1) rfl a)))))
  rw [AddEquiv.symm_apply_apply]
  exact congrArg (idealCohomologyAddEquiv j (n + 1))
    (hp.symm.trans (congrArg
      (cohomologyPushforwardEquiv (nilpotentClosedImmersionTopIso b hb)
        (schemeAdditiveKernelSheaf j) (n + 1)) hd))

open SquareZeroPicardObstruction

variable [CompactSpace Z]

include hj hjb hb

/-- Quotienting the ambient thickening takes the actual Picard obstruction to its image. -/
lemma obstructionMap_naturality (y : Group Z) :
    obstructionMap j hj y =
      idealCohomologyMap b j hb 2 (obstructionMap (j ≫ b) hjb y) :=
  boundaryMap_naturality b j hj hjb hb 1 (Group.unitCohomologyAddEquiv Z y)

/-- Homomorphism form of ambient quotient naturality. -/
lemma obstructionMap_comp :
    obstructionMap j hj =
      (idealCohomologyMap b j hb 2).comp (obstructionMap (j ≫ b) hjb) := by
  ext y
  exact obstructionMap_naturality b j hj hjb hb y

/-- Ambient quotient preserves vanishing of the actual obstruction. -/
lemma obstructionMap_eq_zero (y : Group Z)
    (hy : obstructionMap (j ≫ b) hjb y = 0) :
    obstructionMap j hj y = 0 := by
  rw [obstructionMap_naturality b j hj hjb hb, hy, map_zero]

/-- An injective ideal H² comparison also reflects obstruction vanishing. -/
lemma obstructionMap_eq_zero_iff
    (h : Function.Injective (idealCohomologyMap b j hb 2)) (y : Group Z) :
    obstructionMap j hj y = 0 ↔ obstructionMap (j ≫ b) hjb y = 0 := by
  rw [obstructionMap_naturality b j hj hjb hb]
  exact h.eq_iff' (map_zero _)

variable [CompactSpace Y]

/-- A class lifts to the quotient ambient scheme precisely when the obstruction image vanishes. -/
lemma picard_lift_iff_image_obstruction (y : Group Z) :
    (∃ x : Group Y, Group.pullback j x = y) ↔
      idealCohomologyMap b j hb 2 (obstructionMap (j ≫ b) hjb y) = 0 := by
  rw [picard_lift_iff j hj, obstructionMap_naturality b j hj hjb hb]

/-- The same criterion retains an actual line bundle and an actual module-sheaf isomorphism. -/
lemma lineBundle_lift_iff_image_obstruction (L : LineBundle Z) :
    (∃ M : LineBundle Y, Nonempty (((LineBundle.pullback j).obj M).obj ≅ L.obj)) ↔
      idealCohomologyMap b j hb 2 (obstructionMap (j ≫ b) hjb L.classOf) = 0 := by
  rw [lineBundle_lift_iff j hj, obstructionMap_naturality b j hj hjb hb]

variable [CompactSpace X]

/-- An injective ideal H² comparison makes the two actual Picard lifting conditions equivalent. -/
lemma picard_lift_iff_of_injective
    (h : Function.Injective (idealCohomologyMap b j hb 2)) (y : Group Z) :
    (∃ x : Group Y, Group.pullback j x = y) ↔
      ∃ x : Group X, Group.pullback (j ≫ b) x = y := by
  rw [picard_lift_iff j hj, picard_lift_iff (j ≫ b) hjb]
  exact obstructionMap_eq_zero_iff b j hj hjb hb h y

end Langlands.AlgebraicGeometry.Picard.SquareZeroAmbientObstructionNaturality
