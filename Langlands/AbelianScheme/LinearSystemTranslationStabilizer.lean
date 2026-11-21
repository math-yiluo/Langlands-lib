import Langlands.AbelianScheme.AmpleGenericTranslationVanishingStatement
import Langlands.AbelianScheme.AmpleGenericTangentVanishingStatement
import Langlands.AbelianScheme.EndomorphismEulerDegree
import Langlands.AbelianScheme.SeparatingLineBundle.Assembly
import Langlands.AlgebraicGeometry.LinearSystem.CompleteGeneratingSystem
import Langlands.GroupScheme.TranslationStabilizer

/-! # Generic vanishing and translation stabilizers of complete linear systems -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped CategoryTheory.MonObj

noncomputable section

local notation "Specᵣ " K:arg => Spec (CommRingCat.of K)

namespace Langlands.AlgebraicGeometry.LinearSystem.CompleteGeneratingSystem

variable {K : Type u} [Field K] {X : Over (Specᵣ K)} {N : LineBundle X.left}

/-- The actual linear-system map, viewed in the category of schemes over the field. -/
def overMap (C : CompleteGeneratingSystem X.hom N) :
    X ⟶ Over.mk (projectiveSpaceToSpec K C.n) := Over.homMk C.map C.map_toSpec

@[simp]
lemma overMap_left (C : CompleteGeneratingSystem X.hom N) : C.overMap.left = C.map := rfl

end Langlands.AlgebraicGeometry.LinearSystem.CompleteGeneratingSystem

namespace Langlands.AbelianScheme

open Langlands.GroupScheme Langlands.GroupScheme.SeparatingLineBundle
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.LinearSystem

variable {K : Type u} [Field K] [IsAlgClosed K] (A : AbelianScheme (Specᵣ K))

/-- On an abelian variety over an algebraically closed field, rational generation provides a
complete generating basis. -/
lemma exists_completeGeneratingSystem_abelian (N : LineBundle A.X.left)
    (hgen : ∀ y : Over.mk (𝟙 (Specᵣ K)) ⟶ A.X,
      ∃ s : GlobalSections N.obj, ¬ VanishesAlong N y.left s) :
    Nonempty (CompleteGeneratingSystem A.X.hom N) := by
  have : Nonempty A.X.left := ⟨(1 : Over.mk (𝟙 (Specᵣ K)) ⟶ A.X).left
    (IsLocalRing.closedPoint K)⟩
  have : Module.Finite K ((relativeCohomology A.X.hom 0).obj N.obj) :=
    (EndomorphismEulerDegree.lineBundle_hasFiniteCohomology A.X.hom N).1 0
  let e := ((relativeCohomologyZeroIso A.X.hom).app N.obj).toLinearEquiv
  have : Module.Finite K ((relativeGlobalSections A.X.hom).obj N.obj) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact exists_completeGeneratingSystem A.X.hom N fun y hy ↦
    hgen (Over.homMk y (show y ≫ A.X.hom = 𝟙 _ from hy))

variable {A} {N : LineBundle A.X.left} (C : CompleteGeneratingSystem A.X.hom N)

/-- A rational translation that generically preserves vanishing of global sections belongs
to the scheme-theoretic stabilizer of the complete linear-system map. -/
lemma mem_linearSystem_stabilizer_of_generic_translation
    (a : Over.mk (𝟙 (Specᵣ K)) ⟶ A.X) (U : A.X.left.Opens) (hU : (U : Set A.X.left).Nonempty)
    (h : ∀ y : Over.mk (𝟙 (Specᵣ K)) ⟶ A.X, y.left (IsLocalRing.closedPoint K) ∈ U →
      ∀ s : GlobalSections N.obj, VanishesAlong N y.left s → VanishesAlong N (a * y).left s) :
    a ∈ (translationStabilizer (G := A.toGrp) C.overMap).carrier (Over.mk (𝟙 (Specᵣ K))) := by
  have : IsReduced A.X.left := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    K A.X.left A.X.hom
  have : IrreducibleSpace A.X.left := irreducibleSpace_of_smooth_of_isProper A.toGrp
  have : IsSeparated (Over.mk (projectiveSpaceToSpec K C.n)).hom :=
    inferInstanceAs (IsSeparated (projectiveSpaceToSpec K C.n))
  apply (mem_translationStabilizer_iff_rational C.overMap a U (U.isOpen.dense hU)).2
  intro y hy
  change Over.mk (𝟙 (Specᵣ K)) ⟶ A.X at y
  have hu : toUnit (Over.mk (𝟙 (Specᵣ K))) = 𝟙 (Over.mk (𝟙 (Specᵣ K))) :=
    toUnit_unique _ _
  rw [hu, Category.id_comp, mul_comm y a]
  apply Over.OverMorphism.ext
  exact (C.comp_map_eq_of_rational_vanishing (Over.w y) (Over.w (a * y)) (h y hy)).symm

/-- A dual-number point at the unit that generically preserves vanishing of global sections
after translation belongs to the same stabilizer. -/
lemma mem_linearSystem_stabilizer_of_generic_tangent
    (t : Specᵣ (DualNumber K) ⟶ A.X.left)
    (ht : IsTangentVectorAt A.X.hom (1 : Over.mk (𝟙 (Specᵣ K)) ⟶ A.X).left t)
    (U : A.X.left.Opens) (hU : (U : Set A.X.left).Nonempty)
    (h : ∀ y : Over.mk (𝟙 (Specᵣ K)) ⟶ A.X, y.left (IsLocalRing.closedPoint K) ∈ U →
      ∀ s : GlobalSections N.obj, VanishesAlong N y.left s →
        VanishesAlong N (t ≫ (translation A.toGrp y).left) s) :
    (Over.homMk t ht.1 : Over.mk (dualNumberProjection K) ⟶ A.X) ∈
      (translationStabilizer (G := A.toGrp) C.overMap).carrier (Over.mk (dualNumberProjection K)) := by
  have : IsReduced A.X.left := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    K A.X.left A.X.hom
  have : IrreducibleSpace A.X.left := irreducibleSpace_of_smooth_of_isProper A.toGrp
  have : IsSeparated (Over.mk (projectiveSpaceToSpec K C.n)).hom :=
    inferInstanceAs (IsSeparated (projectiveSpaceToSpec K C.n))
  let T := Over.mk (dualNumberProjection K)
  let v : T ⟶ A.X := Over.homMk t ht.1
  change v ∈ (translationStabilizer (G := A.toGrp) C.overMap).carrier T
  apply (mem_translationStabilizer_iff_rational C.overMap v U (U.isOpen.dense hU)).2
  intro y hy
  have he : v ≫ translation A.toGrp y = (toUnit T ≫ y) * v := by
    rw [points_translation, show Over.mkIdTerminal.from T = toUnit T from toUnit_unique _ _]
  have ht' : IsTangentVectorAt A.X.hom y.left (t ≫ (translation A.toGrp y).left) := by
    constructor
    · rw [Category.assoc, Over.w, ht.1]
    · rw [← Category.assoc, ht.2, left_comp_translation, mul_one]
  rw [← he]
  apply Over.OverMorphism.ext
  simpa only [Over.comp_left, Over.toUnit_left, Over.mk_hom, Category.assoc] using!
    C.comp_map_eq_of_dualNumber_vanishing (Over.w y) ht' (h y hy)

/-- Both generic vanishing criteria reduce to triviality of the translation stabilizer
of each ample complete generating system. This reduction does not assume that any stabilizer
is étale. -/
theorem ampleGenericVanishings_of_trivial_linearSystem_stabilizers
    (htriv : ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Specᵣ K))
      (N : LineBundle A.X.left) (C : CompleteGeneratingSystem A.X.hom N),
      N.IsAmple → translationStabilizer (G := A.toGrp) C.overMap = ⊥) :
    AmpleGenericTranslationVanishingStatement.{u} ∧ AmpleGenericTangentVanishingStatement.{u} := by
  constructor
  · intro K _ _ A N hN hgen a U hU h
    obtain ⟨C⟩ := exists_completeGeneratingSystem_abelian A N hgen
    have ha := mem_linearSystem_stabilizer_of_generic_translation C a U hU h
    rw [htriv K A N C hN, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at ha
    exact ha
  · intro K _ _ A N hN hgen t ht U hU h
    obtain ⟨C⟩ := exists_completeGeneratingSystem_abelian A N hgen
    have hv := mem_linearSystem_stabilizer_of_generic_tangent C t ht.1 U hU h
    rw [htriv K A N C hN, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hv
    have hconst : (1 : Over.mk (dualNumberProjection K) ⟶ A.X) =
        toUnit (Over.mk (dualNumberProjection K)) ≫ (1 : Over.mk (𝟙 (Specᵣ K)) ⟶ A.X) :=
      (MonObj.comp_one _).symm
    apply ht.2
    rw [hconst] at hv
    exact congrArg (fun a : Over.mk (dualNumberProjection K) ⟶ A.X ↦ a.left) hv

end Langlands.AbelianScheme
