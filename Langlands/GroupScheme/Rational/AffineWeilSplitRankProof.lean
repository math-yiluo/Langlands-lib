import Langlands.GroupScheme.Rational.AffineWeilSplitRankStatement
import Langlands.GroupScheme.AffineWeilTorusAdjunction
import Langlands.GroupScheme.SplitComponent.AffineTargetBridge

/-! # Split rank and affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil.Rank

open SplitComponent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Lattices

variable (k : Type u) [Field k] {Λ : Type u} [AddCommGroup Λ]

/-- The universal character of the quotient by a subgroup of the lattice. -/
def quotientChar (M : AddSubgroup Λ) :
    (latticeFunctor (CommRingCat.of k) Λ).obj
      (latticeAlgebra (CommRingCat.of k) (Λ ⧸ M)) :=
  (univChar (CommRingCat.of k) (Λ ⧸ M)).comp
    (QuotientAddGroup.mk' M).toMultiplicative

theorem quotientChar_restrict (M : AddSubgroup Λ) :
    (latticeMap (R := CommRingCat.of k) M.subtype).app _ (quotientChar k M) = 1 := by
  apply MonoidHom.ext
  intro m
  change univChar (CommRingCat.of k) (Λ ⧸ M)
    (Multiplicative.ofAdd ((QuotientAddGroup.mk' M) m.toAdd.1)) = 1
  have h : (QuotientAddGroup.mk' M) m.toAdd.1 = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr m.toAdd.2
  rw [h]
  exact map_one _

theorem image_top_of_quotientChar_eq_one (M : AddSubgroup Λ)
    (h : quotientChar k M = 1) : M = ⊤ := by
  apply top_unique
  intro m _
  apply (QuotientAddGroup.eq_zero_iff m).mp
  have hm := congrArg (fun χ => (asChar χ (Multiplicative.ofAdd m) :
    AddMonoidAlgebra k (Λ ⧸ M))) h
  change AddMonoidAlgebra.single ((QuotientAddGroup.mk' M) m) (1 : k) =
    AddMonoidAlgebra.single (0 : Λ ⧸ M) (1 : k) at hm
  exact AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0) hm

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (d : (F ⋙ forget GrpCat).CorepresentableBy B)

theorem app_eq_one_of_image_restrict_eq_one
    (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F)
    (C : CommAlgCat.{u} (CommRingCat.of k))
    (χ : (latticeFunctor (CommRingCat.of k) Λ).obj C)
    (hχ : (latticeMap (R := CommRingCat.of k) (imageSubgroup d α).subtype).app C χ = 1) :
    α.app C χ = 1 := by
  rw [← latticeMap_comp_imageHom d α]
  change (imageHom d α).app C
    ((latticeMap (imageSubgroup d α).subtype).app C χ) = 1
  rw [hχ, map_one]

theorem classify_surjective_of_image_top
    (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F)
    (h : imageSubgroup d α = ⊤) :
    Function.Surjective (classify (latticeCorep _ Λ) d α).hom := by
  intro x
  apply (AlgHom.mem_range _).mp
  apply (mem_range_iff d α x).mpr
  intro m _
  rw [h]
  trivial

theorem classify_surjective_of_injective
    (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F)
    (hα : ∀ C, Function.Injective (α.app C)) :
    Function.Surjective (classify (latticeCorep _ Λ) d α).hom := by
  apply classify_surjective_of_image_top k d α
  apply image_top_of_quotientChar_eq_one k
  apply hα _
  rw [map_one]
  exact app_eq_one_of_image_restrict_eq_one k d α _ _
    (quotientChar_restrict k _)

end Lattices

section Adjunction

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of K)))
  {Λ : Type u} [AddCommGroup Λ]

/-- The right tensor inclusion, regarded as a map to a restricted algebra. -/
def rightInclusion (C : CommAlgCat.{u} (CommRingCat.of k)) :
    C ⟶ (restrictScalars k K).obj ((tensorFunctor k K).obj C) := by
  let j : C →+* K ⊗[k] C := Algebra.TensorProduct.includeRight.toRingHom
  letI : Algebra k (K ⊗[k] C) := Algebra.compHom _ (algebraMap k K)
  change C ⟶ CommAlgCat.of (CommRingCat.of k) (K ⊗[k] C)
  exact
  CommAlgCat.ofHom
    { j with
      commutes' := fun a => by
        change (1 : K) ⊗ₜ[k] (algebraMap k C a) = algebraMap k K a ⊗ₜ[k] (1 : C)
        simpa only [TensorProduct.smul_tmul', Algebra.smul_def, mul_one] using
          (TensorProduct.tmul_smul (R := k) a (1 : K) (1 : C)) }

theorem tensor_rightInclusion_multiplication (C : CommAlgCat.{u} (CommRingCat.of k)) :
    (tensorFunctor k K).map (rightInclusion k K C) ≫
      multiplication k ((tensorFunctor k K).obj C) = 𝟙 _ := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    change (multiplication k ((tensorFunctor k K).obj C)).hom
      (b ⊗ₜ[k] ((1 : K) ⊗ₜ[k] c)) = b ⊗ₜ[k] c
    rw [multiplication_tmul]
    change (b ⊗ₜ[k] (1 : C)) * ((1 : K) ⊗ₜ[k] c) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem unitTrans_counitTrans
    (α : latticeFunctor (CommRingCat.of k) Λ ⟶ pointFunctor k K G) :
    unitTrans k G (counitTrans k G α) = α := by
  ext C χ
  rw [unitTrans_app, counitTrans_app]
  have hn := ConcreteCategory.congr_hom (α.naturality (rightInclusion k K C)) χ
  change α.app _ ((latticeFunctor (CommRingCat.of k) Λ).map
      (rightInclusion k K C) χ) =
    G.affinePointMap ((tensorFunctor k K).map (rightInclusion k K C)) (α.app C χ) at hn
  change G.affinePointMap (multiplication k ((tensorFunctor k K).obj C))
    (α.app _ ((latticeFunctor (CommRingCat.of k) Λ).map
      (rightInclusion k K C) χ)) = _
  rw [hn]
  change ((G.affinePointMap (multiplication k ((tensorFunctor k K).obj C))).comp
    (G.affinePointMap ((tensorFunctor k K).map (rightInclusion k K C)))) (α.app C χ) = _
  rw [← GroupScheme.affinePointMap_comp, tensor_rightInclusion_multiplication,
    GroupScheme.affinePointMap_id]
  rfl

variable [IsAffine G.X.left]

theorem counit_classify_surjective
    (α : latticeFunctor (CommRingCat.of k) Λ ⟶ pointFunctor k K G)
    (hα : ∀ C, Function.Injective (α.app C)) :
    Function.Surjective
      (classify (latticeCorep (CommRingCat.of K) Λ)
        (AffineCoordinates.corepresentation G)
        (counitTrans k G α ≫ coordinatePointsTrans G)).hom := by
  let β := counitTrans k G α ≫ coordinatePointsTrans G
  let d := AffineCoordinates.corepresentation G
  let M := imageSubgroup d β
  apply classify_surjective_of_image_top K d β
  apply image_top_of_quotientChar_eq_one k M
  apply hα _
  rw [map_one]
  rw [← unitTrans_counitTrans k K G α]
  rw [unitTrans_app]
  apply (coordinatePointsEquiv G _).injective
  rw [map_one]
  change β.app _ ((latticeUnit k K).app _ (quotientChar k M)) = 1
  apply app_eq_one_of_image_restrict_eq_one K d β
  apply MonoidHom.ext
  intro m
  have hm := congrArg (fun χ => asChar χ m) (quotientChar_restrict k M)
  change asChar (quotientChar k M) (Multiplicative.ofAdd m.toAdd.1) = 1 at hm
  change Units.map _ (asChar (quotientChar k M) (Multiplicative.ofAdd m.toAdd.1)) = 1
  rw [hm, map_one]

end Adjunction

section Embeddings

variable {R : CommRingCat.{u}}
  {F F' : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B B' : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')

theorem natOfHom_injective
    (φ : Corepresented.groupScheme F e ⟶ Corepresented.groupScheme F' d)
    (hφ : IsClosedSubgroup φ) (C : CommAlgCat.{u} R) :
    Function.Injective ((natOfHom e d φ).app C) := by
  let : IsClosedImmersion φ.hom.hom.left := hφ
  let : Mono φ.hom.hom := Over.mono_of_mono_left _
  intro x y hxy
  apply (Corepresented.affinePointsEquiv F e C).symm.injective
  apply (cancel_mono φ.hom.hom).mp
  exact (Corepresented.affinePointsEquiv F' d C).injective hxy

theorem natToPoints_injective
    (G : GroupScheme (Spec R)) [IsAffine G.X.left]
    (φ : Corepresented.groupScheme F e ⟶ G) (hφ : IsClosedSubgroup φ)
    (C : CommAlgCat.{u} R) :
    Function.Injective ((natToPoints e φ).app C) := by
  let : IsClosedImmersion φ.hom.hom.left := hφ
  let : Mono φ.hom.hom := Over.mono_of_mono_left _
  intro x y hxy
  apply (Corepresented.affinePointsEquiv F e C).symm.injective
  exact (cancel_mono φ.hom.hom).mp hxy

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {Λ : Type u} [AddCommGroup Λ]

theorem latticeUnit_injective (C : CommAlgCat.{u} (CommRingCat.of k)) :
    Function.Injective ((latticeUnit k K (Λ := Λ)).app C) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro m
  apply Units.ext
  apply Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k K))
  exact congrArg (fun q => (asChar q m).val) h

variable [FiniteDimensional k K]
  (G : GroupScheme (Spec (CommRingCat.of K)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (I : Type u) [Finite I]

theorem exists_embedding_of_weil
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ groupScheme k K G)
    (hi : IsClosedSubgroup i) :
    ∃ j : splitTorus (Spec (CommRingCat.of K)) I ⟶ G, IsClosedSubgroup j := by
  let e := latticeCorep (CommRingCat.of k) (FreeAbelianGroup I)
  let eK := latticeCorep (CommRingCat.of K) (FreeAbelianGroup I)
  let d := corepresentableBy k K G
  let α := natOfHom e d ((torusIso (CommRingCat.of k) I).hom ≫ i)
  have hα : ∀ C, Function.Injective (α.app C) :=
    natOfHom_injective e d _ (hi.iso_comp (torusIso (CommRingCat.of k) I))
  have hβ := counit_classify_surjective k K G α hα
  have hj : IsClosedSubgroup
      (Corepresented.groupSchemeMap eK (AffineCoordinates.corepresentation G)
        (counitTrans k G α ≫ coordinatePointsTrans G)) :=
    isClosedSubgroup_groupSchemeMap eK (AffineCoordinates.corepresentation G) hβ
  exact ⟨(torusIso (CommRingCat.of K) I).inv ≫
      Corepresented.groupSchemeMap eK (AffineCoordinates.corepresentation G)
        (counitTrans k G α ≫ coordinatePointsTrans G) ≫
      (AffineCoordinates.groupSchemeIso G).hom,
    (hj.comp_iso (AffineCoordinates.groupSchemeIso G)).iso_comp
      (torusIso (CommRingCat.of K) I).symm⟩

theorem exists_weil_embedding
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ G)
    (hi : IsClosedSubgroup i) :
    ∃ j : splitTorus (Spec (CommRingCat.of k)) I ⟶ groupScheme k K G,
      IsClosedSubgroup j := by
  let e := latticeCorep (CommRingCat.of k) (FreeAbelianGroup I)
  let eK := latticeCorep (CommRingCat.of K) (FreeAbelianGroup I)
  let d := corepresentableBy k K G
  let β := natToPoints eK ((torusIso (CommRingCat.of K) I).hom ≫ i)
  have hβ : ∀ C, Function.Injective (β.app C) :=
    natToPoints_injective eK G _ (hi.iso_comp (torusIso (CommRingCat.of K) I))
  have hα : ∀ C, Function.Injective ((unitTrans k G β).app C) := by
    intro C x y h
    apply latticeUnit_injective k K C
    apply hβ _
    exact h
  have hj : IsClosedSubgroup (Corepresented.groupSchemeMap e d (unitTrans k G β)) :=
    isClosedSubgroup_groupSchemeMap e d
      (classify_surjective_of_injective k d (unitTrans k G β) hα)
  exact ⟨(torusIso (CommRingCat.of k) I).inv ≫
      Corepresented.groupSchemeMap e d (unitTrans k G β),
    hj.iso_comp (torusIso (CommRingCat.of k) I).symm⟩

end Embeddings

end Langlands.GroupScheme.AffineWeil.Rank

namespace Langlands.GroupScheme

/-- Borel–Tits 6.21(i), in the published supremum definition of split rank. -/
theorem affineWeilSplitRank : AffineWeilSplitRankStatement.{u} := by
  intro k K _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := hG.smooth
  apply le_antisymm
  · refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
    obtain ⟨j, hj⟩ := AffineWeil.Rank.exists_embedding_of_weil k K G I i hi
    exact card_le_splitRank I j hj
  · refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
    obtain ⟨j, hj⟩ := AffineWeil.Rank.exists_weil_embedding k K G I i hi
    exact card_le_splitRank I j hj

end Langlands.GroupScheme
