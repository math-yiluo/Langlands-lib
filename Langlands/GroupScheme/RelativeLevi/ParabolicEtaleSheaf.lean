import Langlands.GroupScheme.RelativeLevi.ParabolicAffineEtaleMatching
import Langlands.GroupScheme.RelativeLevi.ParabolicSheaf
import Langlands.AlgebraicGeometry.Sites.OverFppfSheaf
import Langlands.AlgebraicGeometry.Sites.EtaleFppfComparison

/-! # Étale sheafness and effective descent of actual parabolic families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} (G : GroupScheme S) (hG : IsReductive G)

/-- The affine surjective étale singleton sheaf condition is ordinary
matching and unique descent of actual parabolic families. -/
theorem parabolic_isSheafFor_affineEtale {M T : Over S} (a : M ⟶ T)
    [IsAffine T.left] [IsAffine M.left] [Etale a.left] [Surjective a.left] :
    Presieve.IsSheafFor (parabolicPresheaf G hG) (.singleton a) := by
  apply Presieve.isSheafFor_singleton.mpr
  intro F hF
  exact existsUnique_restrict_affineEtale hG a F (fun V b c hab => hF b c hab)

/-- Actual relative parabolic subgroup functors form a sheaf on the big
étale slice, with no affine or quasi-compact restriction on tests or covers. -/
theorem parabolic_isSheaf_etale :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) (parabolicPresheaf G hG) := by
  let P := parabolicPresheaf G hG
  let : Scheme.etaleTopology.Subcanonical :=
    .of_le Langlands.AlgebraicGeometry.Sites.etaleTopology_le_fppfTopology
  apply Langlands.AlgebraicGeometry.OverFppfSheaf.isSheaf_over_of_isSheaf_ext
    P Scheme.etaleTopology
  have he : Scheme.etaleTopology.{u} = Scheme.propQCTopology @Etale := by
    change (Scheme.precoverage @Etale).toGrothendieck =
      (Scheme.qcPrecoverage ⊓ Scheme.precoverage @Etale).toGrothendieck
    rw [inf_eq_right.mpr (Scheme.precoverage_le_qcPrecoverage_of_isOpenMap
      (fun X Y f hf => by
        let : Etale f := hf
        exact f.isOpenMap))]
  rw [he, isSheaf_type_propQCTopology_iff]
  refine ⟨Langlands.AlgebraicGeometry.OverFppfSheaf.isSheaf_ext_of_isSheaf_over
    P Scheme.zariskiTopology (parabolic_isSheaf G hG), ?_⟩
  intro R R' φ hφ hs
  let : Etale (Spec.map φ) := hφ
  let : Surjective (Spec.map φ) := hs
  have : IsRegularEpi (Spec.map φ) :=
    isRegularEpi_of_flat_of_surjective_of_isAffine _
  apply Langlands.AlgebraicGeometry.OverFppfSheaf.isSheafFor_singleton_ext P (Spec.map φ)
    (.singleton_of_isRepresentable_of_effectiveEpi _ _)
  intro (s : Spec R ⟶ S)
  let : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec R))
  let : IsAffine (Over.mk (Spec.map φ ≫ s)).left :=
    inferInstanceAs (IsAffine (Spec R'))
  let a : Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s := Over.homMk (Spec.map φ)
  let : Etale a.left := hφ
  let : Surjective a.left := hs
  exact parabolic_isSheafFor_affineEtale G hG a

/-- The big étale sheaf whose sections are actual relative parabolic
subgroup functors on every test scheme. -/
def parabolicEtaleSheaf : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  ⟨parabolicPresheaf G hG,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (parabolic_isSheaf_etale G hG)⟩

/-- The singleton sheaf condition holds for every surjective étale parameter
morphism, including nonaffine source and target. -/
theorem parabolic_isSheafFor_etale {M T : Over S} (a : M ⟶ T)
    [Etale a.left] [Surjective a.left] :
    Presieve.IsSheafFor (parabolicPresheaf G hG) (.singleton a) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply parabolic_isSheaf_etale G hG
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0}]
  change Sieve.overEquiv _ (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  change Sieve.generate (Presieve.ofArrows
    (fun _ : PUnit.{1} => M.left) (fun _ => a.left)) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff @Etale a.left).mpr
      ⟨a.left.surjective, inferInstance⟩)

variable {G}

/-- Ordinary matching has unique actual descent along any surjective étale
parameter morphism. -/
theorem existsUnique_restrict_etale {M T : Over S} (a : M ⟶ T)
    [Etale a.left] [Surjective a.left]
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F) :
    ∃! H : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G),
      restrict hG a H = F :=
  Presieve.isSheafFor_singleton.mp (parabolic_isSheafFor_etale G hG a) F
    (fun {V} b c hab => hF V b c hab)

/-- Construct the global actual parabolic family from matching data along
an arbitrary surjective étale parameter map. -/
def matchingEtale {M T : Over S} (a : M ⟶ T)
    [Etale a.left] [Surjective a.left]
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F) :
    ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G) :=
  (existsUnique_restrict_etale hG a F hF).choose

/-- The constructed global parabolic restricts to the prescribed local family. -/
@[simp]
theorem restrict_matchingEtale {M T : Over S} (a : M ⟶ T)
    [Etale a.left] [Surjective a.left]
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G))
    (hF : IsMatchingAlong hG a F) :
    restrict hG a (matchingEtale hG a F hF) = F :=
  (existsUnique_restrict_etale hG a F hF).choose_spec.1

end Langlands.GroupScheme.ParabolicSubgroupModuli
