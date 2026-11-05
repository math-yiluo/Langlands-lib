import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Solvability reduction for quasi-split groups with central cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G P : GroupScheme S}

/-- A subgroup representing the dynamic parabolic of a central cocharacter is canonically
isomorphic to the ambient group. -/
def isoOfCentralParabolic (χ : (Gm S).toGrp ⟶ G) {i : P ⟶ G}
    (hi : (parabolic χ).IsRepresentedBy i) (hχ : centralizer χ = ⊤) : P ≅ G := by
  have htop : (⊤ : SubgroupFunctor G).IsRepresentedBy i :=
    ⟨hi.1, hi.2.trans (parabolic_eq_top_of_centralizer χ hχ)⟩
  exact htop.isoOfIsRepresentedBy (SubgroupFunctor.top_isRepresentedBy_id G)

/-- The canonical isomorphism has the original subgroup inclusion as its forward map. -/
@[simp] theorem isoOfCentralParabolic_hom (χ : (Gm S).toGrp ⟶ G) {i : P ⟶ G}
    (hi : (parabolic χ).IsRepresentedBy i) (hχ : centralizer χ = ⊤) :
    (isoOfCentralParabolic χ hi hχ).hom = i := by
  unfold isoOfCentralParabolic
  simpa only [Category.comp_id] using
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
      (F := (⊤ : SubgroupFunctor G))
      ⟨hi.1, hi.2.trans (parabolic_eq_top_of_centralizer χ hχ)⟩
      (SubgroupFunctor.top_isRepresentedBy_id G)

end Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- With the parabolic/cocharacter comparison, every parabolic inclusion into a connected
reductive group whose ground-field cocharacters are central is an isomorphism. -/
theorem isIso_parabolic_of_central_cocharacters (hdynamic : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G)
    (hcentral : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.centralizer χ = ⊤)
    {P : GroupScheme (Spec (CommRingCat.of k))} {i : P ⟶ G}
    (hi : IsParabolicSubgroup i) : IsIso i := by
  obtain ⟨χ, hχ⟩ := (hdynamic k G hG P i hi.isClosedSubgroup).1 hi
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy i := ⟨inferInstance, hχ⟩
  rw [← Dynamic.isoOfCentralParabolic_hom χ hrep (hcentral χ)]
  infer_instance

/-- A quasi-split group whose ground-field cocharacters are all central is solvable,
provided the parabolic/cocharacter comparison is available. -/
theorem IsQuasiSplit.isSolvableGroupScheme_of_central_cocharacters
    (hG : IsQuasiSplit G) (hdynamic : ParabolicDynamicStatement.{u})
    (hcentral : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.centralizer χ = ⊤) : IsSolvableGroupScheme G := by
  obtain ⟨B, i, hi, hB⟩ := hG.exists_solvable_parabolic
  have : IsIso i := isIso_parabolic_of_central_cocharacters hdynamic
    hG.isConnectedReductive hcentral hi
  exact hB.of_iso (asIso i).symm

end Langlands.GroupScheme
