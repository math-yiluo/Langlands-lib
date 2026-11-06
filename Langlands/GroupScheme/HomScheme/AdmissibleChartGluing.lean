import Langlands.GroupScheme.HomScheme.AdmissibleChartCover
import Langlands.GroupScheme.HomScheme.AdmissibleSheaf

/-! # Gluing actual admissible charts, conditional on effective descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A representing object for the actual admissible presheaf carries an actual
universal closed torus family. -/
theorem exists_universal_of_representableBy {M : Over S}
    (e : (smallAdmissiblePresheaf G).RepresentableBy M) :
    ∃ (K : GroupScheme M.left) (j : K ⟶ (baseChange M.hom).obj G),
      IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧ IsUniversal j := by
  let F := smallAdmissibleEquiv G M (e.homEquiv (𝟙 M))
  let r := admissibleRepresentative F
  have he {T : Over S} (a : T ⟶ M) :
      evaluate r.hom a = (smallAdmissibleEquiv G T (e.homEquiv a)).val := by
    rw [e.homEquiv_eq, smallAdmissibleEquiv_map]
    exact (restrict_eq_evaluate F r.hom r.represents.2 a).symm
  refine ⟨r.group, r.hom, r.closed, r.torus, ?_⟩
  intro T F' hF'
  let x := (smallAdmissibleEquiv G T).symm ⟨F', hF'⟩
  refine ⟨e.homEquiv.symm x, ?_, ?_⟩
  · change evaluate r.hom (e.homEquiv.symm x) = F'
    rw [he, Equiv.apply_symm_apply]
    exact congrArg Subtype.val ((smallAdmissibleEquiv G T).apply_symm_apply ⟨F', hF'⟩)
  · intro b hb
    apply e.homEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply (smallAdmissibleEquiv G T).injective
    apply Subtype.ext
    rw [← he, hb]
    exact (congrArg Subtype.val
      ((smallAdmissibleEquiv G T).apply_symm_apply ⟨F', hF'⟩)).symm

namespace OpenCharts

variable {ι : Type u} {U : ι → Over S} {K : ∀ k, GroupScheme (U k).left}
variable (j : ∀ k, K k ⟶ (baseChange (U k).hom).obj G)
variable (hj : ∀ k, IsOpenChart (j k))

/-- The total sheaf of actual admissible subgroups, with its explicit effective
descent hypothesis. -/
def totalSheaf (hG : HasEffectiveAdmissibleDescent G) :
    Sheaf Scheme.zariskiTopology (Type u) :=
  ⟨totalAdmissiblePresheaf G,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (totalAdmissible_isSheaf G hG)⟩

/-- The scheme gluing datum is the actual charts and their represented open
pairwise intersections. -/
def glueDatum (hG : HasEffectiveAdmissibleDescent G) : Scheme.GlueData :=
  Scheme.LocalRepresentability.glueData (F := totalSheaf hG)
    (fun k => isOpenImmersion_presheaf (j k) (hj k))

include hj in
/-- The gluing of actual open charts constructs a smooth parameter scheme and
an actual universal closed torus family, conditional only on effective
admissible descent. -/
theorem exists_smooth_universal (hG : HasEffectiveAdmissibleDescent G)
    (hc : CoversFieldPoints j) :
    ∃ (M : Over S) (L : GroupScheme M.left)
      (i : L ⟶ (baseChange M.hom).obj G),
      IsClosedSubgroup i ∧ RelativeTorus.IsTorus L ∧
        IsUniversal i ∧ Smooth M.hom := by
  let F := totalSheaf hG
  have hf : ∀ k, IsOpenImmersion.presheaf
      (show yoneda.obj (U k).left ⟶ F.1 from chartMap (j k) (hj k)) :=
    fun k => isOpenImmersion_presheaf (j k) (hj k)
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun k => (show yoneda.obj (U k).left ⟶ F.1 from
        chartMap (j k) (hj k)))) := isLocallySurjective j hj hc
  let e : (totalAdmissiblePresheaf G).RepresentableBy _ :=
    Scheme.LocalRepresentability.representableBy (F := F) hf
  let X := (Scheme.LocalRepresentability.glueData (F := F) hf).glued
  let a : ∀ k, (U k).left ⟶ X := fun k =>
    Scheme.LocalRepresentability.toGlued (F := F) hf k
  have hea (k : ι) : e.homEquiv (a k) = yonedaEquiv (chartMap (j k) (hj k)) :=
    Scheme.LocalRepresentability.yonedaGluedToSheaf_app_toGlued (F := F) hf
  have hab (k : ι) : a k ≫ e.overTotalBase = (U k).hom := by
    calc a k ≫ e.overTotalBase = (e.homEquiv (a k)).1 :=
          (e.overTotal_homEquiv_fst (a k)).symm
      _ = (yonedaEquiv (chartMap (j k) (hj k))).1 := congrArg Sigma.fst (hea k)
      _ = (U k).hom := rfl
  have hs : Smooth e.overTotalBase := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Smooth)
      (Scheme.LocalRepresentability.glueData (F := F) hf).openCover
    intro k
    change Smooth (a k ≫ e.overTotalBase)
    rw [hab]
    exact (hj k).smooth
  obtain ⟨L, i, hi, hL, hu⟩ := exists_universal_of_representableBy e.ofOverTotal
  exact ⟨Over.mk e.overTotalBase, L, i, hi, hL, hu, hs⟩

end OpenCharts

end Langlands.GroupScheme.TorusSubgroupModuli
