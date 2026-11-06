import Langlands.GroupScheme.Reductive.CentralizerProduct
import Langlands.GroupScheme.Derived.CentralProduct
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Full centralizers, perfect factors and derived subgroup comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H C : GroupScheme S}

/-- The full centralizer of an actual homomorphism commutes with arbitrary
base change, on all test schemes and refinements. -/
theorem conjugation_fixedSubgroup_baseChange (j : H ⟶ G) :
    (AutomorphicAction.conjugation ((GroupScheme.baseChange b).map j)).fixedSubgroup =
      (AutomorphicAction.conjugation j).fixedSubgroup.baseChange b := by
  ext T x
  rw [SubgroupFunctor.mem_baseChange, mem_conjugation_fixedSubgroup_iff,
    mem_conjugation_fixedSubgroup_iff]
  constructor
  · intro hx U c h
    let U' : Over S' := Over.mk (c.left ≫ T.hom)
    let a : U' ⟶ T := Over.homMk c.left rfl
    let e : U ≅ (Over.map b).obj U' := Over.isoMk (Iso.refl _) (by
      simpa [U'] using Over.w c)
    have hc : e.hom ≫ (Over.map b).map a = c := by
      ext
      simp [e, a]
    have h1 := (hx U' a ((baseChangePointsEquiv b H U').symm (e.inv ≫ h))).map
      (baseChangePointsEquiv b G U').toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom] at h1
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply,
      baseChangePointsEquiv_naturality] at h1
    have h2 := commute_comp e.hom h1
    simpa only [← Category.assoc, hc, Iso.hom_inv_id, Category.id_comp] using h2
  · intro hx U a h
    have h1 := hx ((Over.map b).obj U) ((Over.map b).map a)
      (baseChangePointsEquiv b H U h)
    rw [← baseChangePointsEquiv_naturality, ← baseChangePointsEquiv_comp] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      h1.map (baseChangePointsEquiv b G U).symm.toMonoidHom

/-- Every supplied representative of the full centralizer remains one after
arbitrary base change. -/
theorem isRepresentedBy_conjugation_fixedSubgroup_baseChange
    {j : H ⟶ G} {c : C ⟶ G}
    (hc : (AutomorphicAction.conjugation j).fixedSubgroup.IsRepresentedBy c) :
    ((AutomorphicAction.conjugation ((GroupScheme.baseChange b).map j)).fixedSubgroup).IsRepresentedBy
      ((GroupScheme.baseChange b).map c) := by
  rw [conjugation_fixedSubgroup_baseChange]
  exact hc.baseChange b

end BaseChange

namespace CentralizerProduct

section Comparison

variable {S : Scheme.{u}} {G H C Z K D : GroupScheme S}
    (j : H ⟶ G) [Mono j.hom.hom] (c : C ⟶ G)
    (hc : (AutomorphicAction.conjugation j).fixedSubgroup.IsRepresentedBy c)
    (z : Z ⟶ H) (hz : IsSchemeTheoreticCenter z) (d : K ⟶ C)
    (hd : IsClosedSubgroup d)
    [Flat (subgroupMultiplication j (d ≫ c)).left]
    [Surjective (subgroupMultiplication j (d ≫ c)).left]
    [QuasiCompact (subgroupMultiplication j (d ≫ c)).left]
    (hK : derivedSubgroup K = ⊤)

include hc hz hd hK in
/-- A perfect closed centralizer factor giving fpqc ambient multiplication is
the full derived subgroup of the centralizer. -/
theorem isDerivedSubgroup : IsDerivedSubgroup d := by
  have hp := fpqc j c hc z hz d
  let : Flat (subgroupMultiplication (centerMap j c hc z hz) d).left := hp.1
  let : Surjective (subgroupMultiplication (centerMap j c hc z hz) d).left := hp.2.1
  let : QuasiCompact (subgroupMultiplication (centerMap j c hc z hz) d).left := hp.2.2
  exact isDerivedSubgroup_of_fpqc_centralProduct (centerMap j c hc z hz) d
    (centerMap_isCentral j c hc z hz) hd hK

/-- The actual comparison of a perfect centralizer factor with any supplied
full derived representative of that centralizer. -/
def derivedIso {e : D ⟶ C} (he : IsDerivedSubgroup e) : K ≅ D :=
  (isDerivedSubgroup j c hc z hz d hd hK).iso he

@[reassoc]
theorem derivedIso_hom_comp {e : D ⟶ C} (he : IsDerivedSubgroup e) :
    (derivedIso j c hc z hz d hd hK he).hom ≫ e = d :=
  (isDerivedSubgroup j c hc z hz d hd hK).iso_hom_comp he

end Comparison

section FieldExtension

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G H C Z D : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) [Mono j.hom.hom] (c : C ⟶ G)
    (hc : (AutomorphicAction.conjugation j).fixedSubgroup.IsRepresentedBy c)
    (z : Z ⟶ H) (hz : IsSchemeTheoreticCenter z)
    [IsAffineHom C.X.hom] {e : D ⟶ C} (he : IsDerivedSubgroup e)

local instance : Mono
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map j).hom.hom :=
  inferInstanceAs
    (Mono ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map j.hom.hom))

variable {K : GroupScheme (Spec (CommRingCat.of L))}
    (d : K ⟶ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj C)
    (hd : IsClosedSubgroup d)
    [Flat (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map j)
      (d ≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map c)).left]
    [Surjective (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map j)
      (d ≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map c)).left]
    [QuasiCompact (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map j)
      (d ≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map c)).left]
    (hK : derivedSubgroup K = ⊤)

/-- A geometric perfect centralizer factor is actually the base change of the
original full derived representative, compatibly with its inclusion. -/
def derivedIsoOfFieldExtension :
    K ≅ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj D :=
  derivedIso
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map j)
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map c)
    (isRepresentedBy_conjugation_fixedSubgroup_baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) hc)
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map z)
    (hz.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))) d hd hK
    (he.baseChange_of_eq (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (derivedSubgroup_baseChange_eq_of_field
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) C))

@[reassoc]
theorem derivedIsoOfFieldExtension_hom_comp :
    (derivedIsoOfFieldExtension j c hc z hz he d hd hK).hom ≫
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map e = d := by
  exact (isDerivedSubgroup
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map j)
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map c)
    (isRepresentedBy_conjugation_fixedSubgroup_baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) hc)
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map z)
    (hz.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))) d hd hK).iso_hom_comp
    (he.baseChange_of_eq (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (derivedSubgroup_baseChange_eq_of_field
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) C))

include hc hz he hd hK in
/-- Semisimplicity of a supplied geometric perfect factor descends to the
original full derived representative of the centralizer. -/
theorem semisimple_of_fieldExtension (hKs : IsSemisimple K) : IsSemisimple D := by
  have hDs : IsSemisimple
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj D) :=
    hKs.of_iso (derivedIsoOfFieldExtension j c hc z hz he d hd hK).symm
  exact IsSemisimple.of_fieldExtension hDs

end FieldExtension

end CentralizerProduct

end Langlands.GroupScheme
