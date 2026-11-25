/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit

/-!
# Sections over qcqs objects of filtered colimits of pro-étale sheaves

Let `c` be a colimit cocone of a filtered diagram `F : K ⥤ Sh(X_proét, Ab)` and `W` an object
of the pro-étale site of `X` with quasi-compact quasi-separated underlying space. Then
`c.pt(W) = colim_k F_k(W)`: the cocone of section groups over `W` is a colimit cocone in `Ab`
(`AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimit`). This packages
`CategoryTheory.Sheaf.exists_app_eq_of_isColimit_of_finite` (sections come from a finite stage)
and `CategoryTheory.Sheaf.exists_map_eq_of_isColimit_of_finite` (sections are separated at a
finite stage), applied to the objects with qcqs underlying scheme, as a colimit statement;
the variant `AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimitOfSmall` allows diagrams
indexed by categories in `Type`, such as `ℕ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}

/-- The functor of sections over `W` of abelian pro-étale sheaves. -/
abbrev abSectionsFunctor (W : X.ProEt) :
    Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W)

section Large

variable {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
  {F : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone F}

/-- **Sections over a quasi-compact quasi-separated object commute with filtered colimits** of
abelian pro-étale sheaves: `c.pt(W) = colim_k F_k(W)`. -/
noncomputable def isColimitSectionsOfIsColimit (hc : IsColimit c) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit ((abSectionsFunctor W).mapCocone c) := by
  have : ReflectsColimitsOfShape K (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun s ↦ ?_) fun k a b h ↦ ?_
  · obtain ⟨k, t, ht⟩ := Sheaf.exists_app_eq_of_isColimit_of_finite hc
      (fun V : X.ProEt ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left)
      (fun _ hV _ hR ↦ exists_finite_cechNerve_of_mem_topology hV hR) ⟨‹_›, ‹_›⟩ s
    exact ⟨k, t, ht.symm⟩
  · refine Sheaf.exists_map_eq_of_isColimit_of_finite hc (fun R hR ↦ ?_) a b h
    obtain ⟨n, U, -, hUR, hUJ⟩ := exists_finite_cechNerve_of_mem_topology ⟨‹_›, ‹_›⟩ hR
    exact ⟨n, U, hUR, hUJ⟩

omit [IsFiltered K] in
lemma abSectionsFunctor_mapCocone_ι_app_apply (W : X.ProEt) (k : K)
    (t : (F.obj k).obj.obj (op W)) :
    ((abSectionsFunctor W).mapCocone c).ι.app k t = (c.ι.app k).hom.app (op W) t :=
  rfl


end Large

section Small

variable {J : Type} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone F}

/-- `AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimit` for a filtered diagram indexed
by a category in `Type`, such as `ℕ` or the finite subextensions of `ℚ̄_ℓ`. -/
noncomputable def isColimitSectionsOfIsColimitOfSmall (hc : IsColimit c) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit ((abSectionsFunctor W).mapCocone c) :=
  let e := (AsSmall.equiv.{0, 0, u + 1} (C := J)).symm
  (IsColimit.whiskerEquivalenceEquiv e).symm
    (isColimitSectionsOfIsColimit (hc.whiskerEquivalence e) W)

end Small

end AlgebraicGeometry.Scheme.ProEt
