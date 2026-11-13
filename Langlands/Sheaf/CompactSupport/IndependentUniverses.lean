import Langlands.Sheaf.CompactSupport

/-!
# Compact sections with independent coefficient and space universes

This internal extension uses the same actual nonzero-germ support and compactness
condition as `CompactSupport`. The auxiliary filtered-colimit instances are local.
-/

noncomputable section

namespace Langlands.Sheaf.CompactSupport.IndependentUniverses

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

section General

variable {R : Type v} [CommRing R] {X : TopCat.{u}}

/-- Filtered colimits of modules are preserved by forgetting to abelian groups
also when the carrier universe is larger than the coefficient universe. -/
local instance forget₂_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {G} =>
        preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit G)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (G ⋙ forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})) }

/-- Germs are computed elementwise at all compatible carrier universes. -/
local instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget (ModuleCat.{max u v} R)) :=
  Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
    (forget AddCommGrpCat.{max u v})

/-- The support of a global section is the set of its nonzero germs. -/
def support (F : X.Presheaf (ModuleCat.{u} R)) (s : F.obj (op ⊤)) : Set X :=
  {x | F.Γgerm x s ≠ 0}

/-- A zero germ is witnessed by vanishing on an open neighborhood. -/
theorem isClosed_support [PreservesFilteredColimits (forget (ModuleCat.{u} R))]
    (F : X.Presheaf (ModuleCat.{u} R)) (s : F.obj (op ⊤)) :
    IsClosed (support F s) := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : F.Γgerm x s = 0 := by simpa [support] using hx
  obtain ⟨W, hxW, i, j, hW⟩ :=
    F.germ_eq x (U := ⊤) (V := ⊤) trivial trivial s 0
      (by simpa [TopCat.Presheaf.Γgerm] using hx0)
  have hzero : F.map i.op s = 0 := by simpa using hW
  apply Filter.mem_of_superset (W.isOpen.mem_nhds hxW)
  intro y hy
  change ¬ F.Γgerm y s ≠ 0
  apply not_not.mpr
  rw [← F.Γgerm_res_apply y hy s (i := i), hzero]
  exact map_zero _

@[simp]
theorem support_zero (F : X.Presheaf (ModuleCat.{u} R)) :
    support F 0 = ∅ := by
  ext x
  simp [support]

theorem support_add_subset (F : X.Presheaf (ModuleCat.{u} R))
    (s t : F.obj (op ⊤)) :
    support F (s + t) ⊆ support F s ∪ support F t := by
  intro x hx
  by_contra h
  have hs : F.Γgerm x s = 0 := by simpa [support] using (not_or.mp h).1
  have ht : F.Γgerm x t = 0 := by simpa [support] using (not_or.mp h).2
  exact hx (by simp [map_add, hs, ht])

theorem support_smul_subset (F : X.Presheaf (ModuleCat.{u} R))
    (r : R) (s : F.obj (op ⊤)) :
    support F (r • s) ⊆ support F s := by
  intro x hx
  contrapose! hx
  simp only [support, Set.mem_ofPred_eq, not_not] at hx ⊢
  simp [hx]

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of presheaves cannot enlarge a section's support. -/
theorem support_map_subset {F G : X.Presheaf (ModuleCat.{u} R)}
    (f : F ⟶ G) (s : F.obj (op ⊤)) :
    support G (f.app (op ⊤) s) ⊆ support F s := by
  intro x hx
  contrapose! hx
  simp only [support, Set.mem_ofPred_eq, not_not] at hx ⊢
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply (⊤ : Opens X) x trivial f s
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f
    (F.Γgerm x s) = G.Γgerm x (f.app (op ⊤) s) at h
  rw [hx, map_zero] at h
  exact h.symm

variable [PreservesFilteredColimits (forget (ModuleCat.{u} R))]

/-- The actual submodule of global sections with compact support. -/
def submodule (F : X.Presheaf (ModuleCat.{u} R)) : Submodule R (F.obj (op ⊤)) where
  carrier := {s | IsCompact (support F s)}
  zero_mem' := by
    change IsCompact (support F 0)
    rw [support_zero F]
    exact isCompact_empty
  add_mem' hs ht :=
    (hs.union ht).of_isClosed_subset (isClosed_support F _) (support_add_subset F _ _)
  smul_mem' r s hs :=
    hs.of_isClosed_subset (isClosed_support F _) (support_smul_subset F r s)

/-- The induced linear map on compactly supported sections. -/
def map {F G : X.Presheaf (ModuleCat.{u} R)} (f : F ⟶ G) :
    submodule F →ₗ[R] submodule G :=
  (f.app (op ⊤)).hom.restrict
    (fun s hs => hs.of_isClosed_subset (isClosed_support G _) (support_map_subset f s))


end General

section Comparison

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
  (F : X.Presheaf (ModuleCat.{u} R))

/-- At a common universe this is the published support, by definition. -/
@[simp]
theorem support_eq (s : F.obj (op ⊤)) :
    support F s = CompactSupport.support F s := rfl

/-- At a common universe the compact-section submodule is the published one. -/
@[simp]
theorem submodule_eq : submodule F = CompactSupport.submodule F := by
  ext s
  rfl

end Comparison

end Langlands.Sheaf.CompactSupport.IndependentUniverses
