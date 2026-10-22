import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Compactly supported sections of module sheaves on a topological space

The support is defined by the actual stalk maps. Closedness, the submodule
operations and functoriality are proved. This is the ordinary topological
construction; no analytic site or smooth equivariant descent is assumed.
-/

noncomputable section

namespace Langlands.Sheaf.CompactSupport

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- The support of a global section is the set of its nonzero germs. -/
def support (F : X.Presheaf (ModuleCat.{u} R)) (s : F.obj (op ⊤)) : Set X :=
  {x | F.Γgerm x s ≠ 0}

/-- A zero germ is witnessed by vanishing on an open neighborhood. -/
theorem isClosed_support (F : X.Presheaf (ModuleCat.{u} R)) (s : F.obj (op ⊤)) :
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

/-- The actual submodule of global sections with compact support. -/
def submodule (F : X.Presheaf (ModuleCat.{u} R)) : Submodule R (F.obj (op ⊤)) where
  carrier := {s | IsCompact (support F s)}
  zero_mem' := by simp
  add_mem' hs ht :=
    (hs.union ht).of_isClosed_subset (isClosed_support F _) (support_add_subset F _ _)
  smul_mem' r s hs :=
    hs.of_isClosed_subset (isClosed_support F _) (support_smul_subset F r s)

/-- The induced linear map on compactly supported sections. -/
def map {F G : X.Presheaf (ModuleCat.{u} R)} (f : F ⟶ G) :
    submodule F →ₗ[R] submodule G :=
  (f.app (op ⊤)).hom.restrict
    (fun s hs => hs.of_isClosed_subset (isClosed_support G _) (support_map_subset f s))

/-- Compact sections are functorial already for module-valued presheaves. -/
def presheafFunctor : X.Presheaf (ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj F := ModuleCat.of R (submodule F)
  map f := ModuleCat.ofHom (map f)
  map_id F := by
    ext s
    rfl
  map_comp f g := by
    ext s
    rfl

variable (X R)

/-- Global sections, written as evaluation on the largest open. -/
def globalSections : TopCat.Sheaf (ModuleCat.{u} R) X ⥤ ModuleCat.{u} R :=
  TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)

instance : (globalSections (X := X) (R := R)).Additive where
  map_add := by
    intro F G f g
    rfl

instance : PreservesFiniteLimits (globalSections (X := X) (R := R)) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
      (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)))

/-- The compact-support section functor on actual module sheaves. -/
def functor : TopCat.Sheaf (ModuleCat.{u} R) X ⥤ ModuleCat.{u} R :=
  TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙ presheafFunctor

instance : (functor (X := X) (R := R)).Additive where
  map_add := by
    intro F G f g
    ext s
    rfl

/-- Forgetting compact support gives the canonical inclusion of sections. -/
def inclusion : functor (X := X) (R := R) ⟶ globalSections (X := X) (R := R) where
  app F := ModuleCat.ofHom (submodule F.presheaf).subtype
  naturality _ _ f := by
    ext s
    rfl

instance (F : TopCat.Sheaf (ModuleCat.{u} R) X) :
    Mono ((inclusion (X := X) (R := R)).app F) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

set_option backward.isDefEq.respectTransparency false in
/-- A monomorphism of sheaves preserves, rather than just shrinks, section support. -/
theorem support_map_of_mono {F G : TopCat.Sheaf (ModuleCat.{u} R) X}
    (f : F ⟶ G) [Mono f] (s : F.presheaf.obj (op ⊤)) :
    support G.presheaf (f.hom.app (op ⊤) s) = support F.presheaf s := by
  apply Set.Subset.antisymm (support_map_subset f.hom s)
  intro x hx
  have hinj := (ModuleCat.mono_iff_injective
    ((TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f)).mp inferInstance
  intro hz
  apply hx
  apply hinj
  rw [map_zero]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (⊤ : Opens X) x trivial
    f.hom s).trans hz

instance {F G : TopCat.Sheaf (ModuleCat.{u} R) X} (f : F ⟶ G) [Mono f] :
    Mono ((functor (X := X) (R := R)).map f) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro s t h
  apply Subtype.ext
  apply (ModuleCat.mono_iff_injective
    ((globalSections (X := X) (R := R)).map f)).mp inferInstance
  exact congrArg Subtype.val h

set_option backward.isDefEq.respectTransparency false in
/-- Compact sections preserve kernels: a lifted section has the same support. -/
instance preservesKernel {F G : TopCat.Sheaf (ModuleCat.{u} R) X} (f : F ⟶ G) :
    PreservesLimit (parallelPair f 0) (functor (X := X) (R := R)) := by
  let Γ := globalSections (X := X) (R := R)
  let Γc := functor (X := X) (R := R)
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (Γ.map (kernel.ι f)) (Γ.map f)
      (by rw [← Γ.map_comp, kernel.condition, Γ.map_zero])
  have hS : S.Exact :=
    ShortComplex.exact_of_f_is_kernel S (isLimitOfHasKernelOfPreservesLimit Γ f)
  let T : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (Γc.map (kernel.ι f)) (Γc.map f)
      (by rw [← Γc.map_comp, kernel.condition, Γc.map_zero])
  have hT : T.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    have hz : S.g s.val = 0 := congrArg Subtype.val hs
    obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS s.val hz
    have hc : IsCompact (support (kernel f).presheaf t) := by
      rw [← support_map_of_mono (X := X) (R := R) (kernel.ι f) t]
      change IsCompact (support F.presheaf (S.f t))
      rw [ht]
      exact s.property
    refine ⟨⟨t, hc⟩, ?_⟩
    exact Subtype.ext ht
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  refine (isLimitMapConeForkEquiv' Γc (kernel.condition f)).symm ?_
  exact ModuleCat.isLimitKernelFork T.f T.g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT)
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- The constructed compact-section functor is left exact. -/
instance : PreservesFiniteLimits (functor (X := X) (R := R)) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

end Langlands.Sheaf.CompactSupport
