import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Compactness.Compact

/-!
# Supports of sections and compactly supported sections on a site with points

Let `Φ : I → J.Point` be a family of points of a site, indexed by a topological
space `I`. The support of a section of a module presheaf is the set of indices at
which some germ of the section is nonzero. Sections whose support lies in a
compact subset of `I` form a submodule, functorially in the presheaf. On sheaves
this gives a left exact compactly supported sections functor, whose right
derived functors are the compactly supported cohomology.
-/

noncomputable section

namespace Langlands.Sheaf.PointSupport

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type uI} (Φ : I → J.Point.{w})
variable {R : Type w} [CommRing R]

section Support

/-- The support of a section `s` over `X`: the indices `i` for which the germ of
`s` at some element of the fiber of `Φ i` over `X` is nonzero. -/
def support (F : Cᵒᵖ ⥤ ModuleCat.{w} R) {X : C} (s : F.obj (op X)) : Set I :=
  {i | ∃ x : (Φ i).fiber.obj X, (Φ i).toPresheafFiber X x F s ≠ 0}

variable {Φ}

theorem mem_support {F : Cᵒᵖ ⥤ ModuleCat.{w} R} {X : C} {s : F.obj (op X)} {i : I} :
    i ∈ support Φ F s ↔ ∃ x : (Φ i).fiber.obj X, (Φ i).toPresheafFiber X x F s ≠ 0 :=
  Iff.rfl

theorem support_zero (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (X : C) :
    support Φ F (0 : F.obj (op X)) = ∅ := by
  ext i
  simp [support]

theorem support_add_subset {F : Cᵒᵖ ⥤ ModuleCat.{w} R} {X : C} (s t : F.obj (op X)) :
    support Φ F (s + t) ⊆ support Φ F s ∪ support Φ F t := by
  rintro i ⟨x, hx⟩
  by_contra h
  simp only [Set.mem_union, mem_support, not_or, not_exists, not_not] at h
  apply hx
  rw [map_add, h.1 x, h.2 x, add_zero]

theorem support_smul_subset {F : Cᵒᵖ ⥤ ModuleCat.{w} R} {X : C} (r : R) (s : F.obj (op X)) :
    support Φ F (r • s) ⊆ support Φ F s := by
  rintro i ⟨x, hx⟩
  refine ⟨x, fun h => hx ?_⟩
  rw [map_smul, h, smul_zero]

/-- Restriction shrinks supports. -/
theorem support_map_subset (F : Cᵒᵖ ⥤ ModuleCat.{w} R) {X Y : C} (f : Y ⟶ X)
    (s : F.obj (op X)) : support Φ F (F.map f.op s) ⊆ support Φ F s := by
  rintro i ⟨y, hy⟩
  refine ⟨(Φ i).fiber.map f y, ?_⟩
  rwa [← GrothendieckTopology.Point.toPresheafFiber_w_apply]

/-- Morphisms of presheaves shrink supports. -/
theorem support_app_subset {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ G) {X : C}
    (s : F.obj (op X)) : support Φ G (φ.app (op X) s) ⊆ support Φ F s := by
  rintro i ⟨x, hx⟩
  refine ⟨x, fun h => hx ?_⟩
  rw [← GrothendieckTopology.Point.toPresheafFiber_naturality_apply, h, map_zero]

/-- A morphism of presheaves which is injective on all fibers preserves
supports. -/
theorem support_app_of_injective {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ G)
    (hφ : ∀ i, Function.Injective ((Φ i).presheafFiber.map φ)) {X : C} (s : F.obj (op X)) :
    support Φ G (φ.app (op X) s) = support Φ F s := by
  refine (support_app_subset φ s).antisymm ?_
  rintro i ⟨x, hx⟩
  refine ⟨x, fun h => hx (hφ i ?_)⟩
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply, h, map_zero]

/-- Over a terminal object the fiber of each point is a singleton, so the support
is the set of points at which the germ of the section is nonzero. -/
theorem mem_support_iff_of_isTerminal [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ ModuleCat.{w} R} {X : C}
    (hX : IsTerminal X) (s : F.obj (op X)) (i : I) :
    i ∈ support Φ F s ↔
      (Φ i).toPresheafFiber X ((Φ i).uniqueFiberObj X hX).default F s ≠ 0 := by
  let := (Φ i).uniqueFiberObj X hX
  constructor
  · rintro ⟨x, hx⟩
    rwa [Subsingleton.elim x default] at hx
  · exact fun h => ⟨_, h⟩

end Support

section Compact

variable [TopologicalSpace I]

/-- A section is compactly supported when its support lies in a compact subset of
the index space. -/
def IsCompactlySupported (F : Cᵒᵖ ⥤ ModuleCat.{w} R) {X : C} (s : F.obj (op X)) : Prop :=
  ∃ K : Set I, IsCompact K ∧ support Φ F s ⊆ K

variable (R) in
/-- The compactly supported sections over `X`. -/
def compactSubmodule (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (X : C) : Submodule R (F.obj (op X)) where
  carrier := {s | IsCompactlySupported Φ F s}
  zero_mem' := ⟨∅, isCompact_empty, (support_zero F X).subset⟩
  add_mem' := by
    rintro s t ⟨K, hK, hs⟩ ⟨K', hK', ht⟩
    exact ⟨K ∪ K', hK.union hK', (support_add_subset s t).trans (Set.union_subset_union hs ht)⟩
  smul_mem' := by
    rintro r s ⟨K, hK, hs⟩
    exact ⟨K, hK, (support_smul_subset r s).trans hs⟩

variable {Φ}

theorem mem_compactSubmodule {F : Cᵒᵖ ⥤ ModuleCat.{w} R} {X : C} {s : F.obj (op X)} :
    s ∈ compactSubmodule Φ R F X ↔ IsCompactlySupported Φ F s :=
  Iff.rfl

/-- Over a compact index space, every section is compactly supported. -/
theorem isCompactlySupported_of_compactSpace [CompactSpace I] (F : Cᵒᵖ ⥤ ModuleCat.{w} R)
    {X : C} (s : F.obj (op X)) : IsCompactlySupported Φ F s :=
  ⟨Set.univ, isCompact_univ, Set.subset_univ _⟩

theorem IsCompactlySupported.map {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ G) {X : C}
    {s : F.obj (op X)} (hs : IsCompactlySupported Φ F s) :
    IsCompactlySupported Φ G (φ.app (op X) s) := by
  obtain ⟨K, hK, hsK⟩ := hs
  exact ⟨K, hK, (support_app_subset φ s).trans hsK⟩

variable (Φ R)

/-- Compactly supported sections over `X`, as a functor on module presheaves:
a subfunctor of evaluation at `X`. -/
def compactSections (X : C) : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R where
  obj F := ModuleCat.of R (compactSubmodule Φ R F X)
  map φ := ModuleCat.ofHom ((φ.app (op X)).hom.restrict fun _ hs => hs.map φ)
  map_id _ := by
    ext
    rfl
  map_comp _ _ := by
    ext
    rfl

/-- The inclusion of compactly supported sections into all sections. -/
def compactSectionsι (X : C) :
    compactSections Φ R X ⟶ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op X) where
  app F := ModuleCat.ofHom (compactSubmodule Φ R F X).subtype
  naturality _ _ _ := rfl

theorem compactSectionsι_app_injective (X : C) (F : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    Function.Injective ((compactSectionsι Φ R X).app F) :=
  Subtype.val_injective

instance compactSections_additive (X : C) : (compactSections Φ R X).Additive where
  map_add := by
    intros
    ext
    rfl

variable (J)

/-- Compactly supported sections over `X` of module sheaves. -/
def sheafCompactSections (X : C) : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙ compactSections Φ R X

instance sheafCompactSections_additive (X : C) : (sheafCompactSections J Φ R X).Additive :=
  inferInstanceAs (sheafToPresheaf J (ModuleCat.{w} R) ⋙ compactSections Φ R X).Additive

variable [LocallySmall.{w} C]

omit [TopologicalSpace I] in
/-- The presheaf underlying the kernel inclusion of a morphism of module sheaves
is injective on all fibers. -/
theorem injective_presheafFiber_map_kernelι {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G)
    (i : I) :
    Function.Injective ((Φ i).presheafFiber.map
      ((sheafToPresheaf J (ModuleCat.{w} R)).map (kernel.ι f))) := by
  have : Presheaf.IsLocallyInjective J ((sheafToPresheaf J (ModuleCat.{w} R)).map (kernel.ι f)) :=
    Presheaf.isLocallyInjective_of_injective J _ fun U => by
      have : Mono ((sheafToPresheaf J (ModuleCat.{w} R) ⋙
          (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj U).map (kernel.ι f)) := inferInstance
      exact (ModuleCat.mono_iff_injective _).1 this
  exact (Φ i).toPresheafFiber_map_injective _

/-- Compactly supported sections of module sheaves preserve kernels: a section
of the kernel has the same support as its image. -/
instance sheafCompactSections_preservesKernel (X : C) {F G : Sheaf J (ModuleCat.{w} R)}
    (f : F ⟶ G) : PreservesLimit (parallelPair f 0) (sheafCompactSections J Φ R X) := by
  let Γ : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
    sheafToPresheaf J (ModuleCat.{w} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op X)
  let Γc := sheafCompactSections J Φ R X
  let S : ShortComplex (ModuleCat.{w} R) :=
    ShortComplex.mk (Γ.map (kernel.ι f)) (Γ.map f)
      (by rw [← Γ.map_comp, kernel.condition, Γ.map_zero])
  have hS : S.Exact :=
    ShortComplex.exact_of_f_is_kernel S (isLimitOfHasKernelOfPreservesLimit Γ f)
  let T : ShortComplex (ModuleCat.{w} R) :=
    ShortComplex.mk (Γc.map (kernel.ι f)) (Γc.map f)
      (by rw [← Γc.map_comp, kernel.condition, Γc.map_zero])
  have hT : T.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    have hz : S.g s.val = 0 := congrArg Subtype.val hs
    obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS s.val hz
    have hsupp : support Φ (kernel f).obj t = support Φ F.obj s.val :=
      (support_app_of_injective ((sheafToPresheaf J (ModuleCat.{w} R)).map (kernel.ι f))
        (injective_presheafFiber_map_kernelι J Φ R f) t).symm.trans
          (congrArg (support Φ F.obj) ht)
    refine ⟨⟨t, ?_⟩, Subtype.ext ht⟩
    obtain ⟨K, hK, hsK⟩ := s.property
    exact ⟨K, hK, hsupp ▸ hsK⟩
  have hTf : Mono T.f := by
    rw [ModuleCat.mono_iff_injective]
    intro a b h
    apply Subtype.ext
    have : Mono (Γ.map (kernel.ι f)) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this (congrArg Subtype.val h)
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  refine (isLimitMapConeForkEquiv' Γc (kernel.condition f)).symm ?_
  exact ModuleCat.isLimitKernelFork T.f T.g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT)
    ((ModuleCat.mono_iff_injective _).mp hTf)

variable [HasSheafify J (ModuleCat.{w} R)]

/-- Compactly supported sections of module sheaves are left exact. -/
instance sheafCompactSections_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (sheafCompactSections J Φ R X) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- Degree `q` compactly supported cohomology over `X`: the right derived functors
of compactly supported sections, computed with injective resolutions of module
sheaves. -/
def compactDerived (X : C) (q : ℕ) : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
  (sheafCompactSections J Φ R X).rightDerived q

/-- In degree zero, compactly supported cohomology is compactly supported
sections. -/
def compactDerivedZeroIso (X : C) : compactDerived J Φ R X 0 ≅ sheafCompactSections J Φ R X :=
  (sheafCompactSections J Φ R X).rightDerivedZeroIsoSelf

/-- Compactly supported cohomology is the homology of the compactly supported
sections of any injective resolution. -/
def compactDerivedIso (X : C) {F : Sheaf J (ModuleCat.{w} R)} (I : InjectiveResolution F)
    (q : ℕ) :
    (compactDerived J Φ R X q).obj F ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℕ) q).obj
        (((sheafCompactSections J Φ R X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (sheafCompactSections J Φ R X) q

omit [LocallySmall.{w} C] in
/-- Compactly supported cohomology vanishes in positive degrees on injective
sheaves. -/
theorem isZero_compactDerived_succ_of_injective (X : C) (F : Sheaf J (ModuleCat.{w} R))
    [Injective F] (q : ℕ) : IsZero ((compactDerived J Φ R X (q + 1)).obj F) :=
  (sheafCompactSections J Φ R X).isZero_rightDerived_obj_injective_succ q F

end Compact

end Langlands.Sheaf.PointSupport
