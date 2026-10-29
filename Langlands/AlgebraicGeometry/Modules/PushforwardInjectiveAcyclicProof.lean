import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Topology.Sheaves.Flasque
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicStatement
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof
import Langlands.Cohomology.RightDerivedSequence

/-! # Pushforwards of injective scheme modules are acyclic: proof -/

universe v u u'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace PushforwardInjectiveAcyclic

section Injective

variable {C : Type u'} [Category.{v} C]

/-- The free presheaf of modules functor sends monomorphisms of presheaves of types to
monomorphisms. -/
lemma mono_free_map (R₀ : Cᵒᵖ ⥤ RingCat.{v}) {F G : Cᵒᵖ ⥤ Type v} (φ : F ⟶ G) [Mono φ] :
    Mono ((PresheafOfModules.free R₀).map φ) := by
  apply PresheafOfModules.mono_of_injective
  intro X
  have hφ : Function.Injective (φ.app X) :=
    (mono_iff_injective (φ.app X)).1 inferInstance
  exact Finsupp.mapDomain_injective hφ

lemma freeYonedaEquiv_apply {R₀ : Cᵒᵖ ⥤ RingCat.{v}} {M : PresheafOfModules.{v} R₀} {U : C}
    (g : (PresheafOfModules.free R₀).obj (yoneda.obj U) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv g = g.app (op U) (ModuleCat.freeMk (𝟙 U)) := rfl

/-- `freeYonedaEquiv` is natural in the representing object. -/
lemma freeYonedaEquiv_free_map_yoneda_map_comp {R₀ : Cᵒᵖ ⥤ RingCat.{v}}
    {M : PresheafOfModules.{v} R₀} {U V : C} (f : U ⟶ V)
    (g : (PresheafOfModules.free R₀).obj (yoneda.obj V) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv ((PresheafOfModules.free R₀).map (yoneda.map f) ≫ g) =
      M.map f.op (PresheafOfModules.freeYonedaEquiv g) := by
  have h := (PresheafOfModules.freeAdjunction R₀).homEquiv_naturality_left (yoneda.map f) g
  simp only [PresheafOfModules.freeAdjunction_homEquiv] at h
  exact (congrArg yonedaEquiv h).trans (yonedaEquiv_naturality _ _).symm

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Every restriction map of an injective sheaf of modules along a monomorphism of the
site is surjective. -/
lemma surjective_map_of_injective (M : SheafOfModules.{v} R) [Injective M] {U V : C}
    (f : U ⟶ V) [Mono f] : Function.Surjective (M.val.map f.op) := by
  intro t
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let i : (PresheafOfModules.free R.obj).obj (yoneda.obj U) ⟶
      (PresheafOfModules.free R.obj).obj (yoneda.obj V) :=
    (PresheafOfModules.free R.obj).map (yoneda.map f)
  have : Mono i := mono_free_map R.obj _
  let φ : (PresheafOfModules.free R.obj).obj (yoneda.obj U) ⟶
      (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M :=
    PresheafOfModules.freeYonedaEquiv.symm t
  let m := (PresheafOfModules.sheafification (𝟙 R.obj)).map i
  have : Mono m := inferInstance
  let ψ := Injective.factorThru ((adj.homEquiv _ _).symm φ) m
  have hψ : m ≫ ψ = (adj.homEquiv _ _).symm φ := Injective.comp_factorThru _ _
  have h : i ≫ adj.homEquiv _ _ ψ = φ := by
    rw [← Adjunction.homEquiv_naturality_left]
    change adj.homEquiv _ _ (m ≫ ψ) = φ
    rw [hψ, Equiv.apply_symm_apply]
  refine ⟨PresheafOfModules.freeYonedaEquiv (adj.homEquiv _ _ ψ), ?_⟩
  have := congrArg PresheafOfModules.freeYonedaEquiv h
  rw [freeYonedaEquiv_free_map_yoneda_map_comp] at this
  exact this.trans (Equiv.apply_symm_apply _ _)

end Injective

section Flasque

variable {X Y : Scheme.{u}}

/-- The forgetful functor from `𝒪_X`-modules to sheaves of abelian groups on `X`. -/
noncomputable abbrev toAbSheaf (X : Scheme.{u}) : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance (X : Scheme.{u}) : (toAbSheaf X).PreservesZeroMorphisms :=
  ⟨fun M N => (SheafOfModules.toSheaf X.ringCatSheaf).map_zero M N⟩

instance (X : Scheme.{u}) : PreservesFiniteLimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

instance (X : Scheme.{u}) : PreservesFiniteColimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf X.ringCatSheaf))

/-- Injective `𝒪_X`-modules are flasque. -/
lemma isFlasque_of_injective (I : X.Modules) [Injective I] :
    TopCat.Presheaf.IsFlasque I.presheaf where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    have : Injective (C := SheafOfModules.{u} X.ringCatSheaf) I := ‹_›
    exact surjective_map_of_injective X.ringCatSheaf I i.unop

/-- The pushforward of a flasque `𝒪_X`-module is flasque. -/
lemma isFlasque_pushforward (h : X ⟶ Y) (M : X.Modules)
    [TopCat.Presheaf.IsFlasque M.presheaf] :
    TopCat.Presheaf.IsFlasque ((Scheme.Modules.pushforward h).obj M).presheaf where
  epi {U V} i := by
    change Epi (M.presheaf.map ((TopologicalSpace.Opens.map h.base).map i.unop).op)
    infer_instance

/-- The short exact sequence `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` given by the chosen embedding of `F`
into an injective object. -/
noncomputable abbrev injectiveSc (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma injectiveSc_shortExact (F : X.Modules) : (injectiveSc F).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

lemma toSheaf_injectiveSc_shortExact (F : X.Modules) :
    ((injectiveSc F).map (toAbSheaf X)).ShortExact :=
  (injectiveSc_shortExact F).map_of_exact _

/-- The cokernel of the embedding of a flasque module into an injective one is flasque. -/
lemma isFlasque_cokernel (F : X.Modules) [TopCat.Presheaf.IsFlasque F.presheaf] :
    TopCat.Presheaf.IsFlasque (cokernel (Injective.ι F)).presheaf := by
  have hS := toSheaf_injectiveSc_shortExact F
  have : TopCat.Sheaf.IsFlasque
      ((injectiveSc F).map (toAbSheaf X)).X₁ :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque F.presheaf)
  have : TopCat.Sheaf.IsFlasque
      ((injectiveSc F).map (toAbSheaf X)).X₂ :=
    isFlasque_of_injective (Injective.under F)
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS

/-- For a flasque module `F`, global sections of the injective hull surject onto global
sections of the cokernel. -/
lemma epi_globalSections_map (F : X.Modules) [TopCat.Presheaf.IsFlasque F.presheaf] :
    Epi ((DerivedSections.globalSections X).map (injectiveSc F).g) := by
  have hS := toSheaf_injectiveSc_shortExact F
  have : TopCat.Sheaf.IsFlasque
      ((injectiveSc F).map (toAbSheaf X)).X₁ :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque F.presheaf)
  have := TopCat.Sheaf.IsFlasque.epi_of_shortExact hS (U := ⊤)
  rw [ModuleCat.epi_iff_surjective]
  exact (AddCommGrpCat.epi_iff_surjective _).1 this

/-- Flasque `𝒪_X`-modules have vanishing higher cohomology. -/
theorem isZero_cohomology_succ_of_isFlasque (n : ℕ) (F : X.Modules)
    [TopCat.Presheaf.IsFlasque F.presheaf] :
    IsZero ((DerivedSections.cohomology X (n + 1)).obj F) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, ⊤))
  let G := DerivedSections.globalSections X
  change IsZero ((G.rightDerived (n + 1)).obj F)
  induction n generalizing F with
  | zero =>
    have hS := injectiveSc_shortExact F
    have := Langlands.Cohomology.DerivedPlus.epi_rightDerivedδ_of_isZero G hS 0 1 rfl
      (G.isZero_rightDerived_obj_injective_succ 0 (Injective.under F))
    refine IsZero.of_epi_eq_zero (Langlands.Cohomology.DerivedPlus.rightDerivedδ G hS 0 1 rfl) ?_
    have h0 : Epi ((G.rightDerived 0).map (injectiveSc F).g) := by
      have e : (G.rightDerived 0).map (injectiveSc F).g =
          (G.rightDerivedZeroIsoSelf.hom.app _ ≫ G.map (injectiveSc F).g) ≫
            G.rightDerivedZeroIsoSelf.inv.app _ := by
        rw [← G.rightDerivedZeroIsoSelf.hom.naturality, Category.assoc,
          Iso.hom_inv_id_app, Category.comp_id]
      have := epi_globalSections_map F
      rw [e]
      infer_instance
    rw [← cancel_epi ((G.rightDerived 0).map (injectiveSc F).g),
      Langlands.Cohomology.DerivedPlus.rightDerived_map_comp_δ, comp_zero]
  | succ n ih =>
    have hS := injectiveSc_shortExact F
    have := Langlands.Cohomology.DerivedPlus.epi_rightDerivedδ_of_isZero G hS (n + 1) (n + 2) rfl
      (G.isZero_rightDerived_obj_injective_succ (n + 1) (Injective.under F))
    have : TopCat.Presheaf.IsFlasque (cokernel (Injective.ι F)).presheaf := isFlasque_cokernel F
    exact IsZero.of_epi (Langlands.Cohomology.DerivedPlus.rightDerivedδ G hS (n + 1) (n + 2) rfl)
      (ih (cokernel (Injective.ι F)))

end Flasque

end PushforwardInjectiveAcyclic

open PushforwardInjectiveAcyclic in
/-- Pushforwards of injective `𝒪_X`-modules have vanishing higher cohomology. -/
theorem pushforwardInjectiveAcyclic : PushforwardInjectiveAcyclicStatement.{u} := by
  intro X Y h J _ n
  have : TopCat.Presheaf.IsFlasque J.presheaf := isFlasque_of_injective J
  have : TopCat.Presheaf.IsFlasque ((Scheme.Modules.pushforward h).obj J).presheaf :=
    isFlasque_pushforward h J
  have h0 := isZero_cohomology_succ_of_isFlasque n ((Scheme.Modules.pushforward h).obj J)
  refine ⟨h0, fun R g => ?_⟩
  exact ((ModuleCat.restrictScalars (DerivedSections.structureRingHom g).hom).map_isZero h0).of_iso
    ((DerivedSections.relativeCohomologyRestrictScalarsIso g (n + 1)).app _).symm

end Langlands.AlgebraicGeometry.Modules
