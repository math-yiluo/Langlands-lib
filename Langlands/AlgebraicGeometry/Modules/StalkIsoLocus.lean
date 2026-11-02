import Langlands.CommutativeAlgebra.FinitePresentationFaithfulDescent
import Langlands.AlgebraicGeometry.Modules.AffineRankOneSpreading
import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatPullbackDescent
import Langlands.AlgebraicGeometry.Modules.StalkPullback
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # The locus where a morphism of module sheaves is a stalk isomorphism -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y W : Scheme.{u}}

/-- The set of points at which a morphism of module sheaves induces a bijection of
actual stalks. -/
def isoLocus {M N : X.Modules} (φ : M ⟶ N) : Set X :=
  {x | Function.Bijective (stalkMap φ x)}

lemma stalkMap_comp {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (x : X) :
    stalkMap (φ ≫ ψ) x = (stalkMap ψ x).comp (stalkMap φ x) :=
  congrArg ModuleCat.Hom.hom ((stalkFunctor x).map_comp φ ψ)

lemma bijective_stalkMap_of_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (x : X) :
    Function.Bijective (stalkMap φ x) :=
  (stalkIso (asIso φ) x).bijective

/-- The iso locus is unchanged by composing with isomorphisms on both sides. -/
lemma mem_isoLocus_iff_of_comm {M M' N N' : X.Modules} (e : M ≅ M') (e' : N ≅ N')
    (φ : M ⟶ N) (φ' : M' ⟶ N') (w : e.hom ≫ φ' = φ ≫ e'.hom) (x : X) :
    x ∈ isoLocus φ ↔ x ∈ isoLocus φ' := by
  have h := congrArg DFunLike.coe (congrArg (fun f => stalkMap f x) w)
  simp only [stalkMap_comp, LinearMap.coe_comp] at h
  change Function.Bijective (stalkMap φ x) ↔ Function.Bijective (stalkMap φ' x)
  rw [← Function.Bijective.of_comp_iff (stalkMap φ' x) (bijective_stalkMap_of_isIso e.hom x),
    ← Function.Bijective.of_comp_iff' (bijective_stalkMap_of_isIso e'.hom x) (stalkMap φ x), h]

/-- Bijectivity of the linear stalk map is the isomorphism condition on abelian stalks. -/
lemma bijective_stalkMap_iff {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    Function.Bijective (stalkMap φ x) ↔
      IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map ((Scheme.Modules.toPresheaf X).map φ)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  rfl

/-- Bijectivity of the linear stalk map is the isomorphism condition in the stalk functor. -/
lemma bijective_stalkMap_iff_isIso_stalkFunctor_map {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    Function.Bijective (stalkMap φ x) ↔ IsIso ((stalkFunctor x).map φ) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  rfl

lemma isIso_iff_forall_mem_isoLocus {M N : X.Modules} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ x, x ∈ isoLocus φ := by
  rw [Langlands.SchemeModule.isIso_iff_stalk_isIso]
  exact forall_congr' fun x => (bijective_stalkMap_iff φ x).symm

/-- Restriction along an open immersion does not change the stalk maps. -/
lemma mem_isoLocus_restrict_iff (f : W ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (φ : M ⟶ N) (w : W) :
    w ∈ isoLocus ((Scheme.Modules.restrictFunctor f).map φ) ↔ f w ∈ isoLocus φ := by
  change Function.Bijective _ ↔ Function.Bijective _
  rw [bijective_stalkMap_iff, bijective_stalkMap_iff]
  exact NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso f w) φ

/-- Pullback along a flat morphism detects bijectivity of stalk maps at the image point. -/
lemma mem_isoLocus_pullback_iff (p : X ⟶ Y) [Flat p] {M N : Y.Modules} (φ : M ⟶ N) (x : X) :
    x ∈ isoLocus ((Scheme.Modules.pullback p).map φ) ↔ p x ∈ isoLocus φ := by
  change Function.Bijective _ ↔ Function.Bijective _
  rw [bijective_stalkMap_iff_isIso_stalkFunctor_map,
    bijective_stalkMap_iff_isIso_stalkFunctor_map]
  refine (NatIso.isIso_map_iff (StalkPullback.pullbackStalkIso p x) φ).trans ?_
  have : (ModuleCat.extendScalars (p.stalkMap x).hom).ReflectsIsomorphisms :=
    ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat (faithfullyFlat_stalkMap p x)
  constructor
  · intro h
    have : IsIso ((ModuleCat.extendScalars (p.stalkMap x).hom).map
        ((stalkFunctor (p x)).map φ)) := h
    exact isIso_of_reflects_iso _ (ModuleCat.extendScalars (p.stalkMap x).hom)
  · intro h
    exact Functor.map_isIso (ModuleCat.extendScalars (p.stalkMap x).hom)
      ((stalkFunctor (p x)).map φ)

section Tilde

variable {R : CommRingCat.{u}}

/-- The stalk map of `tilde.map` is compatible with the localization maps to stalks. -/
lemma stalkMap_tilde_map_toStalk {A B : ModuleCat.{u} R} (l : A ⟶ B) (x : Spec R) (a : A) :
    stalkMap (tilde.map l) x ((tilde.toStalk A x).hom a) =
      (tilde.toStalk B x).hom (l.hom a) := by
  change (TopCat.Presheaf.stalkFunctor Ab x).map (tilde.map l).mapPresheaf
      (TopCat.Presheaf.germ (tilde A).presheaf ⊤ x trivial _) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change _ = TopCat.Presheaf.germ (tilde B).presheaf ⊤ x trivial _
  congr 1
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app l ⊤) a

/-- The stalk map of `tilde.map` is bijective exactly when the localized map is. -/
lemma mem_isoLocus_tilde_map_iff {A B : ModuleCat.{u} R} (l : A ⟶ B) (x : Spec R) :
    x ∈ isoLocus (tilde.map l) ↔
      Function.Bijective (IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk A x).hom (tilde.toStalk B x).hom l.hom) := by
  let ψ : stalk (tilde A) x →ₗ[R] stalk (tilde B) x :=
    { toFun := stalkMap (tilde.map l) x
      map_add' := map_add _
      map_smul' := fun r z => (stalkMap (tilde.map l) x).map_smul
        (StructureSheaf.toStalk R x r) z }
  have hψ : ψ = IsLocalizedModule.map x.asIdeal.primeCompl
      (tilde.toStalk A x).hom (tilde.toStalk B x).hom l.hom := by
    apply IsLocalizedModule.linearMap_ext x.asIdeal.primeCompl (tilde.toStalk A x).hom
      (tilde.toStalk B x).hom
    ext a
    simp only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply]
    exact stalkMap_tilde_map_toStalk l x a
  change Function.Bijective ψ ↔ _
  rw [hψ]

/-- The counit of the tilde-sections adjunction sends the localization of a global
section to its germ. -/
lemma stalkMap_fromTildeΓ_toStalk (M : (Spec R).Modules) (x : Spec R)
    (s : moduleSpecΓFunctor.obj M) :
    stalkMap M.fromTildeΓ x ((tilde.toStalk (moduleSpecΓFunctor.obj M) x).hom s) =
      M.presheaf.germ ⊤ x trivial s := by
  change (TopCat.Presheaf.stalkFunctor Ab x).map M.fromTildeΓ.mapPresheaf
      (TopCat.Presheaf.germ (tilde _).presheaf ⊤ x trivial _) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  congr 1
  have h := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app M ⊤) s
  refine h.trans ?_
  change M.presheaf.map (homOfLE le_top).op s = s
  rw [show (homOfLE le_top : (⊤ : (Spec R).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end Tilde

/-- A finite presentation on an open restriction gives one on a smaller open
restriction factoring through it. -/
def presentationRestrictOfFac (M : X.Modules) {V : Scheme.{u}} (g : V ⟶ X)
    [IsOpenImmersion g] (k : W ⟶ V) [IsOpenImmersion k] (h : W ⟶ X) [IsOpenImmersion h]
    (hkg : k ≫ g = h) (P : (M.restrict g).Presentation) : (M.restrict h).Presentation :=
  (Scheme.Modules.presentationRestrict k P).ofIsIso
    (((Scheme.Modules.restrictFunctorComp k g).app M).inv ≫
      (Scheme.Modules.restrictFunctorCongr hkg).hom.app M)

instance (M : X.Modules) {V : Scheme.{u}} (g : V ⟶ X)
    [IsOpenImmersion g] (k : W ⟶ V) [IsOpenImmersion k] (h : W ⟶ X) [IsOpenImmersion h]
    (hkg : k ≫ g = h) (P : (M.restrict g).Presentation) [P.IsFinite] :
    (presentationRestrictOfFac M g k h hkg P).IsFinite := by
  dsimp [presentationRestrictOfFac, Scheme.Modules.presentationRestrict]
  infer_instance

/-- On an affine spectrum, the iso locus of a morphism between quasi-coherent module
sheaves is the iso locus of the induced morphism of sheaves associated to global
sections. -/
lemma mem_isoLocus_iff_tilde_map {R : CommRingCat.{u}} {F G : (Spec R).Modules}
    [IsIso F.fromTildeΓ] [IsIso G.fromTildeΓ] (φ : F ⟶ G) (y : Spec R) :
    y ∈ isoLocus φ ↔ y ∈ isoLocus (tilde.map (moduleSpecΓFunctor.map φ)) := by
  have hnat : F.fromTildeΓ ≫ φ = tilde.map (moduleSpecΓFunctor.map φ) ≫ G.fromTildeΓ :=
    (Scheme.Modules.fromTildeΓNatTrans.naturality φ).symm
  exact (mem_isoLocus_iff_of_comm (asIso F.fromTildeΓ) (asIso G.fromTildeΓ) _ _ hnat y).symm

/-- Bijectivity of the stalk map of `tilde.map l` at one point spreads to a principal
open neighbourhood when the source is finite and the target finitely presented. -/
lemma exists_basicOpen_subset_isoLocus_tilde {R : CommRingCat.{u}} {A B : ModuleCat.{u} R}
    [Module.Finite R A] [Module.FinitePresentation R B] (l : A ⟶ B) (x : Spec R)
    (hx : x ∈ isoLocus (tilde.map l)) :
    ∃ g : R, g ∉ x.asIdeal ∧ ∀ y : Spec R, g ∉ y.asIdeal → y ∈ isoLocus (tilde.map l) := by
  have h0 := (mem_isoLocus_tilde_map_iff l x).mp hx
  obtain ⟨g, hg, h⟩ := Langlands.CommutativeAlgebra.exists_notMem_forall_bijective l.hom
    x.asIdeal (tilde.toStalk A x).hom (tilde.toStalk B x).hom h0
  exact ⟨g, hg, fun y hy => (mem_isoLocus_tilde_map_iff l y).mpr
    (h y.asIdeal hy (tilde.toStalk A y).hom (tilde.toStalk B y).hom)⟩

/-- A finite presentation of a module sheaf on an affine spectrum gives a finitely
presented module of global sections over the coordinate ring. -/
lemma finitePresentation_moduleSpecΓFunctor_of_presentation {R : CommRingCat.{u}}
    {F : (Spec R).Modules} (P : F.Presentation) [P.IsFinite] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj F) := by
  have : Module.FinitePresentation Γ(Spec R, ⊤) Γ(F, ⊤) :=
    finitePresentation_sections_of_presentation F P ⊤ (isAffineOpen_top _)
  exact finitePresentation_moduleSpecΓFunctor F

/-- On an affine spectrum, bijectivity of the stalk map of a morphism between finitely
presented module sheaves spreads to a principal open neighbourhood. -/
lemma exists_basicOpen_subset_isoLocus {R : CommRingCat.{u}} {F G : (Spec R).Modules}
    (P : F.Presentation) [P.IsFinite] (Q : G.Presentation) [Q.IsFinite] (φ : F ⟶ G)
    (x : Spec R) (hx : x ∈ isoLocus φ) :
    ∃ g : R, g ∉ x.asIdeal ∧ ∀ y : Spec R, g ∉ y.asIdeal → y ∈ isoLocus φ := by
  have : IsIso F.fromTildeΓ := isIso_fromTildeΓ_of_presentation F P
  have : IsIso G.fromTildeΓ := isIso_fromTildeΓ_of_presentation G Q
  have := finitePresentation_moduleSpecΓFunctor_of_presentation P
  have := finitePresentation_moduleSpecΓFunctor_of_presentation Q
  obtain ⟨g, hg, h⟩ := exists_basicOpen_subset_isoLocus_tilde (moduleSpecΓFunctor.map φ) x
    ((mem_isoLocus_iff_tilde_map φ x).mp hx)
  exact ⟨g, hg, fun y hy => (mem_isoLocus_iff_tilde_map φ y).mpr (h y hy)⟩

/-- **Iso-locus openness.** For a morphism between locally finitely presented module
sheaves, the set of points with bijective stalk map is open. -/
lemma isOpen_isoLocus {F G : X.Modules} [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : F ⟶ G) : IsOpen (isoLocus φ) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨U₁, hz₁, P₁, hP₁⟩ := exists_finitePresentation_restrict F z
  obtain ⟨U₂, hz₂, P₂, hP₂⟩ := exists_finitePresentation_restrict G z
  obtain ⟨R, h, hh, ⟨b, hb⟩, hrange⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := U₁ ⊓ U₂) ⟨hz₁, hz₂⟩
  have h₁ : Set.range h ⊆ Set.range U₁.ι := by
    rw [Scheme.Opens.range_ι]; exact hrange.trans fun _ hx => hx.1
  have h₂ : Set.range h ⊆ Set.range U₂.ι := by
    rw [Scheme.Opens.range_ι]; exact hrange.trans fun _ hx => hx.2
  let P := presentationRestrictOfFac F U₁.ι (IsOpenImmersion.lift U₁.ι h h₁) h
    (IsOpenImmersion.lift_fac _ _ _) P₁
  let Q := presentationRestrictOfFac G U₂.ι (IsOpenImmersion.lift U₂.ι h h₂) h
    (IsOpenImmersion.lift_fac _ _ _) P₂
  have hb' : b ∈ isoLocus ((Scheme.Modules.restrictFunctor h).map φ) :=
    (mem_isoLocus_restrict_iff h φ b).mpr (hb ▸ hz)
  obtain ⟨g, hg, hD⟩ := exists_basicOpen_subset_isoLocus P Q _ b hb'
  refine ⟨h '' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)), ?_, ?_, ⟨b, hg, hb⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_isoLocus_restrict_iff h φ y).mp (hD y hy)
  · exact h.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen g).isOpen

/-- **Iso-locus openness by descent.** If the pullbacks of two module sheaves along a flat,
locally finitely presented surjection are locally finitely presented, the iso locus of any
morphism between them is open. -/
lemma isOpen_isoLocus_of_pullback (p : X ⟶ Y) [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] {F G : Y.Modules} (φ : F ⟶ G)
    [((Scheme.Modules.pullback p).obj F).IsFinitePresentation]
    [((Scheme.Modules.pullback p).obj G).IsFinitePresentation] : IsOpen (isoLocus φ) := by
  have h := isOpen_isoLocus ((Scheme.Modules.pullback p).map φ)
  have : isoLocus φ = p '' isoLocus ((Scheme.Modules.pullback p).map φ) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := p.surjective y
      exact ⟨x, (mem_isoLocus_pullback_iff p φ x).mpr hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (mem_isoLocus_pullback_iff p φ x).mp hx
  rw [this]
  exact p.isOpenMap _ h

end Langlands.AlgebraicGeometry.Modules
