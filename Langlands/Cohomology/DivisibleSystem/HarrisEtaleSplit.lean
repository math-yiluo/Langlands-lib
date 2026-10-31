import Langlands.Cohomology.DivisibleSystem.HarrisEtale
import Langlands.Shimura.Coefficients.VaryingCoverLocalTrivialization

/-!
# Global sections of Harris's étale coefficient sheaves over split torsors

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §4, p.311: "the
inverse system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf". The published
`harrisEtaleSectionsDivisibleSystem` is the `ℓ`-divisible system of global sections of the
published model `harrisEtaleDivisibleSystem` of these sheaves, under the explicit hypothesis
`hΓ` that global sections of the maps `j` are epimorphisms; global sections are not right
exact. This module proves `hΓ` in the split case, when every torsor `Y m` has a global section
(hypothesis `hs`):

* `constantForgetSection`, `constantForgetSection_comp`, `iso_conj_section_comp`,
  `surjective_constantSheaf_map_app`: on a site where the forgetful functor from modules to
  sets commutes with sheafification, the constant sheaf of a surjective linear map is
  surjective on sections over every object, since the constant presheaf of sets of a
  surjection has a section;
* `smallEtaleTopology_preservesSheafification`: this commutation holds on the small étale
  site of a scheme, since both coefficient categories satisfy `WEqualsLocallyBijective`;
* `epi_sections_map_of_surjective`, `epi_sections_constantSheaf_map`: surjectivity on
  sections over the terminal object of the small étale site gives epimorphisms on global
  sections;
* `surjective_etaleAssociatedTransition_app_top`: a section of `Y i` trivializes the sheaves
  associated to `Y i` and `Y j` compatibly with the published transition
  `etaleAssociatedTransition` (Worker 13's `etaleAssociatedTrivializationAlong`), so the
  transition is surjective over the terminal object when the coefficient map is surjective;
* `EquivariantStructure.epi_sections_etaleSystem_projection`,
  `EquivariantStructure.etaleSplitSectionsSystem`,
  `EquivariantStructure.etaleSplitSectionsSystem_tower`: the general case of the published
  `etaleSystem`;
* `epi_sections_harrisEtaleDivisibleSystem_projection`,
  `harrisEtaleSplitSectionsDivisibleSystem`: Harris's case; the tower of the second is, by
  definition, the published `harrisEtaleSectionsSystem`.

Harris makes no splitness assumption on his covers of level `K(N, m)`; the split case is a
special case chosen here, and the statements and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w u' uI vI

namespace DivisibleSystem

section ConstantSheaf

variable {C : Type u'} [Category.{v} C] (J : GrothendieckTopology C) {R : Type w} [Ring R]

/-- A set-theoretic section of a surjective linear map `π : M ⟶ M'`, as a morphism of the
underlying constant presheaves of sets. -/
def constantForgetSection {M M' : ModuleCat.{w} R} (π : M ⟶ M') (hπ : Function.Surjective π) :
    (Functor.const Cᵒᵖ).obj M' ⋙ CategoryTheory.forget (ModuleCat.{w} R) ⟶
      (Functor.const Cᵒᵖ).obj M ⋙ CategoryTheory.forget (ModuleCat.{w} R) where
  app _ := TypeCat.ofHom (Function.surjInv hπ)

/-- `constantForgetSection π hπ` is a section of the constant map of `π`. -/
lemma constantForgetSection_comp {M M' : ModuleCat.{w} R} (π : M ⟶ M')
    (hπ : Function.Surjective π) :
    constantForgetSection π hπ ≫
        Functor.whiskerRight ((Functor.const Cᵒᵖ).map π)
          (CategoryTheory.forget (ModuleCat.{w} R)) = 𝟙 _ := by
  ext U x
  exact Function.surjInv_eq hπ x

/-- Conjugating a section of `p` and `p` itself by the same pair of isomorphisms gives a
section again. -/
lemma iso_conj_section_comp {D : Type*} [Category D] {X Y X' Y' : D} (eX : X ≅ X')
    (eY : Y ≅ Y') (s : Y ⟶ X) (p : X ⟶ Y) (hs : s ≫ p = 𝟙 Y) :
    (eY.inv ≫ s ≫ eX.hom) ≫ (eX.inv ≫ p ≫ eY.hom) = 𝟙 Y' := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hs, Iso.inv_hom_id]

variable [HasWeakSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{w} R))]
  [J.PreservesSheafification (CategoryTheory.forget (ModuleCat.{w} R))]

/-- If the forgetful functor preserves sheafification, the constant sheaf of a surjective
linear map is surjective on sections over every object. -/
lemma surjective_constantSheaf_map_app {M M' : ModuleCat.{w} R} (π : M ⟶ M')
    (hπ : Function.Surjective π) (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J (ModuleCat.{w} R)).map π).hom.app U) := by
  let e := sheafComposeNatIso J (CategoryTheory.forget (ModuleCat.{w} R))
    (sheafificationAdjunction J (ModuleCat.{w} R)) (sheafificationAdjunction J (Type w))
  let c := (Functor.const Cᵒᵖ).map π
  let s := (presheafToSheaf J (Type w)).map (constantForgetSection π hπ)
  have hs : s ≫ (presheafToSheaf J (Type w)).map
      (Functor.whiskerRight c (CategoryTheory.forget (ModuleCat.{w} R))) = 𝟙 _ :=
    ((presheafToSheaf J (Type w)).map_comp _ _).symm.trans
      ((congrArg (presheafToSheaf J (Type w)).map (constantForgetSection_comp π hπ)).trans
        ((presheafToSheaf J (Type w)).map_id _))
  have hc : (sheafCompose J (CategoryTheory.forget (ModuleCat.{w} R))).map
      ((constantSheaf J (ModuleCat.{w} R)).map π) =
      e.inv.app _ ≫ (presheafToSheaf J (Type w)).map
        (Functor.whiskerRight c (CategoryTheory.forget (ModuleCat.{w} R))) ≫ e.hom.app _ :=
    (NatIso.naturality_1 e c).symm
  let t := e.inv.app _ ≫ s ≫ e.hom.app _
  have ht := (congrArg (fun φ => t ≫ φ) hc).trans
    (iso_conj_section_comp (e.app _) (e.app _) s _ hs)
  have h1 : t.hom.app U ≫ ((sheafCompose J (CategoryTheory.forget (ModuleCat.{w} R))).map
      ((constantSheaf J (ModuleCat.{w} R)).map π)).hom.app U = 𝟙 _ :=
    congrArg (fun φ => φ.hom.app U) ht
  have h2 : Function.Surjective (((sheafCompose J (CategoryTheory.forget (ModuleCat.{w} R))).map
      ((constantSheaf J (ModuleCat.{w} R)).map π)).hom.app U) := fun y =>
    ⟨(t.hom.app U) y, (types_comp_apply _ _ _).symm.trans
      ((types_congr_hom h1 y).trans (types_id_apply _ _))⟩
  intro y
  obtain ⟨x, hx⟩ := h2 y
  exact ⟨x, hx⟩

end ConstantSheaf

section Etale

open Langlands.Geometry.EtaleDerivedSections Langlands.Shimura.Coefficients

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- On the small étale site, the forgetful functor from sheaves of modules to sheaves of sets
commutes with sheafification: both coefficient categories satisfy `WEqualsLocallyBijective`. -/
instance smallEtaleTopology_preservesSheafification :
    X.smallEtaleTopology.PreservesSheafification (CategoryTheory.forget (ModuleCat.{u} R)) where
  le _ _ f hf := by
    have := hf.isLocallyInjective
    have := hf.isLocallySurjective
    exact (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_forget _ f,
        (Presheaf.isLocallySurjective_iff_whisker_forget _ f).1 inferInstance⟩

/-- A morphism of étale sheaves of modules which is surjective on sections over the terminal
object of the small étale site is an epimorphism on global sections. -/
lemma epi_sections_map_of_surjective {F G : ModuleSheaf X R} (φ : F ⟶ G)
    (hφ : Function.Surjective (φ.hom.app (op (⊤_ X.Etale)))) :
    Epi ((sections X R).map φ) := by
  have : Epi (φ.hom.app (op (⊤_ X.Etale))) := (ModuleCat.epi_iff_surjective _).2 hφ
  have h : (sections X R).map φ ≫ (sectionsIso X R).hom.app G =
      (sectionsIso X R).hom.app F ≫ φ.hom.app (op (⊤_ X.Etale)) :=
    (sectionsIso X R).hom.naturality φ
  have : Epi ((sections X R).map φ ≫ (sectionsIso X R).hom.app G) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).1 this

/-- The constant étale sheaf of a surjective linear map is an epimorphism on global
sections. -/
lemma epi_sections_constantSheaf_map {M M' : ModuleCat.{u} R} (π : M ⟶ M')
    (hπ : Function.Surjective π) :
    Epi ((sections X R).map ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map π)) :=
  epi_sections_map_of_surjective X R _
    (surjective_constantSheaf_map_app X.smallEtaleTopology π hπ _)

variable {X R} {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
  (Y : EquivariantDiagram D X.Etale) (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))

/-- If the torsor `Y i` has a global section `s`, then the transition between associated
sheaves along `f : i ⟶ j` is surjective on sections over the terminal object whenever the
coefficient map along `f` is surjective: evaluation along `s` and along `s ≫ Y f` trivializes
both sheaves compatibly with the transition. -/
lemma surjective_etaleAssociatedTransition_app_top (M : EquivariantDiagram D (ModuleCat.{u} R))
    {i j : I} (f : i ⟶ j) (s : ⊤_ X.Etale ⟶ Y.obj.obj i)
    (hf : Function.Surjective (M.obj.map f)) :
    Function.Surjective (((etaleAssociatedTransition X Y hY f).app M).hom.app
      (op (⊤_ X.Etale))) := by
  let V : (Over (⊤_ X.Etale))ᵒᵖ := op (Over.mk (𝟙 _))
  let ei := ((sheafToPresheaf _ _).mapIso
    (etaleAssociatedTrivializationAlong X Y hY M i s)).app V
  let ej := ((sheafToPresheaf _ _).mapIso
    (etaleAssociatedTrivializationAlong X Y hY M j (s ≫ Y.obj.map f))).app V
  have hc : Epi (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (M.obj.map f)).hom.app (op (⊤_ X.Etale))) :=
    (ModuleCat.epi_iff_surjective _).2
      (surjective_constantSheaf_map_app X.smallEtaleTopology _ hf _)
  have h : ((etaleAssociatedTransition X Y hY f).app M).hom.app (op (⊤_ X.Etale)) ≫ ej.hom =
      ei.hom ≫ ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (M.obj.map f)).hom.app (op (⊤_ X.Etale)) :=
    congrArg (fun φ => φ.hom.app V) (etaleAssociatedTransition_evaluationAlong X Y hY M f s)
  have : Epi (((etaleAssociatedTransition X Y hY f).app M).hom.app (op (⊤_ X.Etale)) ≫
      ej.hom) := by
    rw [h]
    exact epi_comp' (IsIso.epi_of_iso ei.hom) hc
  exact (ModuleCat.epi_iff_surjective _).1 ((epi_comp_iff_of_isIso _ ej.hom).1 this)

end Etale

section Split

open Langlands.Geometry.EtaleDerivedSections Langlands.Shimura.Coefficients

variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ℓ : ℕ}
variable {D : ℕᵒᵖ ⥤ GrpCat.{u}} (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))
variable {T : DivisibleSystem (ModuleCat.{u} R) ℓ} (A : T.EquivariantStructure D)

namespace EquivariantStructure

/-- If every torsor `Y m` has a global section, global sections of the maps `j` of the étale
`ℓ`-divisible system `etaleSystem` are epimorphisms. -/
lemma epi_sections_etaleSystem_projection
    (hs : ∀ n : ℕ, Nonempty (⊤_ X.Etale ⟶ Y.obj.obj (op n))) {m' m : ℕ} (h : m' ≤ m) :
    Epi ((sections X R).map ((A.etaleSystem X Y hY).projection h)) := by
  obtain ⟨s⟩ := hs m
  exact epi_sections_map_of_surjective X R _
    (surjective_etaleAssociatedTransition_app_top Y hY A.diagram (homOfLE h).op s
      ((ModuleCat.epi_iff_surjective _).1 (T.epi_projection h)))

/-- Global sections of the étale `ℓ`-divisible system `etaleSystem`, when every torsor `Y m`
has a global section. -/
def etaleSplitSectionsSystem (hs : ∀ n : ℕ, Nonempty (⊤_ X.Etale ⟶ Y.obj.obj (op n))) :
    DivisibleSystem (ModuleCat.{u} R) ℓ :=
  (A.etaleSystem X Y hY).mapLeftExact (sections X R)
    (A.epi_sections_etaleSystem_projection Y hY hs)

/-- The tower of `etaleSplitSectionsSystem` is the global sections of the published
`etaleAssociatedVaryingSystem`. -/
lemma etaleSplitSectionsSystem_tower
    (hs : ∀ n : ℕ, Nonempty (⊤_ X.Etale ⟶ Y.obj.obj (op n))) :
    (A.etaleSplitSectionsSystem Y hY hs).tower =
      etaleAssociatedVaryingSystem X Y hY A.diagram ⋙ sections X R :=
  rfl

end EquivariantStructure

end Split

section Harris

open Langlands.Global Langlands.Shimura Langlands.Shimura.Coefficients
  Langlands.Geometry.EtaleDerivedSections

variable (ℓ : ℕ) [NeZero ℓ]
variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))
variable (hs : ∀ n : ℕ, Nonempty (⊤_ X.Etale ⟶ Y.obj.obj (op n)))

include hs in
/-- If every torsor `Y m` has a global section, global sections of the maps `j` of Harris's
étale `ℓ`-divisible system are epimorphisms. This is the hypothesis of
`harrisEtaleSectionsDivisibleSystem`, proved in this split case. -/
lemma epi_sections_harrisEtaleDivisibleSystem_projection {m' m : ℕ} (h : m' ≤ m) :
    Epi ((sections X (HarrisCoefficientIntegers L p)).map
      ((harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).projection h)) :=
  (harrisEquivariantStructure ℓ ρ p U).epi_sections_etaleSystem_projection Y hY hs h

/-- Global sections of Harris's étale `ℓ`-divisible system when every torsor `Y m` has a
global section, with the surjectivity hypothesis of `harrisEtaleSectionsDivisibleSystem`
proved. -/
def harrisEtaleSplitSectionsDivisibleSystem :
    DivisibleSystem (ModuleCat.{u} (HarrisCoefficientIntegers L p)) ℓ :=
  harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY
    (epi_sections_harrisEtaleDivisibleSystem_projection ℓ ρ p U X Y hY hs)

/-- The tower of `harrisEtaleSplitSectionsDivisibleSystem` is the published
`harrisEtaleSectionsSystem`. -/
lemma harrisEtaleSplitSectionsDivisibleSystem_tower :
    (harrisEtaleSplitSectionsDivisibleSystem ℓ ρ p U X Y hY hs).tower =
      harrisEtaleSectionsSystem ρ p U ℓ X Y hY :=
  rfl

end Harris

end DivisibleSystem

end Langlands.Cohomology
