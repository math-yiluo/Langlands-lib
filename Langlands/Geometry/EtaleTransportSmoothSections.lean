import Langlands.Geometry.EtaleTransportSections
import Langlands.Cohomology.DivisibleSystem.ScalarExtension

/-! # Smooth global sections of actual small-etale transport sheaves -/

noncomputable section

universe u w uR uM uI

namespace Langlands.Geometry.EtaleTransport.SmoothSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

variable {Y : Scheme.{u}} {G : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (ρ : G →* (Aut Y)ᵐᵒᵖ)
variable (R : Type uR) [CommRing R]

/-- Whole-scheme sections fixed by some open subgroup, with their actual group action. -/
def sections : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ SmoothRep.{uR, w, uM} R G :=
  sectionRepresentation ρ R ⋙ SmoothRep.smoothPartFunctor R G

instance sections_additive :
    (sections ρ R : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _).Additive :=
  inferInstanceAs (Functor.Additive
    (sectionRepresentation ρ R ⋙ SmoothRep.smoothPartFunctor R G))

instance sections_preservesFiniteLimits :
    PreservesFiniteLimits
      (sections ρ R : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) := by
  have : (SmoothRep.smoothPartFunctor R G : Rep.{uM} R G ⥤ _).IsRightAdjoint :=
    (SmoothRep.toRepSmoothPartAdjunction R G).isRightAdjoint
  exact inferInstanceAs (PreservesFiniteLimits
    (sectionRepresentation ρ R ⋙ SmoothRep.smoothPartFunctor R G))

/-- The actual inclusion into algebraic whole-scheme sections. -/
def inclusion :
    sections ρ R ⋙ SmoothRep.toRep ⟶
      (sectionRepresentation ρ R : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G) :=
  Functor.whiskerLeft (sectionRepresentation ρ R)
    (SmoothRep.toRepSmoothPartAdjunction R G).counit

@[simp]
theorem inclusion_app_apply (F : ModuleSheaf.{u, w, uR, uM} ρ R)
    (s : (sections ρ R).obj F) :
    ((inclusion ρ R).app F).hom s = s.val := rfl

omit [IsTopologicalGroup G] in
/-- Membership is fixation by the actual labelled whole-scheme maps of an open subgroup. -/
theorem mem_smoothVectors_iff (F : ModuleSheaf.{u, w, uR, uM} ρ R)
    (s : F.obj.obj (op (whole ρ))) :
    s ∈ smoothVectors ((sectionRepresentation ρ R).obj F).ρ ↔
      ∃ H : OpenSubgroup G, ∀ g : H,
        (F.obj.map (wholeMap ρ (g : G)).op).hom s = s := Iff.rfl

instance inclusion_app_mono (F : ModuleSheaf.{u, w, uR, uM} ρ R) :
    Mono ((inclusion ρ R).app F) :=
  (Rep.mono_iff_injective _).2 Subtype.val_injective

/-- Every intertwiner from a smooth representation factors through smooth global sections. -/
def lift {A : SmoothRep.{uR, w, uM} R G} {F : ModuleSheaf.{u, w, uR, uM} ρ R}
    (f : SmoothRep.toRep.obj A ⟶ (sectionRepresentation ρ R).obj F) :
    A ⟶ (sections ρ R).obj F :=
  (SmoothRep.toRepSmoothPartAdjunction R G).homEquiv A _ f

@[reassoc (attr := simp)]
theorem lift_inclusion {A : SmoothRep.{uR, w, uM} R G}
    {F : ModuleSheaf.{u, w, uR, uM} ρ R}
    (f : SmoothRep.toRep.obj A ⟶ (sectionRepresentation ρ R).obj F) :
    SmoothRep.toRep.map (lift ρ R f) ≫ (inclusion ρ R).app F = f := rfl

/-- The factorization through smooth global sections is unique. -/
theorem lift_unique {A : SmoothRep.{uR, w, uM} R G}
    {F : ModuleSheaf.{u, w, uR, uM} ρ R}
    (f : SmoothRep.toRep.obj A ⟶ (sectionRepresentation ρ R).obj F)
    (g : A ⟶ (sections ρ R).obj F)
    (h : SmoothRep.toRep.map g ≫ (inclusion ρ R).app F = f) :
    g = lift ρ R f := by
  apply SmoothRep.toRep.map_injective
  apply (cancel_mono ((inclusion ρ R).app F)).1
  exact h.trans (lift_inclusion ρ R f).symm

/-- If all global sections are smooth, the actual inclusion is an isomorphism. -/
def algebraicIsoOfSmooth (F : ModuleSheaf.{u, w, uR, uM} ρ R)
    (h : IsSmooth ((sectionRepresentation ρ R).obj F).ρ) :
    (sections ρ R ⋙ SmoothRep.toRep).obj F ≅ (sectionRepresentation ρ R).obj F :=
  Rep.mkIso (smoothEquiv h)

@[simp]
theorem algebraicIsoOfSmooth_hom (F : ModuleSheaf.{u, w, uR, uM} ρ R)
    (h : IsSmooth ((sectionRepresentation ρ R).obj F).ρ) :
    (algebraicIsoOfSmooth ρ R F h).hom = (inclusion ρ R).app F := rfl

omit [IsTopologicalGroup G] in
/-- The whole-scheme action of a discrete group is smooth. -/
theorem isSmooth_of_discreteTopology [DiscreteTopology G]
    (F : ModuleSheaf.{u, w, uR, uM} ρ R) :
    IsSmooth ((sectionRepresentation ρ R).obj F).ρ := by
  intro s
  refine ⟨⟨⊥, isOpen_discrete _⟩, ?_⟩
  change ∀ g : (⊥ : Subgroup G), _
  rintro ⟨g, hg⟩
  have hg' : g = 1 := Subgroup.mem_bot.mp hg
  subst g
  simp

/-- For a discrete acting group, smooth sections recover every algebraic section naturally. -/
def discreteIso [DiscreteTopology G] :
    sections ρ R ⋙ SmoothRep.toRep ≅
      (sectionRepresentation ρ R : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G) :=
  NatIso.ofComponents
    (fun F => algebraicIsoOfSmooth ρ R F (isSmooth_of_discreteTopology ρ R F))
    (fun f => (inclusion ρ R).naturality f)

variable {I : Type uI} (c : ComplexShape I)

/-- Every strict complex of transport sheaves gives an actual smooth representation complex. -/
def complex : HomologicalComplex (ModuleSheaf.{u, w, uR, uM} ρ R) c ⥤
    HomologicalComplex (SmoothRep.{uR, w, uM} R G) c :=
  (sections ρ R).mapHomologicalComplex c

/-- The strict section complex agrees with the published degreewise smooth-part construction. -/
def complexIso :
    complex ρ R c ≅ sectionComplex ρ R c ⋙
      Langlands.Cohomology.smoothPartComplex R G c :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (sectionRepresentation ρ R ⋙ SmoothRep.smoothPartFunctor R G)) c).symm

/-- The section inclusions form a natural chain map to the algebraic section complex. -/
def complexInclusion :
    complex ρ R c ⋙ SmoothRep.toRep.mapHomologicalComplex c ⟶
      (sectionComplex ρ R c : HomologicalComplex (ModuleSheaf.{u, w, uR, uM} ρ R) c ⥤ _) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (sections ρ R ⋙ SmoothRep.toRep)) c).hom ≫
    NatTrans.mapHomologicalComplex (inclusion ρ R) c

@[simp]
theorem complexInclusion_f (K : HomologicalComplex (ModuleSheaf.{u, w, uR, uM} ρ R) c)
    (i : I) :
    ((complexInclusion ρ R c).app K).f i = (inclusion ρ R).app (K.X i) := by
  change 𝟙 _ ≫ (inclusion ρ R).app (K.X i) = _
  simp

end Langlands.Geometry.EtaleTransport.SmoothSections
