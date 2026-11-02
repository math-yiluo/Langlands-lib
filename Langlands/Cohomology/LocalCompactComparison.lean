import Langlands.Cohomology.ProperCompactComplexes
import Langlands.Cohomology.EquivariantSections
import Langlands.Sheaf.Equivariant.LocalSupportComparison

/-! # Local-vanishing and stalk compact-section complexes -/

noncomputable section

universe u v t

open CategoryTheory HomologicalComplex

namespace Langlands.Cohomology.LocalCompactComparison

open Langlands.Sheaf.Equivariant

variable (R : Type u) [CommRing R] (G : Type v) [Group G]
  (X : Type u) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] {I : Type t} (c : ComplexShape I)

/-- Both constructions use the same original global-section functor. -/
def globalComplexIso :
    ProperCompactComplexes.globalComplex R G X c ≅
      EquivariantSections.globalComplex R G X c :=
  Iso.refl _

/-- The proved equality of support conditions gives a natural chain isomorphism. -/
def compactComplexIso :
    ProperCompactComplexes.compactComplex R G X c ≅
      EquivariantSections.compactComplex R G X c :=
  NatIso.mapHomologicalComplex (LocalCompactSections.stalkComparison R G X) c

/-- In each degree the comparison is the original identity-on-sections isomorphism. -/
@[simp]
theorem compactComplexIso_hom_f
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    ((compactComplexIso R G X c).hom.app F).f i =
      (LocalCompactSections.stalkRepIso (F.X i).obj).hom := rfl

@[simp]
theorem compactComplexIso_inv_f
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    ((compactComplexIso R G X c).inv.app F).f i =
      (LocalCompactSections.stalkRepIso (F.X i).obj).inv := rfl

@[simp]
theorem compactComplexIso_hom_apply
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I)
    (s : Langlands.Sheaf.LocalSupport.submodule
      (LocalCompactSections.ordinary (F.X i).obj)) :
    ((((compactComplexIso R G X c).hom.app F).f i).hom s).val = s.val := rfl

@[simp]
theorem compactComplexIso_inv_apply
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I)
    (s : Langlands.Sheaf.CompactSupport.submodule
      (CompactSections.ordinary (F.X i).obj)) :
    ((((compactComplexIso R G X c).inv.app F).f i).hom s).val = s.val := rfl

/-- The chain comparison commutes with the actual support-forgetting inclusions. -/
theorem inclusion_triangle :
    (compactComplexIso R G X c).hom ≫
        EquivariantSections.forgetSupportComplex R G X c =
      ProperCompactComplexes.inclusionComplex R G X c ≫
        (globalComplexIso R G X c).hom := by
  ext F i s
  rfl

/-- Applying actual homology preserves the comparison of compact-section complexes. -/
def compactHomologyIso (i : I) :
    ProperCompactComplexes.compactHomology R G X c i ≅
      EquivariantSections.compactHomology R G X c i :=
  Functor.isoWhiskerRight (compactComplexIso R G X c)
    (homologyFunctor (Rep.{u} R G) c i)

/-- The two global homology functors retain the same action. -/
def globalHomologyIso (i : I) :
    ProperCompactComplexes.globalHomology R G X c i ≅
      EquivariantSections.globalHomology R G X c i :=
  Functor.isoWhiskerRight (globalComplexIso R G X c)
    (homologyFunctor (Rep.{u} R G) c i)

theorem inclusionHomology_triangle
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    (compactHomologyIso R G X c i).hom.app F ≫
        (EquivariantSections.forgetSupportHomology R G X c i).app F =
      (ProperCompactComplexes.inclusionHomology R G X c i).app F ≫
        (globalHomologyIso R G X c i).hom.app F := by
  simpa only [compactHomologyIso, globalHomologyIso,
    EquivariantSections.forgetSupportHomology, ProperCompactComplexes.inclusionHomology,
    ProperCompactComplexes.compactHomology, ProperCompactComplexes.globalHomology,
    EquivariantSections.compactHomology, EquivariantSections.globalHomology,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_obj, Functor.map_comp] using
    congrArg (fun k => (homologyFunctor (Rep.{u} R G) c i).map k)
      (congrArg (fun a => a.app F) (inclusion_triangle R G X c))

variable {R G X}
  {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G Y] [MulAction G Z] [ContinuousConstSMul G Y]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Transport genuine proper compact pullback to the existing stalk-support complex. -/
def properComplex (hp : IsProperMap f) :
    ProperCompactComplexes.directImageComplex c f hf ⋙
        EquivariantSections.compactComplex R G Y c ⟶
      EquivariantSections.compactComplex R G X c :=
  Functor.whiskerLeft (ProperCompactComplexes.directImageComplex c f hf)
      (compactComplexIso R G Y c).inv ≫
    ProperCompactComplexes.properComplex c f hf hp ≫ (compactComplexIso R G X c).hom

/-- The transported map uses the original section without changing its value. -/
@[simp]
theorem properComplex_apply (hp : IsProperMap f)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I)
    (s : Langlands.Sheaf.CompactSupport.submodule
      (CompactSections.ordinary
        (((ProperCompactComplexes.directImageComplex c f hf).obj F).X i).obj)) :
    ((((properComplex c f hf hp).app F).f i).hom s).val = s.val := rfl

/-- The two support conventions give the same proper spatial chain map. -/
theorem properComplex_comparison (hp : IsProperMap f) :
    Functor.whiskerLeft (ProperCompactComplexes.directImageComplex c f hf)
        (compactComplexIso R G Y c).hom ≫ properComplex c f hf hp =
      ProperCompactComplexes.properComplex c f hf hp ≫
        (compactComplexIso R G X c).hom := by
  ext F i s
  rfl

/-- Forgetting stalk support recovers the original global-section identification. -/
theorem properComplex_inclusion_triangle (hp : IsProperMap f)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) :
    (properComplex c f hf hp).app F ≫
        (EquivariantSections.forgetSupportComplex R G X c).app F =
      (EquivariantSections.forgetSupportComplex R G Y c).app
          ((ProperCompactComplexes.directImageComplex c f hf).obj F) ≫
        (ProperCompactComplexes.globalComplexIso c f hf).hom.app F := by
  ext i s
  rfl

@[simp]
theorem properComplex_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) :
    (properComplex c (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id).app F =
      𝟙 ((EquivariantSections.compactComplex R G X c).obj F) := by
  ext i s
  rfl

theorem properComplex_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) :
    (properComplex c (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp)).app F =
      (properComplex c g hg hq).app
          ((ProperCompactComplexes.directImageComplex c f hf).obj F) ≫
        (properComplex c f hf hp).app F := by
  ext i s
  rfl

/-- Homology of the transported proper chain map retains the stalk-support action. -/
def properHomology (hp : IsProperMap f) (i : I) :
    ProperCompactComplexes.directImageComplex c f hf ⋙
        EquivariantSections.compactHomology R G Y c i ⟶
      EquivariantSections.compactHomology R G X c i :=
  Functor.whiskerRight (properComplex c f hf hp)
    (homologyFunctor (Rep.{u} R G) c i)

/-- The support comparison intertwines the actual proper homology maps. -/
theorem properHomology_comparison (hp : IsProperMap f)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    (compactHomologyIso R G Y c i).hom.app
          ((ProperCompactComplexes.directImageComplex c f hf).obj F) ≫
        (properHomology c f hf hp i).app F =
      (ProperCompactComplexes.properHomology c f hf hp i).app F ≫
        (compactHomologyIso R G X c i).hom.app F := by
  simpa only [properHomology, ProperCompactComplexes.properHomology,
    ProperCompactComplexes.compactHomology, EquivariantSections.compactHomology,
    compactHomologyIso, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, Functor.map_comp] using congrArg
    (fun k => (homologyFunctor (Rep.{u} R G) c i).map k)
    (congrArg (fun a => a.app F) (properComplex_comparison c f hf hp))

set_option backward.isDefEq.respectTransparency false in
theorem properHomology_inclusion_triangle (hp : IsProperMap f)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    (properHomology c f hf hp i).app F ≫
        (EquivariantSections.forgetSupportHomology R G X c i).app F =
      (EquivariantSections.forgetSupportHomology R G Y c i).app
          ((ProperCompactComplexes.directImageComplex c f hf).obj F) ≫
        (ProperCompactComplexes.globalHomologyIso c f hf i).hom.app F := by
  simpa only [properHomology, EquivariantSections.forgetSupportHomology,
    EquivariantSections.compactHomology, EquivariantSections.globalHomology,
    ProperCompactComplexes.globalHomology,
    ProperCompactComplexes.globalHomologyIso, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.map_comp] using congrArg
    (fun k => (homologyFunctor (Rep.{u} R G) c i).map k)
    (properComplex_inclusion_triangle c f hf hp F)

@[simp]
theorem properHomology_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    (properHomology c (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id i).app F =
      𝟙 ((EquivariantSections.compactHomology R G X c i).obj F) := by
  change (homologyFunctor (Rep.{u} R G) c i).map _ = _
  rw [properComplex_id]
  exact (homologyFunctor (Rep.{u} R G) c i).map_id _

theorem properHomology_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    (properHomology c (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) i).app F =
      (properHomology c g hg hq i).app
          ((ProperCompactComplexes.directImageComplex c f hf).obj F) ≫
        (properHomology c f hf hp i).app F := by
  change (homologyFunctor (Rep.{u} R G) c i).map _ = _
  rw [properComplex_comp c f hf g hg hp hq F]
  exact (homologyFunctor (Rep.{u} R G) c i).map_comp _ _

variable {c}
  {K : HomologicalComplex (TopologicalSheaf G Y (ModuleCat.{u} R)) c}
  {F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c}

/-- A genuine chain map into direct image induces stalk compact spatial pullback. -/
def pullbackComplex (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) :
    (EquivariantSections.compactComplex R G Y c).obj K ⟶
      (EquivariantSections.compactComplex R G X c).obj F :=
  (EquivariantSections.compactComplex R G Y c).map b ≫
    (properComplex c f hf hp).app F

/-- The map on original sections is the given degreewise global sheaf component. -/
@[simp]
theorem pullbackComplex_apply (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) (i : I)
    (s : Langlands.Sheaf.CompactSupport.submodule
      (CompactSections.ordinary (K.X i).obj)) :
    (((pullbackComplex f hf hp b).f i).hom s).val =
      ((b.f i).hom.app (Opposite.op ActionOpens.top)).hom s.val := rfl

/-- Comparison identifies pullback of the same genuine input chain map. -/
theorem pullbackComplex_comparison (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) :
    (compactComplexIso R G Y c).hom.app K ≫ pullbackComplex f hf hp b =
      ProperCompactComplexes.pullbackComplex f hf hp b ≫
        (compactComplexIso R G X c).hom.app F := by
  ext i s
  rfl

theorem pullbackComplex_inclusion_triangle (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) :
    pullbackComplex f hf hp b ≫
        (EquivariantSections.forgetSupportComplex R G X c).app F =
      (EquivariantSections.forgetSupportComplex R G Y c).app K ≫
        (EquivariantSections.globalComplex R G Y c).map b ≫
          (ProperCompactComplexes.globalComplexIso c f hf).hom.app F := by
  ext i s
  rfl

@[simp]
theorem pullbackComplex_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) :
    pullbackComplex (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id (𝟙 F) =
      𝟙 ((EquivariantSections.compactComplex R G X c).obj F) := by
  ext i s
  rfl

theorem pullbackComplex_precomp (hp : IsProperMap f)
    {K' : HomologicalComplex (TopologicalSheaf G Y (ModuleCat.{u} R)) c}
    (a : K' ⟶ K)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) :
    pullbackComplex f hf hp (a ≫ b) =
      (EquivariantSections.compactComplex R G Y c).map a ≫
        pullbackComplex f hf hp b := by
  ext i s
  rfl

theorem pullbackComplex_postcomp (hp : IsProperMap f)
    {F' : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c}
    (a : F ⟶ F')
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) :
    pullbackComplex f hf hp (b ≫ (ProperCompactComplexes.directImageComplex c f hf).map a) =
      pullbackComplex f hf hp b ≫
        (EquivariantSections.compactComplex R G X c).map a := by
  ext i s
  rfl

theorem pullbackComplex_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    {L : HomologicalComplex (TopologicalSheaf G Z (ModuleCat.{u} R)) c}
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F)
    (a : L ⟶ (ProperCompactComplexes.directImageComplex c g hg).obj K) :
    pullbackComplex (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) (a ≫ (ProperCompactComplexes.directImageComplex c g hg).map b) =
      pullbackComplex g hg hq a ≫ pullbackComplex f hf hp b := by
  ext i s
  rfl

/-- Actual homology of the constructed stalk compact pullback. -/
def pullbackHomology (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) (i : I) :
    (EquivariantSections.compactHomology R G Y c i).obj K ⟶
      (EquivariantSections.compactHomology R G X c i).obj F :=
  (homologyFunctor (Rep.{u} R G) c i).map (pullbackComplex f hf hp b)

theorem pullbackHomology_factor (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp b i =
      (EquivariantSections.compactHomology R G Y c i).map b ≫
        (properHomology c f hf hp i).app F :=
  (homologyFunctor (Rep.{u} R G) c i).map_comp _ _

theorem pullbackHomology_comparison (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) (i : I) :
    (compactHomologyIso R G Y c i).hom.app K ≫ pullbackHomology f hf hp b i =
      ProperCompactComplexes.pullbackHomology f hf hp b i ≫
        (compactHomologyIso R G X c i).hom.app F := by
  simpa only [pullbackHomology, ProperCompactComplexes.pullbackHomology,
    ProperCompactComplexes.compactHomology, EquivariantSections.compactHomology,
    compactHomologyIso, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.map_comp] using congrArg
    (fun k => (homologyFunctor (Rep.{u} R G) c i).map k)
    (pullbackComplex_comparison f hf hp b)

set_option backward.isDefEq.respectTransparency false in
theorem pullbackHomology_inclusion_triangle (hp : IsProperMap f)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp b i ≫
        (EquivariantSections.forgetSupportHomology R G X c i).app F =
      (EquivariantSections.forgetSupportHomology R G Y c i).app K ≫
        (EquivariantSections.globalHomology R G Y c i).map b ≫
          (ProperCompactComplexes.globalHomologyIso c f hf i).hom.app F := by
  simpa only [pullbackHomology, EquivariantSections.forgetSupportHomology,
    ProperCompactComplexes.globalHomologyIso, EquivariantSections.globalHomology,
    ProperCompactComplexes.globalHomology, EquivariantSections.compactHomology,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp] using congrArg
    (fun k => (homologyFunctor (Rep.{u} R G) c i).map k)
    (pullbackComplex_inclusion_triangle f hf hp b)

@[simp]
theorem pullbackHomology_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    pullbackHomology (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id (𝟙 F) i =
      𝟙 ((EquivariantSections.compactHomology R G X c i).obj F) := by
  unfold pullbackHomology
  rw [pullbackComplex_id]
  exact (homologyFunctor (Rep.{u} R G) c i).map_id _

theorem pullbackHomology_precomp (hp : IsProperMap f)
    {K' : HomologicalComplex (TopologicalSheaf G Y (ModuleCat.{u} R)) c}
    (a : K' ⟶ K)
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp (a ≫ b) i =
      (EquivariantSections.compactHomology R G Y c i).map a ≫
        pullbackHomology f hf hp b i := by
  simp only [pullbackHomology, pullbackComplex_precomp, Functor.map_comp]
  rfl

theorem pullbackHomology_postcomp (hp : IsProperMap f)
    {F' : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c}
    (a : F ⟶ F')
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp (b ≫ (ProperCompactComplexes.directImageComplex c f hf).map a) i =
      pullbackHomology f hf hp b i ≫
        (EquivariantSections.compactHomology R G X c i).map a := by
  simp only [pullbackHomology, pullbackComplex_postcomp, Functor.map_comp]
  rfl

theorem pullbackHomology_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    {L : HomologicalComplex (TopologicalSheaf G Z (ModuleCat.{u} R)) c}
    (b : K ⟶ (ProperCompactComplexes.directImageComplex c f hf).obj F)
    (a : L ⟶ (ProperCompactComplexes.directImageComplex c g hg).obj K) (i : I) :
    pullbackHomology (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) (a ≫ (ProperCompactComplexes.directImageComplex c g hg).map b) i =
      pullbackHomology g hg hq a i ≫ pullbackHomology f hf hp b i := by
  unfold pullbackHomology
  rw [pullbackComplex_comp f hf g hg hp hq b a]
  exact (homologyFunctor (Rep.{u} R G) c i).map_comp _ _

end Langlands.Cohomology.LocalCompactComparison
