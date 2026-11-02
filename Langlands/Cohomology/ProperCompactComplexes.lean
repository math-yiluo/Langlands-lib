import Langlands.Sheaf.Equivariant.ProperCompactSections
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Proper spatial maps on complexes of full equivariant compact sections -/

noncomputable section

universe u v r w t

open CategoryTheory HomologicalComplex

namespace Langlands.Sheaf.Equivariant.LocalCompactSections

variable (R : Type r) [CommRing R] (G : Type v) [Group G]
  (X : Type u) [TopologicalSpace X] [MulAction G X]

instance globalFunctor_additive : (globalFunctor R G X : TopologicalSheaf G X (ModuleCat.{w} R) ⥤ Rep.{w} R G).Additive where
  map_add {F F'} {a b} := by ext s; rfl

variable [ContinuousConstSMul G X]

instance presheafFunctor_additive : (presheafFunctor R G X : ((ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Rep.{w} R G).Additive where
  map_add {F F'} {a b} := by ext s; rfl

instance functor_additive : (functor R G X : TopologicalSheaf G X (ModuleCat.{w} R) ⥤ Rep.{w} R G).Additive where
  map_add {F F'} {a b} := by ext s; rfl

end Langlands.Sheaf.Equivariant.LocalCompactSections

namespace Langlands.Sheaf.Equivariant.DirectImage

variable {R : Type r} [CommRing R] {G : Type v} [Group G]
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G X] [MulAction G Y]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

instance presheaf_additive : (presheaf f hf (ModuleCat.{w} R)).Additive where
  map_add {F F'} {a b} := by ext U s; rfl

instance sheaf_additive : (sheaf f hf (ModuleCat.{w} R)).Additive where
  map_add {F F'} {a b} := by
    apply ObjectProperty.hom_ext
    ext U s
    rfl

end Langlands.Sheaf.Equivariant.DirectImage

namespace Langlands.Cohomology.ProperCompactComplexes

open Langlands.Sheaf.Equivariant

variable (R : Type r) [CommRing R] (G : Type v) [Group G]
  (X : Type u) [TopologicalSpace X] [MulAction G X]
  {I : Type t} (c : ComplexShape I)

/-- Each differential is the original equivariant map on global sections. -/
def globalComplex :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c ⥤
      HomologicalComplex (Rep.{w} R G) c :=
  (LocalCompactSections.globalFunctor R G X).mapHomologicalComplex c

variable [ContinuousConstSMul G X]

/-- Each term consists of all sections whose actual local support is compact. -/
def compactComplex :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c ⥤
      HomologicalComplex (Rep.{w} R G) c :=
  (LocalCompactSections.functor R G X).mapHomologicalComplex c

/-- Inclusion of the actual support submodules in every degree. -/
def inclusionComplex : compactComplex R G X c ⟶ globalComplex R G X c :=
  NatTrans.mapHomologicalComplex (LocalCompactSections.inclusion R G X) c

/-- Homology is formed in the abelian category of all algebraic representations. -/
def compactHomology (i : I) :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c ⥤ Rep.{w} R G :=
  compactComplex R G X c ⋙ homologyFunctor (Rep.{w} R G) c i

/-- The homology representation of the full global-section complex. -/
def globalHomology (i : I) :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c ⥤ Rep.{w} R G :=
  globalComplex R G X c ⋙ homologyFunctor (Rep.{w} R G) c i

/-- The actual chain inclusion induces the support-forgetting map on homology. -/
def inclusionHomology (i : I) :
    compactHomology R G X c i ⟶ globalHomology R G X c i :=
  Functor.whiskerRight (inclusionComplex R G X c)
    (homologyFunctor (Rep.{w} R G) c i)

variable {R G X}
  {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G Y] [MulAction G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Direct image of each complete sheaf, differential and chain-map component. -/
def directImageComplex :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c ⥤
      HomologicalComplex (TopologicalSheaf G Y (ModuleCat.{w} R)) c :=
  (DirectImage.sheaf f hf (ModuleCat.{w} R)).mapHomologicalComplex c

variable [ContinuousConstSMul G Y]

/-- Direct image retains the original global-section complex. -/
def globalComplexIso :
    directImageComplex c f hf ⋙ globalComplex R G Y c ≅ globalComplex R G X c :=
  Functor.mapHomologicalComplexCompIso (ProperCompactSections.globalIso f hf) c

/-- The proper compact-section transformation is a natural chain map. -/
def properComplex (hp : IsProperMap f) :
    directImageComplex c f hf ⋙ compactComplex R G Y c ⟶ compactComplex R G X c :=
  NatTrans.mapHomologicalComplex (ProperCompactSections.natTrans f hf hp) c

/-- The map in each degree is precisely the proper compact-section map. -/
@[simp]
theorem properComplex_f (hp : IsProperMap f)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) (i : I) :
    ((properComplex c f hf hp).app F).f i =
      (ProperCompactSections.natTrans f hf hp).app (F.X i) := rfl

/-- Spatial compact pullback commutes with forgetting support as a chain map. -/
theorem inclusion_triangle (hp : IsProperMap f)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) :
    (properComplex c f hf hp).app F ≫ (inclusionComplex R G X c).app F =
      (inclusionComplex R G Y c).app ((directImageComplex c f hf).obj F) ≫
        (globalComplexIso c f hf).hom.app F := by
  ext i s
  rfl

@[simp]
theorem properComplex_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) :
    (properComplex c (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id).app F =
      𝟙 ((compactComplex R G X c).obj F) := by
  ext i s
  rfl

/-- The actual chain maps compose along proper spatial maps. -/
theorem properComplex_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) :
    (properComplex c (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp)).app F =
      (properComplex c g hg hq).app ((directImageComplex c f hf).obj F) ≫
        (properComplex c f hf hp).app F := by
  ext i s
  rfl

/-- The natural proper chain map induces an actual map on homology. -/
def properHomology (hp : IsProperMap f) (i : I) :
    directImageComplex c f hf ⋙ compactHomology R G Y c i ⟶
      compactHomology R G X c i :=
  Functor.whiskerRight (properComplex c f hf hp)
    (homologyFunctor (Rep.{w} R G) c i)

/-- The global-section identification also identifies the homology actions. -/
def globalHomologyIso (i : I) :
    directImageComplex c f hf ⋙ globalHomology R G Y c i ≅
      globalHomology R G X c i :=
  Functor.isoWhiskerRight (globalComplexIso c f hf) (homologyFunctor (Rep.{w} R G) c i)

theorem inclusionHomology_triangle (hp : IsProperMap f)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) (i : I) :
    (properHomology c f hf hp i).app F ≫ (inclusionHomology R G X c i).app F =
      (inclusionHomology R G Y c i).app ((directImageComplex c f hf).obj F) ≫
        (globalHomologyIso c f hf i).hom.app F := by
  simpa only [properHomology, inclusionHomology, globalHomologyIso,
    globalHomology, compactHomology, Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom, Functor.comp_map, Functor.comp_obj, Functor.map_comp] using congrArg
    (fun k => (homologyFunctor (Rep.{w} R G) c i).map k)
    (inclusion_triangle c f hf hp F)

@[simp]
theorem properHomology_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) (i : I) :
    (properHomology c (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id i).app F =
      𝟙 ((compactHomology R G X c i).obj F) := by
  change (homologyFunctor (Rep.{w} R G) c i).map _ = _
  rw [properComplex_id]
  exact (homologyFunctor (Rep.{w} R G) c i).map_id _

theorem properHomology_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) (i : I) :
    (properHomology c (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) i).app F =
      (properHomology c g hg hq i).app ((directImageComplex c f hf).obj F) ≫
        (properHomology c f hf hp i).app F := by
  change (homologyFunctor (Rep.{w} R G) c i).map _ = _
  rw [properComplex_comp c f hf g hg hp hq F]
  exact (homologyFunctor (Rep.{w} R G) c i).map_comp _ _

variable {c}
  {K : HomologicalComplex (TopologicalSheaf G Y (ModuleCat.{w} R)) c}
  {F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c}

/-- Any genuine chain map into direct image induces compact spatial pullback. -/
def pullbackComplex (hp : IsProperMap f)
    (b : K ⟶ (directImageComplex c f hf).obj F) :
    (compactComplex R G Y c).obj K ⟶ (compactComplex R G X c).obj F :=
  (compactComplex R G Y c).map b ≫ (properComplex c f hf hp).app F

/-- Pullback uses the supplied chain map on the original section in every degree. -/
@[simp]
theorem pullbackComplex_apply (hp : IsProperMap f)
    (b : K ⟶ (directImageComplex c f hf).obj F) (i : I)
    (s : Langlands.Sheaf.LocalSupport.submodule
      (LocalCompactSections.ordinary (K.X i).obj)) :
    (((pullbackComplex f hf hp b).f i).hom s).val =
      ((b.f i).hom.app (Opposite.op ActionOpens.top)).hom s.val := rfl

/-- Each component agrees with the previously constructed full sheaf pullback. -/
theorem pullbackComplex_f (hp : IsProperMap f)
    (b : K ⟶ (directImageComplex c f hf).obj F) (i : I) :
    (pullbackComplex f hf hp b).f i = ProperCompactSections.pullback f hf hp (b.f i) :=
  rfl

/-- The original chain map and the global-section identification give the same map. -/
theorem pullbackComplex_inclusion_triangle (hp : IsProperMap f)
    (b : K ⟶ (directImageComplex c f hf).obj F) :
    pullbackComplex f hf hp b ≫ (inclusionComplex R G X c).app F =
      (inclusionComplex R G Y c).app K ≫
        (globalComplex R G Y c).map b ≫ (globalComplexIso c f hf).hom.app F := by
  ext i s
  rfl

@[simp]
theorem pullbackComplex_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) :
    pullbackComplex (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id (𝟙 F) =
      𝟙 ((compactComplex R G X c).obj F) := by
  ext i s
  rfl

theorem pullbackComplex_precomp (hp : IsProperMap f)
    {K' : HomologicalComplex (TopologicalSheaf G Y (ModuleCat.{w} R)) c}
    (a : K' ⟶ K) (b : K ⟶ (directImageComplex c f hf).obj F) :
    pullbackComplex f hf hp (a ≫ b) =
      (compactComplex R G Y c).map a ≫ pullbackComplex f hf hp b := by
  ext i s
  rfl

theorem pullbackComplex_postcomp (hp : IsProperMap f)
    {F' : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c}
    (a : F ⟶ F') (b : K ⟶ (directImageComplex c f hf).obj F) :
    pullbackComplex f hf hp (b ≫ (directImageComplex c f hf).map a) =
      pullbackComplex f hf hp b ≫ (compactComplex R G X c).map a := by
  ext i s
  rfl

theorem pullbackComplex_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    {L : HomologicalComplex (TopologicalSheaf G Z (ModuleCat.{w} R)) c}
    (b : K ⟶ (directImageComplex c f hf).obj F)
    (a : L ⟶ (directImageComplex c g hg).obj K) :
    pullbackComplex (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) (a ≫ (directImageComplex c g hg).map b) =
      pullbackComplex g hg hq a ≫ pullbackComplex f hf hp b := by
  ext i s
  rfl

/-- Homology of the constructed compact pullback, with its original group action. -/
def pullbackHomology (hp : IsProperMap f)
    (b : K ⟶ (directImageComplex c f hf).obj F) (i : I) :
    (compactHomology R G Y c i).obj K ⟶ (compactHomology R G X c i).obj F :=
  (homologyFunctor (Rep.{w} R G) c i).map (pullbackComplex f hf hp b)

/-- The homology map factors through homology of the actual direct-image complex. -/
theorem pullbackHomology_factor (hp : IsProperMap f)
    (b : K ⟶ (directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp b i =
      (compactHomology R G Y c i).map b ≫ (properHomology c f hf hp i).app F :=
  (homologyFunctor (Rep.{w} R G) c i).map_comp _ _

theorem pullbackHomology_inclusion_triangle (hp : IsProperMap f)
    (b : K ⟶ (directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp b i ≫ (inclusionHomology R G X c i).app F =
      (inclusionHomology R G Y c i).app K ≫
        (globalHomology R G Y c i).map b ≫
          (globalHomologyIso c f hf i).hom.app F := by
  simpa only [properHomology, inclusionHomology, globalHomologyIso,
    pullbackHomology, globalHomology, compactHomology, Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom, Functor.comp_map, Functor.comp_obj, Functor.map_comp] using congrArg
    (fun k => (homologyFunctor (Rep.{w} R G) c i).map k)
    (pullbackComplex_inclusion_triangle f hf hp b)

@[simp]
theorem pullbackHomology_id
    (F : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c) (i : I) :
    pullbackHomology (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id (𝟙 F) i =
      𝟙 ((compactHomology R G X c i).obj F) := by
  unfold pullbackHomology
  rw [pullbackComplex_id]
  exact (homologyFunctor (Rep.{w} R G) c i).map_id _

theorem pullbackHomology_precomp (hp : IsProperMap f)
    {K' : HomologicalComplex (TopologicalSheaf G Y (ModuleCat.{w} R)) c}
    (a : K' ⟶ K) (b : K ⟶ (directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp (a ≫ b) i =
      (compactHomology R G Y c i).map a ≫ pullbackHomology f hf hp b i := by
  simp only [pullbackHomology, pullbackComplex_precomp, Functor.map_comp]
  rfl

theorem pullbackHomology_postcomp (hp : IsProperMap f)
    {F' : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{w} R)) c}
    (a : F ⟶ F') (b : K ⟶ (directImageComplex c f hf).obj F) (i : I) :
    pullbackHomology f hf hp (b ≫ (directImageComplex c f hf).map a) i =
      pullbackHomology f hf hp b i ≫ (compactHomology R G X c i).map a := by
  simp only [pullbackHomology, pullbackComplex_postcomp, Functor.map_comp]
  rfl

theorem pullbackHomology_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    {L : HomologicalComplex (TopologicalSheaf G Z (ModuleCat.{w} R)) c}
    (b : K ⟶ (directImageComplex c f hf).obj F)
    (a : L ⟶ (directImageComplex c g hg).obj K) (i : I) :
    pullbackHomology (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) (a ≫ (directImageComplex c g hg).map b) i =
      pullbackHomology g hg hq a i ≫ pullbackHomology f hf hp b i := by
  simpa only [properHomology, inclusionHomology, globalHomologyIso,
    pullbackHomology, globalHomology, compactHomology, Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom, Functor.comp_map, Functor.comp_obj, Functor.map_comp] using congrArg
    (fun k => (homologyFunctor (Rep.{w} R G) c i).map k)
    (pullbackComplex_comp f hf g hg hp hq b a)

end Langlands.Cohomology.ProperCompactComplexes
