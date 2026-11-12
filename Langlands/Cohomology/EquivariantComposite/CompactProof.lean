import Langlands.Cohomology.EquivariantComposite.InjectiveAcyclic
import Langlands.Cohomology.EquivariantComposite.AcyclicHomology
import Langlands.Cohomology.DerivedPlusNaturality

/-! # The compact-group composite-functor identification -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant

namespace Langlands.Cohomology.EquivariantComposite

universe w w' u

variable (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- Deriving the actual trivial-source Hom identification. -/
def trivialHomDerivedIso (n : ℕ) :
    (SmoothHomComplex.homFunctor R G (trivialSmoothRep R G)).rightDerived n ≅
      (invariants R G).rightDerived n where
  hom := NatTrans.rightDerived (trivialHomIso R G).hom n
  inv := NatTrans.rightDerived (trivialHomIso R G).inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

/-- Compact sections of an injective smooth sheaf have no positive derived ordinary Hom
from the trivial representation, after forgetting the coefficient module structure. -/
theorem isZero_compactSections_higherHom_of_injective
    (I : SmoothTopologicalSheaf R G X) [Injective I] (q : ℕ) :
    IsZero (((preadditiveCoyoneda.obj (op (trivialSmoothRep R G))).rightDerived (q + 1)).obj
      ((smoothSheafCompactSections R G X).obj I)) := by
  let V := (smoothSheafCompactSections R G X).obj I
  have hlinear : IsZero
      (((SmoothHomComplex.homFunctor R G (trivialSmoothRep R G)).rightDerived (q + 1)).obj V) :=
    IsZero.of_iso (isZero_compactSections_higherInvariants_of_injective R G X I q)
      ((trivialHomDerivedIso R G (q + 1)).app V)
  exact IsZero.of_iso ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_isZero hlinear)
    (ExtRightDerived.linearRightDerivedIso R (trivialSmoothRep R G) V (q + 1)).symm

/-- Ordinary Hom out of the trivial representation is invariant compact sections. -/
def compactHomIso :
    SmoothSheafCohomology.invariantCompactSections R G X ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      smoothSheafCompactSections R G X ⋙ preadditiveCoyoneda.obj (op (trivialSmoothRep R G)) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (smoothSheafCompactSections R G X) (trivialHomIso R G).symm)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- The compact-section Hom identification on every complex. -/
def compactHomComplexIso {ι : Type*} (c : ComplexShape ι) :
    ((SmoothSheafCohomology.invariantCompactSections R G X ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex c) ≅
      (smoothSheafCompactSections R G X).mapHomologicalComplex c ⋙
        (preadditiveCoyoneda.obj (op (trivialSmoothRep R G))).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (compactHomIso R G X) c ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) c).symm

/-- Exact forgetting of coefficient modules commutes with classical derived functors. -/
def compactDerivedForgetIso (n : ℕ) :
    ((SmoothSheafCohomology.invariantCompactSections R G X ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerived n) ≅
      SmoothSheafCohomology.invariantCompactDerived R G X n ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  asIso (LeftExactHomology.derivedNatTrans (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (SmoothSheafCohomology.invariantCompactSections R G X) n)

variable [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X)]

/-- Classical derived functors with group coefficients, computed on an integer resolution. -/
def compactGroupResolutionIso
    (F : SmoothTopologicalSheaf R G X ⥤ AddCommGrpCat.{u}) [F.Additive]
    {A : SmoothTopologicalSheaf R G X} (I : InjectiveResolution A) (n : ℕ) :
    (F.rightDerived n).obj A ≅ ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology n := by
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  exact (DerivedPlus.homologyIso F I n).symm ≪≫ DerivedPlus.homologyResolutionIso F I n

omit [CompactSpace G] in
/-- The integer-resolution formula is natural for compatible maps of resolutions. -/
@[reassoc]
theorem compactGroupResolutionIso_naturality
    (F : SmoothTopologicalSheaf R G X ⥤ AddCommGrpCat.{u}) [F.Additive]
    {A B : SmoothTopologicalSheaf R G X} {f : A ⟶ B}
    (I : InjectiveResolution A) (J : InjectiveResolution B)
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (F.rightDerived n).map f ≫ (compactGroupResolutionIso R G X F J n).hom =
      (compactGroupResolutionIso R G X F I n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') n := by
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  dsimp only [compactGroupResolutionIso, Iso.trans_hom, Iso.symm_hom]
  apply (cancel_epi (DerivedPlus.homologyIso F I n).hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← DerivedPlus.homologyIso_hom_naturality_of_hom F φ n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact DerivedPlus.homologyResolutionIso_hom_naturality F φ n

/-- Invariant compact cohomology is Hom cohomology of the compact-section resolution. -/
def compactResolutionHomologyIso {A : SmoothTopologicalSheaf R G X}
    (I : InjectiveResolution A) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((SmoothSheafCohomology.invariantCompactDerived R G X n).obj A) ≅
      (((preadditiveCoyoneda.obj (op (trivialSmoothRep R G))).mapHomologicalComplex (.up ℤ)).obj
        (((smoothSheafCompactSections R G X).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology n :=
  ((compactDerivedForgetIso R G X n).app A).symm ≪≫
    compactGroupResolutionIso R G X _ I n ≪≫
    HomologicalComplex.homologyMapIso ((compactHomComplexIso R G X (.up ℤ)).app I.cochainComplex) n

omit [CompactSpace G] in
set_option maxHeartbeats 800000 in
/-- The preceding formula intertwines the actual cohomology and resolution maps. -/
theorem compactResolutionHomologyIso_naturality
    {A B : SmoothTopologicalSheaf R G X} {f : A ⟶ B}
    (I : InjectiveResolution A) (J : InjectiveResolution B)
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((SmoothSheafCohomology.invariantCompactDerived R G X n).map f) ≫
        (compactResolutionHomologyIso R G X J n).hom =
      (compactResolutionHomologyIso R G X I n).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op (trivialSmoothRep R G))).mapHomologicalComplex (.up ℤ)).map
            (((smoothSheafCompactSections R G X).mapHomologicalComplex (.up ℤ)).map φ.hom')) n := by
  dsimp only [compactResolutionHomologyIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom]
  simp only [Category.assoc, Iso.app_inv]
  have hforget := (compactDerivedForgetIso R G X n).inv.naturality f
  simp only [Functor.comp_map] at hforget
  rw [reassoc_of% hforget, compactGroupResolutionIso_naturality_assoc R G X _ I J φ n]
  have hhom := (HomologicalComplex.homologyMap_comp _ _ (n : ℤ)).symm.trans
    ((congrArg (fun a => HomologicalComplex.homologyMap a (n : ℤ))
      ((compactHomComplexIso R G X (.up ℤ)).hom.naturality φ.hom')).trans
        (HomologicalComplex.homologyMap_comp _ _ (n : ℤ)))
  exact congrArg (fun a => (compactDerivedForgetIso R G X n).inv.app A ≫
    (compactGroupResolutionIso R G X _ I n).hom ≫ a) hhom

/-- Compact sections of an integer-indexed sheaf injective resolution. -/
def compactSectionResolutionPlus {A : SmoothTopologicalSheaf R G X} (I : InjectiveResolution A) :
    CochainComplex.Plus (SmoothRep.{u,u,u} R G) :=
  (smoothSheafCompactSections R G X).mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus I)

omit [HasDerivedCategory (SmoothTopologicalSheaf R G X)] in
/-- Every term in that resolution image is Hom-acyclic. -/
theorem compactSectionResolutionPlus_acyclic {A : SmoothTopologicalSheaf R G X}
    (I : InjectiveResolution A) (i : ℤ) (q : ℕ) :
    IsZero (((preadditiveCoyoneda.obj (op (trivialSmoothRep R G))).rightDerived (q + 1)).obj
      ((compactSectionResolutionPlus R G X I).obj.X i)) :=
  isZero_compactSections_higherHom_of_injective R G X (I.cochainComplex.X i) q

variable [HasDerivedCategory.{w'} (SmoothRep.{u,u,u} R G)]

/-- The derived compact-section complex is represented by compact sections of any resolution. -/
def compactResolutionDerivedIso {A : SmoothTopologicalSheaf R G X} (I : InjectiveResolution A) :
    DerivedCategory.Plus.ι.obj ((SmoothSheafDerivedComplex.compactComplex R G X).obj A) ≅
      DerivedCategory.Q.obj (compactSectionResolutionPlus R G X I).obj :=
  DerivedCategory.Plus.ι.mapIso (DerivedPlus.derivedComplexIso (smoothSheafCompactSections R G X) I) ≪≫
    (DerivedCategory.Plus.QCompιIso _).app (compactSectionResolutionPlus R G X I)

omit [CompactSpace G] in
/-- The derived compact-resolution representation is natural. -/
theorem compactResolutionDerivedIso_naturality
    {A B : SmoothTopologicalSheaf R G X} {f : A ⟶ B}
    (I : InjectiveResolution A) (J : InjectiveResolution B)
    (φ : InjectiveResolution.Hom I J f) :
    DerivedCategory.Plus.ι.map ((SmoothSheafDerivedComplex.compactComplex R G X).map f) ≫
        (compactResolutionDerivedIso R G X J).hom =
      (compactResolutionDerivedIso R G X I).hom ≫ DerivedCategory.Q.map
        (((smoothSheafCompactSections R G X).mapHomologicalComplex (.up ℤ)).map φ.hom') := by
  have h₁ := congrArg (DerivedCategory.Plus.ι.map)
    (DerivedPlus.derivedComplexIso_hom_naturality (smoothSheafCompactSections R G X) φ)
  simp only [Functor.map_comp] at h₁
  have h₂ := (DerivedCategory.Plus.QCompιIso (SmoothRep.{u,u,u} R G)).hom.naturality
    ((smoothSheafCompactSections R G X).mapCochainComplexPlus.map (DerivedPlus.resolutionPlusMap φ))
  dsimp only [compactResolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  dsimp only [SmoothSheafDerivedComplex.compactComplex, compactSectionResolutionPlus]
  rw [reassoc_of% h₁]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) h₂

/-- The additive compact composite comparison. -/
def compactCompositeAddEquiv (A : SmoothTopologicalSheaf R G X) (n : ℕ) :
    (SmoothSheafCohomology.invariantCompactDerived R G X n).obj A ≃+
      ShiftedHom ((DerivedCategory.singleFunctor (SmoothRep.{u,u,u} R G) 0).obj
        (trivialSmoothRep R G))
        (DerivedCategory.Plus.ι.obj ((SmoothSheafDerivedComplex.compactComplex R G X).obj A)) (n : ℤ) :=
  (compactResolutionHomologyIso R G X (injectiveResolution A) n).addCommGroupIsoToAddEquiv.trans
    ((acyclicHomologyDerivedAddEquiv (trivialSmoothRep R G)
      (compactSectionResolutionPlus R G X (injectiveResolution A))
      (compactSectionResolutionPlus_acyclic R G X (injectiveResolution A)) (n : ℤ)).trans
      { toEquiv := ((CategoryTheory.shiftFunctor _ (n : ℤ)).mapIso
          (compactResolutionDerivedIso R G X (injectiveResolution A)).symm).homToEquiv
        map_add' _ _ := CategoryTheory.Preadditive.add_comp _ _ _ _ _ _ })

set_option maxHeartbeats 800000 in
/-- The additive compact composite comparison is natural in the smooth sheaf. -/
theorem compactCompositeAddEquiv_naturality
    {A B : SmoothTopologicalSheaf R G X} (f : A ⟶ B) (n : ℕ)
    (x : (SmoothSheafCohomology.invariantCompactDerived R G X n).obj A) :
    compactCompositeAddEquiv R G X B n
        ((SmoothSheafCohomology.invariantCompactDerived R G X n).map f x) =
      compactCompositeAddEquiv R G X A n x ≫
        (DerivedCategory.Plus.ι.map
          ((SmoothSheafDerivedComplex.compactComplex R G X).map f))⟦(n : ℤ)⟧' := by
  let I := injectiveResolution A
  let J := injectiveResolution B
  let φ := DerivedPlus.descHom f I J
  let g : (compactSectionResolutionPlus R G X I).obj ⟶
      (compactSectionResolutionPlus R G X J).obj :=
    ((smoothSheafCompactSections R G X).mapCochainComplexPlus.map (DerivedPlus.resolutionPlusMap φ)).hom
  let eI := compactResolutionDerivedIso R G X I
  let eJ := compactResolutionDerivedIso R G X J
  let d := DerivedCategory.Plus.ι.map ((SmoothSheafDerivedComplex.compactComplex R G X).map f)
  have hres := ConcreteCategory.congr_hom
    (compactResolutionHomologyIso_naturality R G X I J φ n) x
  change (compactResolutionHomologyIso R G X J n).hom
      ((SmoothSheafCohomology.invariantCompactDerived R G X n).map f x) =
    HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op (trivialSmoothRep R G))).mapHomologicalComplex (.up ℤ)).map g)
      (n : ℤ) ((compactResolutionHomologyIso R G X I n).hom x) at hres
  have hhom := homologyDerivedMap_naturality (trivialSmoothRep R G) g (n : ℤ)
    ((compactResolutionHomologyIso R G X I n).hom x)
  have he : d ≫ eJ.hom = eI.hom ≫ DerivedCategory.Q.map g :=
    compactResolutionDerivedIso_naturality R G X I J φ
  have hinv : DerivedCategory.Q.map g ≫ eJ.inv = eI.inv ≫ d := by
    calc
      DerivedCategory.Q.map g ≫ eJ.inv = eI.inv ≫ (eI.hom ≫ DerivedCategory.Q.map g) ≫ eJ.inv := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = eI.inv ≫ (d ≫ eJ.hom) ≫ eJ.inv := by rw [← he]
      _ = eI.inv ≫ d := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change homologyDerivedMap (trivialSmoothRep R G) _ (n : ℤ)
      ((compactResolutionHomologyIso R G X J n).hom
        ((SmoothSheafCohomology.invariantCompactDerived R G X n).map f x)) ≫ eJ.inv⟦(n : ℤ)⟧' =
    (homologyDerivedMap (trivialSmoothRep R G) _ (n : ℤ)
      ((compactResolutionHomologyIso R G X I n).hom x) ≫ eI.inv⟦(n : ℤ)⟧') ≫ d⟦(n : ℤ)⟧'
  erw [hres, hhom]
  rw [Category.assoc, ← Functor.map_comp, hinv, Functor.map_comp, Category.assoc]
  rfl

/-- Berkovich's compact-group composite-functor identification, at the published independent universes. -/
theorem compactGroupCompactCompositeStatement_proof :
    CompactGroupCompactCompositeStatement.{w,w',u} := by
  intro R G X _ _ _ _ _ _ _ _ _ _ _ n
  exact ⟨fun A => compactCompositeAddEquiv R G X A n,
    fun f x => compactCompositeAddEquiv_naturality R G X f n x⟩

end Langlands.Cohomology.EquivariantComposite
