import Langlands.Sheaf.Equivariant.Exact
import Langlands.Sheaf.Equivariant.Godement.Complex
import Langlands.Sheaf.Equivariant.Godement.SkyscraperProduct
import Langlands.Cohomology.CokernelComplex.Map
import Langlands.Sheaf.Godement.TopologicalPoints

/-!
# The underlying complex of the equivariant Godement complex

After forgetting equivariance, the equivariant Godement complex of an
equivariant module sheaf is naturally isomorphic to the ordinary Godement
complex of its underlying sheaf, built from all points of the space, compatibly
with the two augmentations.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Godement

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

attribute [local instance] Classical.propDecidable

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

@[reassoc]
theorem skyscraperMap_read {M N : ModuleCat.{u} R} (g : M ⟶ N) (x : X) (U : Opens X)
    (hx : x ∈ U) :
    ((skyscraperSheafFunctor (X := TopCat.of X) x).map g).hom.app (op U) ≫
        skyscraperRead x N U hx =
      skyscraperRead x M U hx ≫ g := by
  simp [skyscraperSheafFunctor, skyscraperRead, hx]

/-- Evaluating stalk families commutes with the induced stalk maps. -/
@[reassoc]
theorem zeroMap_familyEvaluation {F F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (f : F ⟶ F') (U : Opens X) (x : X) (hx : x ∈ U) :
    (zeroMap f).hom.app (op ((ActionOpens.inclusion G X).obj U)) ≫
        familyEvaluation F' U x hx =
      familyEvaluation F U x hx ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
          ((underlyingPresheaf G X (ModuleCat.{u} R)).map f) := by
  ext s
  rfl

/-- The projections to the skyscrapers are natural in the equivariant sheaf. -/
theorem skyscraperProjection_naturality {F F' : TopologicalSheaf G X (ModuleCat.{u} R)}
    (f : F ⟶ F') (x : X) :
    (toSheaf G X (ModuleCat.{u} R)).map ((zeroFunctor R G X).map f) ≫
        skyscraperProjection F'.obj x =
      skyscraperProjection F.obj x ≫
        (skyscraperSheafFunctor (X := TopCat.of X) x).map
          ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
            ((underlyingPresheaf G X (ModuleCat.{u} R)).map f.hom)) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  by_cases hx : x ∈ U.unop
  · apply (cancel_mono (skyscraperRead x
      (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F'.obj).stalk x) U.unop hx)).1
    change (zeroMap f.hom).hom.app (op ((ActionOpens.inclusion G X).obj U.unop)) ≫
        skyscraperProjectionApp F'.obj x U.unop ≫ skyscraperRead x _ U.unop hx =
      skyscraperProjectionApp F.obj x U.unop ≫
        ((skyscraperSheafFunctor (X := TopCat.of X) x).map _).hom.app U ≫
          skyscraperRead x _ U.unop hx
    rw [skyscraperProjectionApp_read, zeroMap_familyEvaluation, skyscraperMap_read,
      skyscraperProjectionApp_read_assoc]
  · exact (isTerminalSkyscraperSheafObjObjOfNotMem
      (A := ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F'.obj).stalk x) hx).hom_ext _ _

/-- The coaugmentation followed by a projection is the ordinary stalk-skyscraper unit. -/
theorem coaugmentation_skyscraperProjection (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (x : X) :
    (toSheaf G X (ModuleCat.{u} R)).map ((coaugmentation R G X).app F) ≫
        skyscraperProjection F.obj x =
      (stalkSkyscraperSheafAdjunction (X := TopCat.of X) x).unit.app
        ((toSheaf G X (ModuleCat.{u} R)).obj F) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  by_cases hx : x ∈ U.unop
  · apply (cancel_mono (skyscraperRead x
      (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F.obj).stalk x) U.unop hx)).1
    change (germFamily F.obj).app (op ((ActionOpens.inclusion G X).obj U.unop)) ≫
        skyscraperProjectionApp F.obj x U.unop ≫ skyscraperRead x _ U.unop hx = _
    rw [skyscraperProjectionApp_read]
    simp [stalkSkyscraperSheafAdjunction, skyscraperRead, hx]
    ext s
    rfl
  · exact (isTerminalSkyscraperSheafObjObjOfNotMem
      (A := ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F.obj).stalk x) hx).hom_ext _ _

variable (R G X) in
/-- The ordinary stalk-skyscraper functors, indexed by the points of `X`. -/
abbrev topFactors (x : X) :
    TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X) ⥤ TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X) :=
  (TopCat.Sheaf.forget (ModuleCat.{u} R) (TopCat.of X) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x) ⋙ skyscraperSheafFunctor (X := TopCat.of X) x

/-- Maps into a value of the ordinary product functor are determined by their
components. -/
theorem topZeroFunctor_hom_ext {d : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X)}
    {Y : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X)}
    {a b : Y ⟶ (Sheaf.Godement.topZeroFunctor (ModuleCat.{u} R) (TopCat.of X)).obj d}
    (h : ∀ x : X, a ≫ (Pi.π (topFactors R X) x).app d = b ≫ (Pi.π (topFactors R X) x).app d) :
    a = b := by
  rw [← cancel_mono (piObjIso (topFactors R X) d).hom]
  refine Pi.hom_ext (f := fun x => (topFactors R X x).obj d) _ _ fun x => ?_
  rw [Category.assoc, Category.assoc, piObjIso_hom_comp_π]
  exact h x

variable (R G X) in
/-- The component at `F` of the degree-zero comparison. -/
def zeroIsoTopApp (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (toSheaf G X (ModuleCat.{u} R)).obj ((zeroFunctor R G X).obj F) ≅
      (Sheaf.Godement.topZeroFunctor (ModuleCat.{u} R) (TopCat.of X)).obj
        ((toSheaf G X (ModuleCat.{u} R)).obj F) :=
  skyscraperProductIso F.obj ≪≫
    (piObjIso (topFactors R X) ((toSheaf G X (ModuleCat.{u} R)).obj F)).symm

theorem zeroIsoTopApp_hom_π (F : TopologicalSheaf G X (ModuleCat.{u} R)) (x : X) :
    (zeroIsoTopApp R G X F).hom ≫
        (Pi.π (topFactors R X) x).app ((toSheaf G X (ModuleCat.{u} R)).obj F) =
      skyscraperProjection F.obj x := by
  exact (Category.assoc _ _ _).trans ((congrArg ((skyscraperProductIso F.obj).hom ≫ ·)
    (piObjIso_inv_comp_π (topFactors R X) ((toSheaf G X (ModuleCat.{u} R)).obj F) x)).trans
    (IsLimit.conePointUniqueUpToIso_hom_comp (skyscraperFanIsLimit F.obj)
      (limit.isLimit _) ⟨x⟩))

variable (R G X) in
/-- After forgetting equivariance, the degree-zero equivariant Godement functor is
the product of the ordinary stalk skyscrapers. -/
def zeroIsoTop :
    zeroFunctor R G X ⋙ toSheaf G X (ModuleCat.{u} R) ≅
      toSheaf G X (ModuleCat.{u} R) ⋙
        Sheaf.Godement.topZeroFunctor (ModuleCat.{u} R) (TopCat.of X) :=
  NatIso.ofComponents (zeroIsoTopApp R G X) (fun {F F'} f => by
    apply topZeroFunctor_hom_ext
    intro x
    have hn := (Pi.π (topFactors R X) x).naturality ((toSheaf G X (ModuleCat.{u} R)).map f)
    calc ((zeroFunctor R G X ⋙ toSheaf G X (ModuleCat.{u} R)).map f ≫
          (zeroIsoTopApp R G X F').hom) ≫ (Pi.π (topFactors R X) x).app _
        = (toSheaf G X (ModuleCat.{u} R)).map ((zeroFunctor R G X).map f) ≫
            skyscraperProjection F'.obj x := by
          rw [Category.assoc]
          exact congrArg _ (zeroIsoTopApp_hom_π F' x)
      _ = skyscraperProjection F.obj x ≫ (topFactors R X x).map
            ((toSheaf G X (ModuleCat.{u} R)).map f) := skyscraperProjection_naturality f x
      _ = ((zeroIsoTopApp R G X F).hom ≫ (Pi.π (topFactors R X) x).app _) ≫
            (topFactors R X x).map ((toSheaf G X (ModuleCat.{u} R)).map f) := by
          rw [zeroIsoTopApp_hom_π]
      _ = (zeroIsoTopApp R G X F).hom ≫
            ((toSheaf G X (ModuleCat.{u} R) ⋙
              Sheaf.Godement.topZeroFunctor (ModuleCat.{u} R) (TopCat.of X)).map f ≫
              (Pi.π (topFactors R X) x).app _) := by
          rw [Category.assoc]
          exact congrArg _ hn.symm
      _ = _ := (Category.assoc _ _ _).symm)

theorem zeroIso_comm_aux (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (toSheaf G X (ModuleCat.{u} R)).map ((coaugmentation R G X).app F) ≫
        (zeroIsoTop R G X).hom.app F =
      (Sheaf.Godement.topCoaugmentation (ModuleCat.{u} R) (TopCat.of X)).app
        ((toSheaf G X (ModuleCat.{u} R)).obj F) := by
  apply topZeroFunctor_hom_ext
  intro x
  calc ((toSheaf G X (ModuleCat.{u} R)).map ((coaugmentation R G X).app F) ≫
        (zeroIsoTop R G X).hom.app F) ≫ (Pi.π (topFactors R X) x).app _
      = (toSheaf G X (ModuleCat.{u} R)).map ((coaugmentation R G X).app F) ≫
          skyscraperProjection F.obj x := by
        rw [Category.assoc]
        exact congrArg _ (zeroIsoTopApp_hom_π F x)
    _ = (stalkSkyscraperSheafAdjunction (X := TopCat.of X) x).unit.app
          ((toSheaf G X (ModuleCat.{u} R)).obj F) := coaugmentation_skyscraperProjection F x
    _ = _ := (NatTrans.congr_app (Pi.lift_comp_π
          (fun x => (stalkSkyscraperSheafAdjunction (C := ModuleCat.{u} R)
            (X := TopCat.of X) x).unit) x) _).symm

variable (R G X) in
/-- After forgetting equivariance, the degree-zero equivariant Godement functor is
the published Godement degree-zero functor over all points of the space. -/
def zeroIso :
    zeroFunctor R G X ⋙ toSheaf G X (ModuleCat.{u} R) ≅
      toSheaf G X (ModuleCat.{u} R) ⋙
        Sheaf.Godement.zeroFunctor (Cohomology.Flasque.spacePoints (TopCat.of X))
          (ModuleCat.{u} R) :=
  zeroIsoTop R G X ≪≫ Functor.isoWhiskerLeft (toSheaf G X (ModuleCat.{u} R))
    (Sheaf.Godement.topZeroFunctorIso (ModuleCat.{u} R) (TopCat.of X))

/-- The degree-zero comparison carries the equivariant coaugmentation to the
ordinary Godement coaugmentation. -/
theorem zeroIso_comm (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (toSheaf G X (ModuleCat.{u} R)).map ((coaugmentation R G X).app F) ≫
        (zeroIso R G X).hom.app F =
      (Sheaf.Godement.coaugmentation (Cohomology.Flasque.spacePoints (TopCat.of X))
        (ModuleCat.{u} R)).app ((toSheaf G X (ModuleCat.{u} R)).obj F) := by
  have h := NatTrans.congr_app
    (Sheaf.Godement.topCoaugmentation_topZeroFunctorIso (ModuleCat.{u} R) (TopCat.of X))
    ((toSheaf G X (ModuleCat.{u} R)).obj F)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (zeroIso_comm_aux F)).trans h)

variable (R G X) in
/-- After forgetting equivariance, the equivariant Godement complex is naturally
isomorphic to the ordinary Godement complex over all points of the space. -/
def underlyingComplexIso :
    complexFunctor R G X ⋙
        (toSheaf G X (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      toSheaf G X (ModuleCat.{u} R) ⋙
        Sheaf.Godement.complexFunctor (Cohomology.Flasque.spacePoints (TopCat.of X))
          (ModuleCat.{u} R) :=
  Cohomology.CokernelComplex.functorIso (zeroIso R G X) zeroIso_comm

/-- The comparison is compatible with the two augmentations. -/
theorem underlyingComplexIso_augmentation (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (toSheaf G X (ModuleCat.{u} R)).map ((coaugmentation R G X).app F) ≫
        ((underlyingComplexIso R G X).hom.app F).f 0 =
      Sheaf.Godement.augmentation (Cohomology.Flasque.spacePoints (TopCat.of X))
        (ModuleCat.{u} R) ((toSheaf G X (ModuleCat.{u} R)).obj F) :=
  Cohomology.CokernelComplex.map_augmentation_functorIso (zeroIso R G X) zeroIso_comm F

end Langlands.Sheaf.Equivariant.Godement
