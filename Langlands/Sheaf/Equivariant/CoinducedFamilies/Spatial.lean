import Langlands.Sheaf.Equivariant.CoinducedFamilies.Functoriality
import Langlands.Sheaf.Equivariant.Godement.SpatialZero

/-! # Spatial maps on coinduced stalk families -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.CoinducedFamilies.Spatial

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Pull each indexed family entry back by the actual spatial stalk map. -/
def familySpatialMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    familyFunctor.obj ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ⟶
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj (familyFunctor.obj F) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun s g x := Godement.Spatial.stalkMap f hf F.obj x.1
            (s g ⟨f x.1, by
              rw [← hf]
              exact x.2⟩)
          map_add' s t := by funext g x; exact map_add _ _ _
          map_smul' r s := by funext g x; exact map_smul _ _ _ }
      naturality _U _V _k := rfl }

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
@[simp]
theorem familySpatialMap_apply (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (U : ActionOpens G Y)
    (s : Sections ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) U)
    (g : G) (x : {x : X // g • x ∈ ((DirectImage.preimage f hf).obj U).openSet}) :
    (familySpatialMap f hf F).hom.app (op U) s g x =
      Godement.Spatial.stalkMap f hf F.obj x.1
        (s g ⟨f x.1, by rw [← hf]; exact x.2⟩) := rfl

/-- Spatial pullback of indexed families is natural in the original sheaf. -/
def familySpatialNatTrans :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ familyFunctor ⟶
      familyFunctor ⋙ DirectImage.sheaf f hf (ModuleCat.{u} R) where
  app F := familySpatialMap f hf F
  naturality F F' a := by
    apply ObjectProperty.hom_ext
    ext U s
    funext g x
    exact congrArg (fun b => b (s g ⟨f x.1, by rw [← hf]; exact x.2⟩))
      (Godement.Spatial.stalkMap_naturality f hf a.hom x.1)

omit [ContinuousConstSMul G X] in
@[simp]
theorem familySpatialMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    familySpatialMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      𝟙 (familyFunctor.obj F) := by
  apply ObjectProperty.hom_ext
  ext U s
  funext g x
  change Godement.Spatial.stalkMap (ContinuousMap.id X)
    (fun (_ : G) (_ : X) => rfl) F.obj x.1 (s g ⟨x.1, x.2⟩) = s g x
  rw [Godement.Spatial.stalkMap_id]
  rfl

omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z] in
/-- Indexed spatial maps retain the actual composite of continuous maps. -/
theorem familySpatialMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    familySpatialMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      familySpatialMap g hg ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (DirectImage.sheaf g hg (ModuleCat.{u} R)).map (familySpatialMap f hf F) := by
  apply ObjectProperty.hom_ext
  ext U s
  funext k x
  exact congrArg (fun b => b (s k ⟨g (f x.1), by rw [← hg, ← hf]; exact x.2⟩))
    (Godement.Spatial.stalkMap_comp f hf g hg F.obj x.1)

/-- The spatial comparison for the actual right Kan coinduction, transported
through its natural family coordinates. -/
def coinducedSpatialNatTrans :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ coinducedZeroFunctor ⟶
      coinducedZeroFunctor ⋙ DirectImage.sheaf f hf (ModuleCat.{u} R) :=
  Functor.whiskerLeft (DirectImage.sheaf f hf (ModuleCat.{u} R))
      coinducedZeroNatIso.hom ≫
    familySpatialNatTrans f hf ≫
    Functor.whiskerRight coinducedZeroNatIso.inv
      (DirectImage.sheaf f hf (ModuleCat.{u} R))

/-- The section map of actual coinduction, with no assumed spatial comparison. -/
abbrev coinducedSpatialMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :=
  (coinducedSpatialNatTrans f hf).app F

/-- Reading the resulting Kan section gives exactly the original spatial
stalk map in each group coordinate. -/
theorem read_coinducedSpatialMap (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (U : ActionOpens G Y)
    (s : (coinducedZero ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).obj.obj (op U))
    (g : G) (x : {x : X // g • x ∈ ((DirectImage.preimage f hf).obj U).openSet}) :
    read F ((DirectImage.preimage f hf).obj U)
        ((coinducedSpatialMap f hf F).hom.app (op U) s) g x =
      Godement.Spatial.stalkMap f hf F.obj x.1
        (read ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) U s
          g ⟨f x.1, by rw [← hf]; exact x.2⟩) := by
  change read F _ ((read F _).symm _) g x = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- In family coordinates, the actual coaugmentation is the original germ
followed by actual group transport on stalks. -/
theorem read_coinducedCoaugmentation_stalkPull
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) (U : ActionOpens G X)
    (s : F.obj.obj (op U)) (g : G) (x : {x : X // g • x ∈ U.openSet}) :
    read F U (((coinducedCoaugmentation (R := R)).app F).hom.app (op U) s) g x =
      Godement.stalkPull F.obj g x.1 (g • x.1) rfl
        (((underlyingPresheaf G X (ModuleCat.{u} R)).obj F.obj).germ
          U.openSet (g • x.1) x.2 s) := by
  rw [read_coinducedCoaugmentation]
  exact (congrArg (fun a => a s)
    (Godement.germ_stalkPull_arrow F.obj (coordinateArrow U g)
      x.1 (g • x.1) rfl x.2)).symm

/-- The natural coaugmentation into the explicit indexed stalk families. -/
def familyCoaugmentation :
    𝟭 (TopologicalSheaf G X (ModuleCat.{u} R)) ⟶ familyFunctor :=
  coinducedCoaugmentation ≫ coinducedZeroNatIso.hom

/-- Spatial pullback carries the actual coaugmented indexed family to that on
`X`, including its original labelled germ transport. -/
@[reassoc]
theorem coaugmentation_familySpatialMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (familyCoaugmentation (R := R)).app
        ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫ familySpatialMap f hf F =
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).map
        ((familyCoaugmentation (R := R)).app F) := by
  apply ObjectProperty.hom_ext
  ext U s
  funext g x
  change Godement.Spatial.stalkMap f hf F.obj x.1
    (read _ U.unop (((coinducedCoaugmentation (R := R)).app
      ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).hom.app U s)
        g ⟨f x.1, _⟩) =
    read F ((DirectImage.preimage f hf).obj U.unop)
      (((coinducedCoaugmentation (R := R)).app F).hom.app _ s) g x
  rw [read_coinducedCoaugmentation_stalkPull, read_coinducedCoaugmentation_stalkPull]
  have h := Godement.Spatial.stalkMap_transport_section f hf F.obj g x.1
    (g • x.1) rfl (g • f x.1) (hf g x.1).symm rfl U.unop.openSet
    (fun y => ((underlyingPresheaf G Y (ModuleCat.{u} R)).obj
      ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F.obj)).germ
        U.unop.openSet y.1 y.2 s) (by rw [← hf]; exact x.2) x.2
  exact h.trans (congrArg (Godement.stalkPull F.obj g x.1 (g • x.1) rfl)
    (congrArg (fun a => a s)
      (Godement.Spatial.germ_stalkMap f hf F.obj U.unop.openSet (g • x.1) x.2)))

/-- The actual coinduced spatial comparison respects the actual coinduction
coaugmentation. -/
@[reassoc]
theorem coaugmentation_coinducedSpatialMap
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (coinducedCoaugmentation (R := R)).app
        ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫ coinducedSpatialMap f hf F =
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).map
        ((coinducedCoaugmentation (R := R)).app F) := by
  apply (cancel_mono ((DirectImage.sheaf f hf (ModuleCat.{u} R)).map
    (coinducedZeroNatIso.hom.app F))).1
  simp only [coinducedSpatialMap, coinducedSpatialNatTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [familyCoaugmentation, familySpatialNatTrans, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
    using coaugmentation_familySpatialMap f hf F

@[simp]
theorem coinducedSpatialMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    coinducedSpatialMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      𝟙 (coinducedZero F) := by
  apply ObjectProperty.hom_ext
  ext U s
  apply (read F U.unop).injective
  funext g x
  have h := read_coinducedSpatialMap (ContinuousMap.id X)
    (fun (_ : G) (_ : X) => rfl) F U.unop s g x
  have hi := congrArg (fun a => a (read F U.unop s g x))
    (Godement.Spatial.stalkMap_id F.obj x.1)
  exact h.trans hi

/-- Composition holds for actual coinduced sections, with the two genuine
spatial stalk maps. -/
theorem coinducedSpatialMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    coinducedSpatialMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      coinducedSpatialMap g hg ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (DirectImage.sheaf g hg (ModuleCat.{u} R)).map (coinducedSpatialMap f hf F) := by
  apply ObjectProperty.hom_ext
  ext U s
  apply (read F ((DirectImage.preimage f hf).obj
    ((DirectImage.preimage g hg).obj U.unop))).injective
  funext k x
  change read F _ ((coinducedSpatialMap (g.comp f) _ F).hom.app U s) k x =
    read F _ ((coinducedSpatialMap f hf F).hom.app _
      ((coinducedSpatialMap g hg _).hom.app U s)) k x
  have h₁ := read_coinducedSpatialMap (g.comp f)
    (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F U.unop s k x
  have h₂ := read_coinducedSpatialMap f hf F ((DirectImage.preimage g hg).obj U.unop)
    ((coinducedSpatialMap g hg _).hom.app U s) k x
  have h₃ := read_coinducedSpatialMap g hg
    ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) U.unop s k
      ⟨f x.1, by rw [← hf]; exact x.2⟩
  have hc := congrArg (fun a => a (read
    ((DirectImage.sheaf (g.comp f)
      (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (ModuleCat.{u} R)).obj F) U.unop s k
          ⟨g (f x.1), by rw [← hg, ← hf]; exact x.2⟩))
    (Godement.Spatial.stalkMap_comp f hf g hg F.obj x.1)
  exact h₁.trans (hc.trans ((congrArg (Godement.Spatial.stalkMap f hf F.obj x.1) h₃).symm.trans
    h₂.symm))

end Langlands.Sheaf.Equivariant.CoinducedFamilies.Spatial
