import Langlands.Sheaf.Equivariant.CoinducedFamilies

/-! # Functorial coordinates for coinduced stalk families -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.CoinducedFamilies

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- Apply an original sheaf morphism to the stalk at every indexed point. -/
def familyMap {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (a : F ⟶ F') :
    sheaf (G := G) (Coefficients F) ⟶ sheaf (G := G) (Coefficients F') :=
  ObjectProperty.homMk
    { app _U := ModuleCat.ofHom
        { toFun s g y := (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) y.1).map
            ((underlyingPresheaf G X (ModuleCat.{u} R)).map a.hom) (s g y)
          map_add' s t := by funext g y; exact map_add _ _ _
          map_smul' r s := by funext g y; exact map_smul _ _ _ }
      naturality _U _V _k := rfl }

omit [ContinuousConstSMul G X] in
@[simp]
theorem familyMap_apply {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (a : F ⟶ F')
    (U : ActionOpens G X) (s : Sections F U) (g : G)
    (y : {y : X // g • y ∈ U.openSet}) :
    (familyMap a).hom.app (op U) s g y =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) y.1).map
        ((underlyingPresheaf G X (ModuleCat.{u} R)).map a.hom) (s g y) := rfl

/-- The actual equivariant sheaves of indexed stalk families form a functor. -/
def familyFunctor :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ TopologicalSheaf G X (ModuleCat.{u} R) where
  obj F := sheaf (G := G) (Coefficients F)
  map a := familyMap a
  map_id F := by
    apply ObjectProperty.hom_ext
    ext U s
    funext g y
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) y.1).map
      ((underlyingPresheaf G X (ModuleCat.{u} R)).map (𝟙 F.obj)) (s g y) = s g y
    simp
  map_comp a b := by
    apply ObjectProperty.hom_ext
    ext U s
    funext g y
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) y.1).map
      ((underlyingPresheaf G X (ModuleCat.{u} R)).map (a.hom ≫ b.hom)) (s g y) = _
    simp only [Functor.map_comp]
    rfl

/-- Coinduce the actual underlying sheaf of ordinary stalk families. -/
def coinducedZeroFunctor :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ TopologicalSheaf G X (ModuleCat.{u} R) :=
  Godement.zeroFunctor R G X ⋙ toSheaf G X (ModuleCat.{u} R) ⋙
    coinduction G X (ModuleCat.{u} R)

/-- Reading the actual Kan extension commutes with every original sheaf map. -/
theorem read_map_hom {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (a : F ⟶ F')
    (U : ActionOpens G X) (s : (coinducedZero F).obj.obj (op U)) (g : G)
    (y : {y : X // g • y ∈ U.openSet}) :
    read F' U (((coinducedZeroFunctor (R := R)).map a).hom.app (op U) s) g y =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) y.1).map
        ((underlyingPresheaf G X (ModuleCat.{u} R)).map a.hom) (read F U s g y) := by
  let b := (toSheaf G X (ModuleCat.{u} R)).map ((Godement.zeroFunctor R G X).map a)
  let k := coordinateArrow U g
  let W := coordinateOpen U g
  change read F' U (((coinduction G X (ModuleCat.{u} R)).map b).hom.app (op U) s)
    g y = _
  have h₁ := read_arrow F' U W k
    (((coinduction G X (ModuleCat.{u} R)).map b).hom.app (op U) s) ⟨y.1, y.2⟩
  have h₂ := read_arrow F U W k s ⟨y.1, y.2⟩
  have hn := ((coinduction G X (ModuleCat.{u} R)).map b).hom.naturality k.op
  have hc := NatTrans.congr_app
    ((ActionOpens.inclusion G X).op.ranCounit.naturality b.hom) (op W)
  have hn' := congrArg (fun t => t s) hn
  have hc' := congrArg (fun t => t ((coinducedZero F).obj.map k.op s)) hc
  have he := (congrArg
    (fun t => (((ActionOpens.inclusion G X).op.ranCounit.app
      (ordinaryZero F').obj).app (op W)) t) hn').symm.trans hc'
  exact h₁.trans ((congrFun he ⟨y.1, y.2⟩).trans
    (congrArg
      (fun t => (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) y.1).map
        ((underlyingPresheaf G X (ModuleCat.{u} R)).map a.hom) t) h₂.symm))

/-- The existing coordinate isomorphisms assemble naturally in the original sheaf. -/
def coinducedZeroNatIso :
    coinducedZeroFunctor (R := R) (G := G) (X := X) ≅ familyFunctor :=
  NatIso.ofComponents coinducedZeroIso (by
    intro F F' a
    apply ObjectProperty.hom_ext
    ext U s
    funext g y
    change read F' U.unop
      (((coinducedZeroFunctor (R := R)).map a).hom.app U s) g y = _
    exact read_map_hom a U.unop s g y)

/-- The concrete coinduction counit is the counit of the underlying right Kan
extension. -/
theorem coinduction_counit_hom
    (S : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X)) :
    ((coinductionAdjunction G X (ModuleCat.{u} R)).counit.app S).hom =
      (ActionOpens.inclusion G X).op.ranCounit.app S.obj := by
  simp only [coinductionAdjunction, Adjunction.ofNatIsoLeft,
    toSheafIsoPushforward, sheafEquivalence,
    Equivalence.toAdjunction]
  erw [Category.id_comp,
    Functor.sheafAdjunctionCocontinuous_counit_app_hom,
    Functor.ranAdjunction_counit]

/-- Coaugment into ordinary stalk families and then use the actual coinduction
unit. -/
def coinducedCoaugmentation :
    𝟭 (TopologicalSheaf G X (ModuleCat.{u} R)) ⟶
      coinducedZeroFunctor (R := R) :=
  Godement.coaugmentation R G X ≫
    Functor.whiskerLeft (Godement.zeroFunctor R G X)
      (coinductionAdjunction G X (ModuleCat.{u} R)).unit

/-- After forgetting equivariance and evaluating the Kan counit, the
coinduced coaugmentation is the original family of germs. -/
@[reassoc]
theorem coinducedCoaugmentation_counit
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (toSheaf G X (ModuleCat.{u} R)).map ((coinducedCoaugmentation (R := R)).app F) ≫
        (coinductionAdjunction G X (ModuleCat.{u} R)).counit.app (ordinaryZero F) =
      (toSheaf G X (ModuleCat.{u} R)).map ((Godement.coaugmentation R G X).app F) := by
  change (toSheaf G X (ModuleCat.{u} R)).map
    ((Godement.coaugmentation R G X).app F ≫
      (coinductionAdjunction G X (ModuleCat.{u} R)).unit.app
        ((Godement.zeroFunctor R G X).obj F)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  exact (congrArg
    ((toSheaf G X (ModuleCat.{u} R)).map
      ((Godement.coaugmentation R G X).app F) ≫ ·)
    ((coinductionAdjunction G X (ModuleCat.{u} R)).left_triangle_components
      ((Godement.zeroFunctor R G X).obj F))).trans (Category.comp_id _)

/-- The coordinate labelled by `g` of the coaugmentation is the germ at `y` of
the original section transported along the full `g`-labelled open. -/
theorem read_coinducedCoaugmentation
    (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (U : ActionOpens G X) (s : F.obj.obj (op U)) (g : G)
    (y : {y : X // g • y ∈ U.openSet}) :
    read F U (((coinducedCoaugmentation (R := R)).app F).hom.app (op U) s) g y =
      ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F.obj).germ
        (coordinateOpen U g) y.1 y.2
        (F.obj.map (coordinateArrow U g).op s) := by
  let k := coordinateArrow U g
  let W := coordinateOpen U g
  have h₁ := read_arrow F U W k
    (((coinducedCoaugmentation (R := R)).app F).hom.app (op U) s) ⟨y.1, y.2⟩
  have hn := congrArg (fun t => t s)
    (((coinducedCoaugmentation (R := R)).app F).hom.naturality k.op)
  have hc := congrArg
    (fun t => t.hom.app (op W) (F.obj.map k.op s))
    (coinducedCoaugmentation_counit F)
  change (((coinductionAdjunction G X (ModuleCat.{u} R)).counit.app
    (ordinaryZero F)).hom.app (op W))
      ((((coinducedCoaugmentation (R := R)).app F).hom.app
        (op ((ActionOpens.inclusion G X).obj W))) (F.obj.map k.op s)) = _ at hc
  rw [coinduction_counit_hom] at hc
  exact h₁.trans (congrFun
    ((congrArg
      (fun t => (((ActionOpens.inclusion G X).op.ranCounit.app
        (ordinaryZero F).obj).app (op W)) t) hn).symm.trans hc) ⟨y.1, y.2⟩)

end Langlands.Sheaf.Equivariant.CoinducedFamilies
