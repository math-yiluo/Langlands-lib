import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorUnit
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityStatements

/-! # Canonical tensor comparison for rigidified pullback -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

lemma tensorMap_id (M N : X.Modules) :
    tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensorObj M N) :=
  (tensorFunctor X).map_id (M, N)

/-- Equality transport of the morphism commutes with the fixed tensor comparison. -/
lemma pullbackCongr_tensor {f g : X ⟶ Y} (h : f = g) (M N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app (tensorObj M N) ≫
        pullbackTensorComparisonApp g M N =
      pullbackTensorComparisonApp f M N ≫
        tensorMap ((Scheme.Modules.pullbackCongr h).hom.app M)
          ((Scheme.Modules.pullbackCongr h).hom.app N) := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, tensorMap_id, Category.comp_id]

/-- The canonical pullback-unit map respects multiplication of the structure sheaf. -/
lemma pullbackUnit_tensor (coherence : PullbackTensorLeftUnitorStatement.{u})
    (f : X ⟶ Y) :
    pullbackTensorComparisonApp f (structureSheaf Y) (structureSheaf Y) ≫
        tensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom ≫
        (tensorLeftUnitor (structureSheaf X)).hom =
      (Scheme.Modules.pullback f).map (tensorLeftUnitor (structureSheaf Y)).hom ≫
        (pullbackUnitIso f).hom := by
  have ht := tensorMap_comp (pullbackUnitIso f).hom (𝟙 (structureSheaf X))
    (𝟙 ((Scheme.Modules.pullback f).obj (structureSheaf Y))) (pullbackUnitIso f).hom
  erw [Category.comp_id] at ht
  erw [← ht, Category.assoc (tensorMap (pullbackUnitIso f).hom
    (𝟙 ((Scheme.Modules.pullback f).obj (structureSheaf Y)))),
    tensorLeftUnitor_naturality (pullbackUnitIso f).hom,
    ← Category.assoc (pullbackTensorComparisonApp f (structureSheaf Y) (structureSheaf Y))]
  exact congrArg (· ≫ (pullbackUnitIso f).hom) (coherence X Y f (structureSheaf Y))

/-- The inverse unit identification commutes with the diagonal into the tensor unit. -/
lemma pullbackUnit_tensor_inv (coherence : PullbackTensorLeftUnitorStatement.{u})
    (f : X ⟶ Y) :
    (pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (tensorLeftUnitor (structureSheaf Y)).inv ≫
        pullbackTensorComparisonApp f (structureSheaf Y) (structureSheaf Y) =
      (tensorLeftUnitor (structureSheaf X)).inv ≫
        tensorMap (pullbackUnitIso f).inv (pullbackUnitIso f).inv := by
  apply (cancel_mono (((tensorFunctor X).mapIso
    ((pullbackUnitIso f).prod (pullbackUnitIso f))) ≪≫
      tensorLeftUnitor (structureSheaf X)).hom).1
  change ((pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (tensorLeftUnitor (structureSheaf Y)).inv ≫
      pullbackTensorComparisonApp f (structureSheaf Y) (structureSheaf Y)) ≫
        (tensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom ≫
          (tensorLeftUnitor (structureSheaf X)).hom) =
    ((tensorLeftUnitor (structureSheaf X)).inv ≫
      tensorMap (pullbackUnitIso f).inv (pullbackUnitIso f).inv) ≫
        (tensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom ≫
          (tensorLeftUnitor (structureSheaf X)).hom)
  erw [Category.assoc (pullbackUnitIso f).inv,
    Category.assoc ((Scheme.Modules.pullback f).map
      (tensorLeftUnitor (structureSheaf Y)).inv), pullbackUnit_tensor coherence f,
    ← Category.assoc ((Scheme.Modules.pullback f).map
      (tensorLeftUnitor (structureSheaf Y)).inv), ← Functor.map_comp,
    Iso.inv_hom_id, (Scheme.Modules.pullback f).map_id, Category.id_comp, Iso.inv_hom_id]
  erw [Category.assoc (tensorLeftUnitor (structureSheaf X)).inv,
    ← Category.assoc (tensorMap (pullbackUnitIso f).inv (pullbackUnitIso f).inv),
    tensorMap_comp (pullbackUnitIso f).inv (pullbackUnitIso f).hom
      (pullbackUnitIso f).inv (pullbackUnitIso f).hom,
    Iso.inv_hom_id, tensorMap_id, Category.id_comp, Iso.inv_hom_id]
  rfl

/-- The inverse composite-pullback comparison also respects tensor comparison. -/
lemma pullbackComp_inv_tensor (composition : PullbackTensorCompositionStatement.{u})
    {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app (tensorObj M N) ≫
        (Scheme.Modules.pullback f).map (pullbackTensorComparisonApp g M N) ≫
        pullbackTensorComparisonApp f ((Scheme.Modules.pullback g).obj M)
          ((Scheme.Modules.pullback g).obj N) =
      pullbackTensorComparisonApp (f ≫ g) M N ≫
        tensorMap ((Scheme.Modules.pullbackComp f g).inv.app M)
          ((Scheme.Modules.pullbackComp f g).inv.app N) := by
  apply (cancel_mono ((tensorFunctor X).mapIso
    (((Scheme.Modules.pullbackComp f g).app M).prod
      ((Scheme.Modules.pullbackComp f g).app N))).hom).1
  change (_ ≫ _ ≫ _) ≫
      tensorMap ((Scheme.Modules.pullbackComp f g).hom.app M)
        ((Scheme.Modules.pullbackComp f g).hom.app N) =
    (_ ≫ tensorMap ((Scheme.Modules.pullbackComp f g).inv.app M)
      ((Scheme.Modules.pullbackComp f g).inv.app N)) ≫
      tensorMap ((Scheme.Modules.pullbackComp f g).hom.app M)
        ((Scheme.Modules.pullbackComp f g).hom.app N)
  erw [Category.assoc ((Scheme.Modules.pullbackComp f g).inv.app (tensorObj M N)),
    Category.assoc ((Scheme.Modules.pullback f).map (pullbackTensorComparisonApp g M N)),
    ← composition X Y Z f g M N,
    ← Category.assoc ((Scheme.Modules.pullbackComp f g).inv.app (tensorObj M N)),
    Iso.inv_hom_id_app, Category.id_comp,
    Category.assoc (pullbackTensorComparisonApp (f ≫ g) M N),
    tensorMap_comp ((Scheme.Modules.pullbackComp f g).inv.app M)
      ((Scheme.Modules.pullbackComp f g).hom.app M)
      ((Scheme.Modules.pullbackComp f g).inv.app N)
      ((Scheme.Modules.pullbackComp f g).hom.app N),
    Iso.inv_hom_id_app, Iso.inv_hom_id_app, tensorMap_id, Category.comp_id]

end Langlands.Scheme.Modules

namespace Langlands.SchemeModule.RigidifiedModule

open Langlands.Scheme.Modules

variable {S X S' X' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'}

/-- The comparison for a commuting square respects the fixed tensor comparisons. -/
lemma squarePullbackIso_tensor (composition : PullbackTensorCompositionStatement.{u})
    (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) (M N : X.Modules) :
    (squarePullbackIso f g comm).hom.app (Langlands.Scheme.Modules.tensorObj M N) ≫
        (Scheme.Modules.pullback ε').map (pullbackTensorComparisonApp f M N) ≫
        pullbackTensorComparisonApp ε' ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) =
      (Scheme.Modules.pullback g).map (pullbackTensorComparisonApp ε M N) ≫
        pullbackTensorComparisonApp g ((Scheme.Modules.pullback ε).obj M)
          ((Scheme.Modules.pullback ε).obj N) ≫
        Langlands.Scheme.Modules.tensorMap ((squarePullbackIso f g comm).hom.app M)
          ((squarePullbackIso f g comm).hom.app N) := by
  change (((Scheme.Modules.pullbackComp g ε).hom.app (Langlands.Scheme.Modules.tensorObj M N) ≫
      (Scheme.Modules.pullbackCongr comm.symm).hom.app (Langlands.Scheme.Modules.tensorObj M N)) ≫
      (Scheme.Modules.pullbackComp ε' f).inv.app (Langlands.Scheme.Modules.tensorObj M N)) ≫ _ = _
  rw [Category.assoc, Category.assoc,
    pullbackComp_inv_tensor composition ε' f M N,
    ← Category.assoc ((Scheme.Modules.pullbackCongr comm.symm).hom.app (Langlands.Scheme.Modules.tensorObj M N)),
    pullbackCongr_tensor comm.symm M N,
    Category.assoc (pullbackTensorComparisonApp (g ≫ ε) M N),
    ← Category.assoc ((Scheme.Modules.pullbackComp g ε).hom.app
      (Langlands.Scheme.Modules.tensorObj M N)), composition S' S X g ε M N,
    Category.assoc ((Scheme.Modules.pullback g).map (pullbackTensorComparisonApp ε M N)),
    Category.assoc (pullbackTensorComparisonApp g ((Scheme.Modules.pullback ε).obj M)
      ((Scheme.Modules.pullback ε).obj N)),
    ← Category.assoc (Langlands.Scheme.Modules.tensorMap
      ((Scheme.Modules.pullbackComp g ε).hom.app M)
      ((Scheme.Modules.pullbackComp g ε).hom.app N)),
    Langlands.Scheme.Modules.tensorMap_comp ((Scheme.Modules.pullbackComp g ε).hom.app M)
      ((Scheme.Modules.pullbackCongr comm.symm).hom.app M)
      ((Scheme.Modules.pullbackComp g ε).hom.app N)
      ((Scheme.Modules.pullbackCongr comm.symm).hom.app N),
    Langlands.Scheme.Modules.tensorMap_comp
      (((Scheme.Modules.pullbackComp g ε).hom.app M) ≫
        ((Scheme.Modules.pullbackCongr comm.symm).hom.app M))
      ((Scheme.Modules.pullbackComp ε' f).inv.app M)
      (((Scheme.Modules.pullbackComp g ε).hom.app N) ≫
        ((Scheme.Modules.pullbackCongr comm.symm).hom.app N))
      ((Scheme.Modules.pullbackComp ε' f).inv.app N)]
  rfl

/-- The fixed tensor comparison preserves rigidifications after pullback along a square. -/
lemma pullbackTensor_compatibility
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (coherence : PullbackTensorLeftUnitorStatement.{u})
    (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε)
    (M N : RigidifiedModule ε) :
    ((pullback f g comm).obj (tensorObj preservation M N)).rigidification.hom ≫
        (Scheme.Modules.pullback ε').map (pullbackTensorComparisonApp f M.carrier N.carrier) =
      (tensorObj preservation ((pullback f g comm).obj M)
        ((pullback f g comm).obj N)).rigidification.hom := by
  let := preservation ε'
  apply (cancel_mono ((asIso (pullbackTensorComparison ε')).app
    ((Scheme.Modules.pullback f).obj M.carrier,
      (Scheme.Modules.pullback f).obj N.carrier)).hom).1
  change (((pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map (tensorObj preservation M N).rigidification.hom ≫
      (squarePullbackIso f g comm).hom.app
        (Langlands.Scheme.Modules.tensorObj M.carrier N.carrier)) ≫
      (Scheme.Modules.pullback ε').map (pullbackTensorComparisonApp f M.carrier N.carrier)) ≫
      pullbackTensorComparisonApp ε' ((Scheme.Modules.pullback f).obj M.carrier)
        ((Scheme.Modules.pullback f).obj N.carrier) =
    (tensorObj preservation ((pullback f g comm).obj M)
      ((pullback f g comm).obj N)).rigidification.hom ≫
      pullbackTensorComparisonApp ε' ((Scheme.Modules.pullback f).obj M.carrier)
        ((Scheme.Modules.pullback f).obj N.carrier)
  erw [Category.assoc, Category.assoc (pullbackUnitIso g).inv,
    Category.assoc ((Scheme.Modules.pullback g).map
      (tensorObj preservation M N).rigidification.hom),
    squarePullbackIso_tensor composition f g comm M.carrier N.carrier,
    ← Category.assoc ((Scheme.Modules.pullback g).map
      (tensorObj preservation M N).rigidification.hom),
    ← Functor.map_comp, tensorObj_rigidification_comp preservation M N,
    (Scheme.Modules.pullback g).map_comp,
    Category.assoc ((Scheme.Modules.pullback g).map
      (tensorLeftUnitor (structureModule S)).inv),
    ← Category.assoc ((Scheme.Modules.pullback g).map
      (Langlands.Scheme.Modules.tensorMap M.rigidification.hom N.rigidification.hom)),
    pullbackTensorComparisonApp_naturality g M.rigidification.hom N.rigidification.hom,
    Category.assoc (pullbackTensorComparisonApp g (structureModule S) (structureModule S)),
    ← Category.assoc ((Scheme.Modules.pullback g).map
      (tensorLeftUnitor (structureModule S)).inv),
    ← Category.assoc (pullbackUnitIso g).inv,
    pullbackUnit_tensor_inv coherence g,
    tensorObj_rigidification_comp preservation ((pullback f g comm).obj M)
      ((pullback f g comm).obj N)]
  erw [Category.assoc (tensorLeftUnitor (structureSheaf S')).inv,
    ← Category.assoc (Langlands.Scheme.Modules.tensorMap
      (pullbackUnitIso g).inv (pullbackUnitIso g).inv),
    Langlands.Scheme.Modules.tensorMap_comp (pullbackUnitIso g).inv
      ((Scheme.Modules.pullback g).map M.rigidification.hom) (pullbackUnitIso g).inv
      ((Scheme.Modules.pullback g).map N.rigidification.hom),
    Langlands.Scheme.Modules.tensorMap_comp
      ((pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map M.rigidification.hom)
      ((squarePullbackIso f g comm).hom.app M.carrier)
      ((pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map N.rigidification.hom)
      ((squarePullbackIso f g comm).hom.app N.carrier),
    Category.assoc (pullbackUnitIso g).inv, Category.assoc (pullbackUnitIso g).inv]
  rfl

/-- The canonical tensor comparison, lifted to actual rigidified modules. -/
def pullbackTensorIso (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (coherence : PullbackTensorLeftUnitorStatement.{u})
    (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε)
    (M N : RigidifiedModule ε) :
    (pullback f g comm).obj (tensorObj preservation M N) ≅
      tensorObj preservation ((pullback f g comm).obj M) ((pullback f g comm).obj N) := by
  let := preservation f
  exact isoMk ((asIso (pullbackTensorComparison f)).app (M.carrier, N.carrier))
    (pullbackTensor_compatibility preservation composition coherence f g comm M N)

end Langlands.SchemeModule.RigidifiedModule

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (coherence : PullbackTensorLeftUnitorStatement.{u})
variable {S X S' X' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'}

/-- The fixed tensor comparison restricts to rigidified line bundles. -/
def pullbackTensorIso (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε)
    (L M : RigidifiedLineBundle ε) :
    (pullback f g comm).obj (tensor preservation L M) ≅
      tensor preservation ((pullback f g comm).obj L) ((pullback f g comm).obj M) :=
  ObjectProperty.isoMk _
    (RigidifiedModule.pullbackTensorIso preservation composition coherence f g comm L.obj M.obj)

variable (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

include composition coherence in
/-- Relative pullback preserves the tensor product of compatible isomorphism classes. -/
lemma classesPullback_tensor {T U : Over S} (h : T ⟶ U)
    (q r : Classes f ε section_eq U) :
    classesPullback f ε section_eq h (classesTensor preservation f ε section_eq U q r) =
      classesTensor preservation f ε section_eq T
        (classesPullback f ε section_eq h q) (classesPullback f ε section_eq h r) := by
  refine Quotient.inductionOn₂ q r (fun L M ↦ ?_)
  exact Quotient.sound ⟨pullbackTensorIso preservation composition coherence
    ((relativeSpace f).map h) h.left
    ((relativeSection f ε section_eq).naturality h).symm L M⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
