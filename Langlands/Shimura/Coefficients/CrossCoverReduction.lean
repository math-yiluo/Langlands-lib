import Langlands.Shimura.Coefficients.Reduction
import Langlands.Shimura.Coefficients.EtaleCrossCover

/-! # Cross-cover maps of associated coefficient reduction systems -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] (I : Ideal R) (X : Scheme.{u})
variable {G H : Type u} [Group G] [Group H]
variable {Y : Action X.Etale G} {Z : Action X.Etale H}

/-- With the cover fixed, cross-cover maps are the associated coefficient maps. -/
theorem etaleCrossCoverMap_sameCover (Y : Action X.Etale G)
    {M N : Action (ModuleCat.{u} R) G} (c : M ⟶ N) :
    etaleCrossCoverMap X (MonoidHom.id G) (𝟙 Y) c =
      (etaleAssociatedFunctor X Y).map c :=
  crossCoverMap_sameCover X.smallEtaleTopology Y
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).map c)

variable (φ : H →* G) (a : Z ⟶ (Action.res X.Etale φ).obj Y)
variable {M M' : Action (ModuleCat.{u} R) G}
variable {N N' : Action (ModuleCat.{u} R) H}

/-- A commuting coefficient square induces a commuting square of invariant sheaves. -/
theorem crossCoverMap_coefficient_square
    {F F' : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G}
    {E E' : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) H}
    (c : (Action.res _ φ).obj F ⟶ E)
    (c' : (Action.res _ φ).obj F' ⟶ E') (d : F ⟶ F') (e : E ⟶ E')
    (h : (Action.res _ φ).map d ≫ c' = c ≫ e) :
    (associatedFunctor X.smallEtaleTopology Y).map d ≫
        crossCoverMap X.smallEtaleTopology φ a c' =
      crossCoverMap X.smallEtaleTopology φ a c ≫
        (associatedFunctor X.smallEtaleTopology Z).map e := by
  apply hom_ext X.smallEtaleTopology Z
  simp only [Category.assoc, crossCoverMap_inclusion,
    crossCoverMap_inclusion_assoc, inclusion_natural, inclusion_natural_assoc]
  rw [← coverPullback_natural_assoc]
  simp only [← CategoryTheory.Functor.map_comp]
  have hh : d.hom ≫ c'.hom = c.hom ≫ e.hom := congrArg (fun k => k.hom) h
  exact congrArg (fun k => inclusion X.smallEtaleTopology Y F ≫
    coverPullback X.smallEtaleTopology a.hom F.V ≫
      (productSheaf X.smallEtaleTopology Z.V).map k) hh

/-- A commuting coefficient square induces a commuting square across covers. -/
theorem etaleCrossCoverMap_coefficient_square
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N)
    (c' : (Action.res (ModuleCat.{u} R) φ).obj M' ⟶ N')
    (d : M ⟶ M') (e : N ⟶ N')
    (h : (Action.res (ModuleCat.{u} R) φ).map d ≫ c' = c ≫ e) :
    (etaleAssociatedFunctor X Y).map d ≫ etaleCrossCoverMap X φ a c' =
      etaleCrossCoverMap X φ a c ≫ (etaleAssociatedFunctor X Z).map e := by
  apply crossCoverMap_coefficient_square X φ a
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction H).map c)
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction H).map c')
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).map d)
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction H).map e)
  apply Action.hom_injective
  change (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map d.hom ≫
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map c'.hom =
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map c.hom ≫
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map e.hom
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun k => (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map k)
    (congrArg (fun k => k.hom) h)

/-- Reduce an equivariant coefficient map, also across a group restriction. -/
def modulePowerReductionCrossMap (n : ℕ)
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (Action.res (ModuleCat.{u} R) φ).obj
        (((Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction G).obj M) ⟶
      ((Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction H).obj N :=
  ((Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction H).map c

/-- Power-reduced coefficient maps commute with the genuine quotient units. -/
theorem modulePowerReductionCrossMap_unit (n : ℕ)
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (Action.res (ModuleCat.{u} R) φ).map ((modulePowerReductionUnit I n).app M) ≫
        modulePowerReductionCrossMap I φ n c =
      c ≫ (modulePowerReductionUnit I n).app N := by
  exact ((modulePowerReductionUnit I n).naturality c).symm

/-- Power-reduced coefficient maps commute with every quotient transition. -/
theorem modulePowerReductionCrossMap_transition {m n : ℕ} (h : m ≤ n)
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (Action.res (ModuleCat.{u} R) φ).map
        ((modulePowerReductionTransition I h).app M) ≫
      modulePowerReductionCrossMap I φ m c =
        modulePowerReductionCrossMap I φ n c ≫
          (modulePowerReductionTransition I h).app N := by
  exact ((modulePowerReductionTransition I h).naturality c).symm

/-- Cross-cover maps at every reduced coefficient level form an inverse-system map. -/
def etaleCrossCoverModuleReductionSystemsMap
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (constantAssociatedModuleReductionFunctor I X Y).obj M ⟶
      (constantAssociatedModuleReductionFunctor I X Z).obj N where
  app n := etaleCrossCoverMap X φ a (modulePowerReductionCrossMap I φ n.unop c)
  naturality _m _n f :=
    etaleCrossCoverMap_coefficient_square X φ a _ _ _ _
      (modulePowerReductionCrossMap_transition I φ (leOfHom f.unop) c)

/-- Identity cover and coefficient maps give the identity on reduction systems. -/
@[simp]
theorem etaleCrossCoverModuleReductionSystemsMap_id
    (Y : Action X.Etale G) (M : Action (ModuleCat.{u} R) G) :
    etaleCrossCoverModuleReductionSystemsMap I X (MonoidHom.id G) (𝟙 Y) (𝟙 M) =
      𝟙 ((constantAssociatedModuleReductionFunctor I X Y).obj M) := by
  apply NatTrans.ext
  funext n
  dsimp only [NatTrans.id_app, etaleCrossCoverModuleReductionSystemsMap,
    modulePowerReductionCrossMap]
  erw [CategoryTheory.Functor.map_id]
  exact etaleCrossCoverMap_id X Y _

/-- Reduction-system maps retain the cover and coefficient composition law. -/
@[reassoc]
theorem etaleCrossCoverModuleReductionSystemsMap_comp
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N)
    {K : Type u} [Group K] {W : Action X.Etale K}
    {P : Action (ModuleCat.{u} R) K}
    (ψ : K →* H) (b : W ⟶ (Action.res X.Etale ψ).obj Z)
    (d : (Action.res (ModuleCat.{u} R) ψ).obj N ⟶ P) :
    etaleCrossCoverModuleReductionSystemsMap I X φ a c ≫
        etaleCrossCoverModuleReductionSystemsMap I X ψ b d =
      etaleCrossCoverModuleReductionSystemsMap I X (φ.comp ψ)
        (b ≫ (Action.res X.Etale ψ).map a)
        ((Action.res (ModuleCat.{u} R) ψ).map c ≫ d) := by
  apply NatTrans.ext
  funext n
  dsimp only [NatTrans.comp_app, etaleCrossCoverModuleReductionSystemsMap]
  rw [etaleCrossCoverMap_comp]
  congr 1
  apply Action.hom_injective
  exact ((Langlands.Coefficients.AdicSystem.powerReduction I n.unop).map_comp
    c.hom d.hom).symm

/-- Associated power reduction commutes with every compatible cover/coefficient map. -/
@[reassoc]
theorem constantAssociatedPowerReductionComparison_crossCover (n : ℕ)
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    ((Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).obj (op n)).map
        (etaleCrossCoverMap X φ a c) ≫
      (constantAssociatedPowerReductionComparison I X Z n).app N =
        (constantAssociatedPowerReductionComparison I X Y n).app M ≫
          etaleCrossCoverMap X φ a (modulePowerReductionCrossMap I φ n c) := by
  apply (cancel_epi ((Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app
    ((etaleAssociatedFunctor X Y).obj M))).mp
  have hq := (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).naturality
    (etaleCrossCoverMap X φ a c)
  simp only [CategoryTheory.Functor.id_map] at hq
  rw [← Category.assoc, ← hq, Category.assoc]
  erw [constantAssociatedPowerReductionComparison_unit I X Z n N,
    constantAssociatedPowerReductionComparison_unit_assoc I X Y n M]
  exact (etaleCrossCoverMap_coefficient_square X φ a c
    (modulePowerReductionCrossMap I φ n c)
    ((modulePowerReductionUnit I n).app M) ((modulePowerReductionUnit I n).app N)
    (modulePowerReductionCrossMap_unit I φ n c)).symm

/-- The comparison of whole reduction systems commutes with cross-cover maps. -/
theorem constantAssociatedReductionSystemsComparison_crossCover
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (EtaleAdicSystem.functor X I).map (etaleCrossCoverMap X φ a c) ≫
        (constantAssociatedReductionSystemsComparison I X Z).app N =
      (constantAssociatedReductionSystemsComparison I X Y).app M ≫
        etaleCrossCoverModuleReductionSystemsMap I X φ a c := by
  apply NatTrans.ext
  funext n
  exact constantAssociatedPowerReductionComparison_crossCover I X φ a n.unop c

end Langlands.Shimura.Coefficients
