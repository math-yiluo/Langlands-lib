import Langlands.Geometry.FormalGroup.GlobalAtlasRationalMorphism
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderMorphism
import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism

/-! # Global full-order rational maps and their atlas restrictions -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {E : ModuleLaw.OrderAction D M} {E' : ModuleLaw.OrderAction D N}
variable {E'' : ModuleLaw.OrderAction D P}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Actual order-linear chart comparisons preserve rational full-order commutation. -/
theorem ofGlobalOrderRationalHom_mem (f : ModuleLaw.OrderAction.RationalHom F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalRationalHom s hs f.val ∈
      OrderAction.rationalHomSubmodule F (ofGlobalCoverOrderAction E s hs)
        (ofGlobalCoverOrderAction E' s hs) (ofGlobalCover_opens_eq M N s hs) := by
  intro A b hb a
  have hc := ((ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
    (globalOrderChartIso E' b.val A hb).inv).comp
      ((ModuleLaw.OrderAction.RationalHom.map (IsScalarTower.toAlgHom O R A) f).comp
        (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
          (globalOrderChartIso E b.val A hb).hom))).commutes a
  have he := onChart_ofGlobalRationalHom f.val s hs A b hb
  exact (congrArg (fun t => ModuleLaw.RationalHom.comp t
    (ModuleLaw.RationalHom.ofHom
      ((((ofGlobalCoverOrderAction E s hs).chart
        (sourceChart (ofGlobalCover_opens_eq M N s hs) b)).map
          (coefficientLift (O := O) b.val A hb)).action a))) he).trans
    (hc.trans (congrArg (fun t => ModuleLaw.RationalHom.comp
      (ModuleLaw.RationalHom.ofHom
        ((((ofGlobalCoverOrderAction E' s hs).chart b).map
          (coefficientLift (O := O) b.val A hb)).action a)) t) he.symm))

/-- Restrict the actual rational global map and retain full-order chart commutation. -/
def ofGlobalOrderRationalHom (s : Set R) (hs : Ideal.span s = ⊤) :
    ModuleLaw.OrderAction.RationalHom F E E' →ₗ[F]
      OrderAction.RationalHom F (ofGlobalCoverOrderAction E s hs)
        (ofGlobalCoverOrderAction E' s hs) (ofGlobalCover_opens_eq M N s hs) where
  toFun f := ⟨ofGlobalRationalHom s hs f.val, ofGlobalOrderRationalHom_mem f s hs⟩
  map_add' f g := by
    apply OrderAction.RationalHom.ext
    exact (ofGlobalRationalHom s hs).map_add f.val g.val
  map_smul' c f := by
    apply OrderAction.RationalHom.ext
    exact (ofGlobalRationalHom s hs).map_smul c f.val

@[simp]
theorem ofGlobalOrderRationalHom_val (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ModuleLaw.OrderAction.RationalHom F E E') :
    (ofGlobalOrderRationalHom s hs f).val = ofGlobalRationalHom s hs f.val := rfl

/-- Restriction agrees with rationalization of actual integral order-linear maps. -/
@[simp]
theorem ofGlobalOrderRationalHom_ofHom (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ModuleLaw.OrderAction.Hom E E') :
    ofGlobalOrderRationalHom s hs (ModuleLaw.OrderAction.RationalHom.ofHom (F := F) f) =
      OrderAction.RationalHom.ofHom (F := F) (ofGlobalOrderHom f s hs) := by
  apply OrderAction.RationalHom.ext
  exact ofGlobalRationalHom_ofHom s hs f.val

@[simp]
theorem ofGlobalOrderRationalHom_id (E : ModuleLaw.OrderAction D M) (s : Set R)
    (hs : Ideal.span s = ⊤) :
    ofGlobalOrderRationalHom s hs (ModuleLaw.OrderAction.RationalHom.id (F := F) E) =
      OrderAction.RationalHom.id (ofGlobalCoverOrderAction E s hs) := by
  apply OrderAction.RationalHom.ext
  exact ofGlobalRationalHom_id M s hs

/-- Restriction preserves actual full-order rational composition. -/
@[simp]
theorem ofGlobalOrderRationalHom_comp (g : ModuleLaw.OrderAction.RationalHom F E' E'')
    (f : ModuleLaw.OrderAction.RationalHom F E E') (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalOrderRationalHom s hs (g.comp f) =
      (ofGlobalOrderRationalHom s hs g).comp (ofGlobalOrderRationalHom s hs f) := by
  apply OrderAction.RationalHom.ext
  exact ofGlobalRationalHom_comp g.val f.val s hs

/-- Restriction is a homomorphism of full-order rational endomorphism rings. -/
def ofGlobalOrderRationalEnd (E : ModuleLaw.OrderAction D M) (s : Set R)
    (hs : Ideal.span s = ⊤) :
    ModuleLaw.OrderAction.RationalHom F E E →+*
      OrderAction.RationalHom F (ofGlobalCoverOrderAction E s hs)
        (ofGlobalCoverOrderAction E s hs) rfl where
  toFun := ofGlobalOrderRationalHom s hs
  map_zero' := (ofGlobalOrderRationalHom s hs).map_zero
  map_add' := (ofGlobalOrderRationalHom s hs).map_add
  map_one' := ofGlobalOrderRationalHom_id E s hs
  map_mul' := fun g f => ofGlobalOrderRationalHom_comp g f s hs

/-- The chart formula holds in the actual coordinate full-order rational centralizer. -/
theorem onChart_ofGlobalOrderRationalHom (f : ModuleLaw.OrderAction.RationalHom F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) (A : CommAlgCat.{v} R) (b : s)
    (hb : IsUnit (algebraMap R A b.val)) :
    (ofGlobalOrderRationalHom s hs f).onChart A b hb =
      (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
        (globalOrderChartIso E' b.val A hb).inv).comp
          ((ModuleLaw.OrderAction.RationalHom.map (IsScalarTower.toAlgHom O R A) f).comp
            (ModuleLaw.OrderAction.RationalHom.ofHom (F := F)
              (globalOrderChartIso E b.val A hb).hom)) := by
  apply ModuleLaw.OrderAction.RationalHom.ext
  exact onChart_ofGlobalRationalHom f.val s hs A b hb

section QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Restrict both full-order rational maps with their actual two-sided inverse laws. -/
def ofGlobalOrderQuasiIsogeny (f : ModuleLaw.OrderAction.QuasiIsogeny F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) :
    OrderAction.QuasiIsogeny F (ofGlobalCoverOrderAction E s hs)
      (ofGlobalCoverOrderAction E' s hs) (ofGlobalCover_opens_eq M N s hs) where
  hom := ofGlobalOrderRationalHom s hs f.hom
  inv := ofGlobalOrderRationalHom s hs f.inv
  inv_hom := by
    apply OrderAction.RationalHom.ext
    exact (ofGlobalQuasiIsogeny f.toModuleQuasiIsogeny s hs).inv_hom
  hom_inv := by
    apply OrderAction.RationalHom.ext
    exact (ofGlobalQuasiIsogeny f.toModuleQuasiIsogeny s hs).hom_inv

@[simp]
theorem ofGlobalOrderQuasiIsogeny_hom (f : ModuleLaw.OrderAction.QuasiIsogeny F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalOrderQuasiIsogeny f s hs).hom = ofGlobalOrderRationalHom s hs f.hom := rfl

@[simp]
theorem ofGlobalOrderQuasiIsogeny_inv (f : ModuleLaw.OrderAction.QuasiIsogeny F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalOrderQuasiIsogeny f s hs).inv = ofGlobalOrderRationalHom s hs f.inv := rfl

/-- Forgetting the order recovers exactly the ambient global rational restriction. -/
@[simp]
theorem toAtlas_ofGlobalOrderQuasiIsogeny (f : ModuleLaw.OrderAction.QuasiIsogeny F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalOrderQuasiIsogeny f s hs).toAtlasQuasiIsogeny =
      ofGlobalQuasiIsogeny f.toModuleQuasiIsogeny s hs := by
  apply BasicAtlas.QuasiIsogeny.ext_hom
  rfl

@[simp]
theorem ofGlobalOrderQuasiIsogeny_refl (E : ModuleLaw.OrderAction D M) (s : Set R)
    (hs : Ideal.span s = ⊤) :
    ofGlobalOrderQuasiIsogeny (ModuleLaw.OrderAction.QuasiIsogeny.refl (F := F) E) s hs =
      OrderAction.QuasiIsogeny.refl (ofGlobalCoverOrderAction E s hs) := by
  apply OrderAction.QuasiIsogeny.ext_hom
  exact ofGlobalOrderRationalHom_id E s hs

@[simp]
theorem ofGlobalOrderQuasiIsogeny_symm (f : ModuleLaw.OrderAction.QuasiIsogeny F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalOrderQuasiIsogeny f.symm s hs = (ofGlobalOrderQuasiIsogeny f s hs).symm := by
  apply OrderAction.QuasiIsogeny.ext_hom
  rfl

@[simp]
theorem ofGlobalOrderQuasiIsogeny_trans (f : ModuleLaw.OrderAction.QuasiIsogeny F E E')
    (g : ModuleLaw.OrderAction.QuasiIsogeny F E' E'') (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalOrderQuasiIsogeny (f.trans g) s hs =
      (ofGlobalOrderQuasiIsogeny f s hs).trans (ofGlobalOrderQuasiIsogeny g s hs) := by
  apply OrderAction.QuasiIsogeny.ext_hom
  exact ofGlobalOrderRationalHom_comp g.hom f.hom s hs

@[simp]
theorem ofGlobalOrderQuasiIsogeny_ofIso (f : ModuleLaw.OrderAction.Iso E E')
    (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalOrderQuasiIsogeny (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F) f) s hs =
      OrderAction.QuasiIsogeny.ofIso (ofGlobalOrderIso f s hs) := by
  apply OrderAction.QuasiIsogeny.ext_hom
  exact ofGlobalOrderRationalHom_ofHom s hs f.hom

/-- Evaluating the quasi-isogeny uses actual coefficient and full-order chart maps. -/
theorem onChart_ofGlobalOrderQuasiIsogeny (f : ModuleLaw.OrderAction.QuasiIsogeny F E E')
    (s : Set R) (hs : Ideal.span s = ⊤) (A : CommAlgCat.{v} R) (b : s)
    (hb : IsUnit (algebraMap R A b.val)) :
    (ofGlobalOrderQuasiIsogeny f s hs).onChart A b hb =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (globalOrderChartIso E b.val A hb)).trans
        ((f.map (IsScalarTower.toAlgHom O R A)).trans
          (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
            (globalOrderChartIso E' b.val A hb)).symm) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact (onChart_ofGlobalOrderRationalHom f.hom s hs A b hb).trans
    (ModuleLaw.OrderAction.RationalHom.comp_assoc _ _ _).symm

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
