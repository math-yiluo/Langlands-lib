import Langlands.Geometry.FormalGroup.FiniteKernelSchemeModels
import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeHom
import Langlands.GroupScheme.Cartier.FiniteDualSchemes

/-! # Actual finite dual diagrams of scalar torsion -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite _root_.AlgebraicGeometry GroupScheme.Cartier.FiniteDual

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

namespace Hom.FiniteKernelModel

variable {f : Hom M N} (P : f.FiniteKernelModel)

attribute [local instance] isFinite_commGroupScheme flat_commGroupScheme
  locallyOfFinitePresentation_commGroupScheme

/-- The finite dual of the actual kernel group scheme. -/
def dualCommGroupScheme : Langlands.CommGroupScheme (Spec (CommRingCat.of R)) :=
  schemeDual P.commGroupScheme

/-- Duals of actual represented kernels are finite, flat and locally of finite presentation. -/
theorem dualCommGroupScheme_finiteLocallyFree :
    IsFinite P.dualCommGroupScheme.X.hom ∧ Flat P.dualCommGroupScheme.X.hom ∧
      LocallyOfFinitePresentation P.dualCommGroupScheme.X.hom :=
  schemeDual_finiteLocallyFree P.commGroupScheme

variable {σ' τ' σ'' τ'' : Type} [Finite σ'] [Finite τ'] [Finite σ''] [Finite τ'']
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {M'' : ModuleLaw O R σ''} {N'' : ModuleLaw O R τ''}
variable {g : Hom M' N'} {k : Hom M'' N''}
variable (Q : g.FiniteKernelModel) (U : k.FiniteKernelModel)

/-- The dual map between the actual finite kernel group schemes. -/
def dualCommGroupSchemeMap (a : P.commGroupScheme ⟶ Q.commGroupScheme) :
    Q.dualCommGroupScheme ⟶ P.dualCommGroupScheme :=
  schemeDualMap a

@[simp]
theorem dualCommGroupSchemeMap_id : P.dualCommGroupSchemeMap P (𝟙 _) = 𝟙 _ :=
  schemeDualMap_id

@[simp]
theorem dualCommGroupSchemeMap_comp (a : P.commGroupScheme ⟶ Q.commGroupScheme)
    (b : Q.commGroupScheme ⟶ U.commGroupScheme) :
    P.dualCommGroupSchemeMap U (a ≫ b) = Q.dualCommGroupSchemeMap U b ≫ P.dualCommGroupSchemeMap Q a :=
  schemeDualMap_comp a b

end Hom.FiniteKernelModel

namespace IsPiDivisible

variable (hM : M.IsPiDivisible π)

/-- The forward dual arrows are the duals of the actual scalar multiplication transitions. -/
def torsionSchemeDualInclusions : ℕ ⥤ Langlands.CommGroupScheme (Spec (CommRingCat.of R)) where
  obj n := (hM.torsionKernelModel n).dualCommGroupScheme
  map {m n} i := (hM.torsionKernelModel n).dualCommGroupSchemeMap (hM.torsionKernelModel m)
    (hM.torsionSchemeTower.map i.op)
  map_id n :=
    let P := hM.torsionKernelModel n
    (congrArg (P.dualCommGroupSchemeMap P) (hM.torsionSchemeTower.map_id (op n))).trans
      P.dualCommGroupSchemeMap_id
  map_comp {l m n} i j :=
    let P := hM.torsionKernelModel n
    let Q := hM.torsionKernelModel m
    let U := hM.torsionKernelModel l
    let a : P.commGroupScheme ⟶ Q.commGroupScheme := hM.torsionSchemeTower.map j.op
    let b : Q.commGroupScheme ⟶ U.commGroupScheme := hM.torsionSchemeTower.map i.op
    (congrArg (P.dualCommGroupSchemeMap U) (hM.torsionSchemeTower.map_comp j.op i.op)).trans
      (P.dualCommGroupSchemeMap_comp Q U a b)

/-- The backward dual arrows are the duals of the actual torsion inclusions. -/
def torsionSchemeDualTower : ℕᵒᵖ ⥤ Langlands.CommGroupScheme (Spec (CommRingCat.of R)) where
  obj n := (hM.torsionKernelModel n.unop).dualCommGroupScheme
  map {m n} i := (hM.torsionKernelModel n.unop).dualCommGroupSchemeMap (hM.torsionKernelModel m.unop)
    (hM.torsionSchemeInclusions.map i.unop)
  map_id n :=
    let P := hM.torsionKernelModel n.unop
    (congrArg (P.dualCommGroupSchemeMap P) (hM.torsionSchemeInclusions.map_id n.unop)).trans
      P.dualCommGroupSchemeMap_id
  map_comp {l m n} i j :=
    let P := hM.torsionKernelModel n.unop
    let Q := hM.torsionKernelModel m.unop
    let U := hM.torsionKernelModel l.unop
    let a : P.commGroupScheme ⟶ Q.commGroupScheme := hM.torsionSchemeInclusions.map j.unop
    let b : Q.commGroupScheme ⟶ U.commGroupScheme := hM.torsionSchemeInclusions.map i.unop
    (congrArg (P.dualCommGroupSchemeMap U) (hM.torsionSchemeInclusions.map_comp j.unop i.unop)).trans
      (P.dualCommGroupSchemeMap_comp Q U a b)

variable (hN : N.IsPiDivisible π)

/-- An integral formal map induces an actual map of dual levels in the opposite direction. -/
def torsionSchemeDualMap (f : Hom M N) (n : ℕ) :
    hN.torsionSchemeDualInclusions.obj n ⟶ hM.torsionSchemeDualInclusions.obj n :=
  (hM.torsionKernelModel n).dualCommGroupSchemeMap (hN.torsionKernelModel n)
    (f.scalarTorsionSchemeMap hM hN n)

/-- The dual level maps commute with all forward dual arrows. -/
def torsionSchemeDualInclusionNatTrans (f : Hom M N) :
    hN.torsionSchemeDualInclusions ⟶ hM.torsionSchemeDualInclusions where
  app n := hM.torsionSchemeDualMap hN f n
  naturality m n i := by
    let P := hM.torsionKernelModel n
    let Q := hM.torsionKernelModel m
    let U := hN.torsionKernelModel n
    let V := hN.torsionKernelModel m
    let a : P.commGroupScheme ⟶ Q.commGroupScheme := hM.torsionSchemeTower.map i.op
    let b : U.commGroupScheme ⟶ V.commGroupScheme := hN.torsionSchemeTower.map i.op
    let x : P.commGroupScheme ⟶ U.commGroupScheme := f.scalarTorsionSchemeMap hM hN n
    let y : Q.commGroupScheme ⟶ V.commGroupScheme := f.scalarTorsionSchemeMap hM hN m
    have h : a ≫ y = x ≫ b := f.scalarTorsionSchemeMap_transition hM hN i
    exact (P.dualCommGroupSchemeMap_comp U V x b).symm.trans
      ((congrArg (P.dualCommGroupSchemeMap V) h.symm).trans (P.dualCommGroupSchemeMap_comp Q V a y))

/-- The same maps commute with all backward dual arrows. -/
def torsionSchemeDualTowerNatTrans (f : Hom M N) :
    hN.torsionSchemeDualTower ⟶ hM.torsionSchemeDualTower where
  app n := hM.torsionSchemeDualMap hN f n.unop
  naturality m n i := by
    let P := hM.torsionKernelModel n.unop
    let Q := hM.torsionKernelModel m.unop
    let U := hN.torsionKernelModel n.unop
    let V := hN.torsionKernelModel m.unop
    let a : P.commGroupScheme ⟶ Q.commGroupScheme := hM.torsionSchemeInclusions.map i.unop
    let b : U.commGroupScheme ⟶ V.commGroupScheme := hN.torsionSchemeInclusions.map i.unop
    let x : P.commGroupScheme ⟶ U.commGroupScheme := f.scalarTorsionSchemeMap hM hN n.unop
    let y : Q.commGroupScheme ⟶ V.commGroupScheme := f.scalarTorsionSchemeMap hM hN m.unop
    have h : a ≫ y = x ≫ b := f.scalarTorsionSchemeMap_inclusion hM hN i.unop
    exact (P.dualCommGroupSchemeMap_comp U V x b).symm.trans
      ((congrArg (P.dualCommGroupSchemeMap V) h.symm).trans (P.dualCommGroupSchemeMap_comp Q V a y))

@[simp]
theorem torsionSchemeDualMap_id (n : ℕ) : hM.torsionSchemeDualMap hM (Hom.id M) n = 𝟙 _ :=
  let P := hM.torsionKernelModel n
  (congrArg (P.dualCommGroupSchemeMap P) (Hom.scalarTorsionSchemeMap_id hM n)).trans
    P.dualCommGroupSchemeMap_id

variable {υ : Type} [Finite υ] {L : ModuleLaw O R υ} (hL : L.IsPiDivisible π)

/-- Dual level maps reverse composition of actual integral formal maps. -/
theorem torsionSchemeDualMap_comp (f : Hom M N) (g : Hom N L) (n : ℕ) :
    hM.torsionSchemeDualMap hL (g.comp f) n =
      hN.torsionSchemeDualMap hL g n ≫ hM.torsionSchemeDualMap hN f n :=
  let P := hM.torsionKernelModel n
  let Q := hN.torsionKernelModel n
  let U := hL.torsionKernelModel n
  (congrArg (P.dualCommGroupSchemeMap U) (Hom.scalarTorsionSchemeMap_comp hM hN hL g f n)).trans
    (P.dualCommGroupSchemeMap_comp Q U (f.scalarTorsionSchemeMap hM hN n)
      (g.scalarTorsionSchemeMap hN hL n))

end IsPiDivisible
end Langlands.FormalGroup.ModuleLaw
