import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback

/-! # Actual polarized isomorphisms and coherent quotient pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules GroupScheme.Tate

variable (P : Prerequisites.{u}) {S S' S'' : Scheme.{u}} {A B : AbelianScheme S}

/-- Naturality of the existing canonical actual dual comparison, with all
presentations specified separately. -/
theorem DualWitness.baseChangeIso_naturality (WA : DualWitness A) (WB : DualWitness B)
    (b : S' ⟶ S) (WA' : DualWitness ((baseChange b).obj A))
    (WB' : DualWitness ((baseChange b).obj B)) (f : A ⟶ B) :
    (baseChange b).map (WA.map P WB f) ≫ (WA.baseChangeIso P b WA').hom =
      (WB.baseChangeIso P b WB').hom ≫ WA'.map P WB' ((baseChange b).map f) :=
  dualAbelianBaseChangeNaturality P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality P.compatibility S S' b A B
    WA.hasDual WA.geometry WA.inverseBundle WA.evaluation
    WB.hasDual WB.geometry WB.inverseBundle WB.evaluation
    WA'.hasDual WA'.geometry WA'.inverseBundle WA'.evaluation
    WB'.hasDual WB'.geometry WB'.inverseBundle WB'.evaluation f

/-- Identity coherence for the actual dual-valued map. -/
theorem DualWitness.pullbackMap_id (W : DualWitness A)
    (Wi : DualWitness ((baseChange (𝟙 S)).obj A)) (lam : A ⟶ W.dual P) :
    W.pullbackMap P (𝟙 S) Wi lam =
      (baseChangeIdIso A).hom ≫ lam ≫ Wi.map P W (baseChangeIdIso A).hom :=
  dualAbelianBaseChangeMap_id P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality P.compatibility A
    W.hasDual W.geometry W.inverseBundle W.evaluation
    Wi.hasDual Wi.geometry Wi.inverseBundle Wi.evaluation lam

/-- Composition coherence for actual dual-valued maps, with separate direct and
successive presentations and the existing contravariant dual of the comparison. -/
theorem DualWitness.pullbackMap_comp (W : DualWitness A) (b : S' ⟶ S) (c : S'' ⟶ S')
    (Wb : DualWitness ((baseChange b).obj A))
    (Wd : DualWitness ((baseChange (c ≫ b)).obj A))
    (Wc : DualWitness ((baseChange c).obj ((baseChange b).obj A)))
    (lam : A ⟶ W.dual P) :
    W.pullbackMap P (c ≫ b) Wd lam =
      (baseChangeCompIso b c A).hom ≫
        Wb.pullbackMap P c Wc (W.pullbackMap P b Wb lam) ≫
          Wd.map P Wc (baseChangeCompIso b c A).hom := by
  have h :=
    (dualAbelianBaseChangeMap_comp_pullback P.preservation P.stability P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.universality P.compatibility A
      W.hasDual W.geometry W.inverseBundle W.evaluation b c
      Wb.hasDual Wb.geometry Wb.inverseBundle Wb.evaluation
      Wd.hasDual Wd.geometry Wd.inverseBundle Wd.evaluation
      Wc.hasDual Wc.geometry Wc.inverseBundle Wc.evaluation lam).symm
  change W.pullbackMap P (c ≫ b) Wd lam =
    ((baseChangeCompIso b c A).hom ≫
      Wb.pullbackMap P c Wc (W.pullbackMap P b Wb lam)) ≫
        Wd.map P Wc (baseChangeCompIso b c A).hom at h
  exact h.trans (Category.assoc _ _ _)

variable {P} {g d n : ℕ} {a a' : Datum P S g d n}

/-- Pull back an actual polarized isomorphism, allowing any chosen changed
auxiliary presentations of its two endpoints. -/
def PolarizedIso.pullbackWith (e : PolarizedIso a a') (b : S' ⟶ S)
    (W : DualWitness ((baseChange b).obj a.abelian))
    (W' : DualWitness ((baseChange b).obj a'.abelian)) :
    PolarizedIso (a.pullbackWith b W) (a'.pullbackWith b W') where
  abelianIso := (baseChange b).mapIso e.abelianIso
  polarization_eq := by
    change (baseChange b).map a.polarization ≫ (a.dualWitness.baseChangeIso P b W).hom =
      (baseChange b).map e.abelianIso.hom ≫
        ((baseChange b).map a'.polarization ≫ (a'.dualWitness.baseChangeIso P b W').hom) ≫
          W.map P W' ((baseChange b).map e.abelianIso.hom)
    rw [e.polarization_eq, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [DualWitness.baseChangeIso_naturality P a.dualWitness a'.dualWitness b W W']
  level_eq i := by
    change mapTuple ((baseChange b).map e.abelianIso.hom)
      (pullbackTuple b a.level.sections) i = pullbackTuple b a'.level.sections i
    rw [pullbackTuple_map]
    exact congrArg (fun v => pullbackTuple b v i) (funext e.level_eq)

/-- Pullback respects the actual polarized-isomorphism relation. -/
def PolarizedIso.pullback (e : PolarizedIso a a') (b : S' ⟶ S) :
    PolarizedIso (a.pullback b) (a'.pullback b) :=
  e.pullbackWith b (a.dualWitness.pullback P b) (a'.dualWitness.pullback P b)

/-- All changed auxiliary presentations give the same actual polarized object. -/
def Datum.pullbackWithIso (a : Datum P S g d n) (b : S' ⟶ S)
    (W W' : DualWitness ((baseChange b).obj a.abelian)) :
    PolarizedIso (a.pullbackWith b W) (a.pullbackWith b W') := by
  refine PolarizedIso.ofParameterMap P (CategoryTheory.Iso.refl _) ?_ ?_
  · change W.parameterMap P (a.dualWitness.pullbackMap P b W a.polarization) =
      𝟙 _ ≫ W'.parameterMap P (a.dualWitness.pullbackMap P b W' a.polarization) ≫
        dualSchemeMap homPicardZeroPullback (𝟙 _) W.hasDual W'.hasDual
    rw [Category.id_comp, dualSchemeMap_id homPicardZeroPullback
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence, Category.comp_id,
      DualWitness.parameterMap_pullbackMap, DualWitness.parameterMap_pullbackMap]
  · exact (PolarizedIso.refl (a.pullbackWith b W)).level_eq

/-- Identity pullback is actually polarized-isomorphic to the supplied datum. -/
def Datum.pullbackIdIso (a : Datum P S g d n) :
    PolarizedIso (a.pullback (𝟙 S)) a where
  abelianIso := baseChangeIdIso a.abelian
  polarization_eq := DualWitness.pullbackMap_id P a.dualWitness
    (a.dualWitness.pullback P (𝟙 S)) a.polarization
  level_eq i := congrFun (pullbackTuple_id a.level.sections) i

/-- Direct pullback is actually polarized-isomorphic to successive pullback. -/
def Datum.pullbackCompIso (a : Datum P S g d n) (b : S' ⟶ S) (c : S'' ⟶ S') :
    PolarizedIso (a.pullback (c ≫ b)) ((a.pullback b).pullback c) where
  abelianIso := baseChangeCompIso b c a.abelian
  polarization_eq := DualWitness.pullbackMap_comp P a.dualWitness b c
    (a.dualWitness.pullback P b) (a.dualWitness.pullback P (c ≫ b))
    ((a.dualWitness.pullback P b).pullback P c) a.polarization
  level_eq i := congrFun (pullbackTuple_comp b c a.level.sections) i

/-- Constructed pullback descends to the actual quotient of data. -/
def Moduli.pullback (b : S' ⟶ S) : Moduli P S g d n → Moduli P S' g d n :=
  Quotient.map (fun a => a.pullback b) (fun _ _ ⟨e⟩ => ⟨e.pullback b⟩)

@[simp] theorem Moduli.pullback_classOf (b : S' ⟶ S) (a : Datum P S g d n) :
    Moduli.pullback b a.classOf = (a.pullback b).classOf := rfl

/-- The representative formula is independent of the chosen changed evaluation. -/
theorem Moduli.pullback_classOf_with (b : S' ⟶ S) (a : Datum P S g d n)
    (W : DualWitness ((baseChange b).obj a.abelian)) :
    Moduli.pullback b a.classOf = (a.pullbackWith b W).classOf :=
  Datum.classOf_eq (a.pullbackWithIso b (a.dualWitness.pullback P b) W)

/-- Changing the original auxiliary evaluation also leaves every restriction
class unchanged. -/
theorem Moduli.pullback_withDualWitness (b : S' ⟶ S) (a : Datum P S g d n)
    (W : DualWitness a.abelian) :
    Moduli.pullback b (a.withDualWitness P W).classOf = Moduli.pullback b a.classOf :=
  congrArg (Moduli.pullback b) (a.withDualWitness_classOf P W)

@[simp] theorem Moduli.pullback_id (x : Moduli P S g d n) :
    Moduli.pullback (𝟙 S) x = x := by
  induction x using Quotient.inductionOn with
  | h a => exact Datum.classOf_eq a.pullbackIdIso

theorem Moduli.pullback_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (x : Moduli P S g d n) :
    Moduli.pullback (c ≫ b) x = Moduli.pullback c (Moduli.pullback b x) := by
  induction x using Quotient.inductionOn with
  | h a => exact Datum.classOf_eq (a.pullbackCompIso b c)

end Langlands.AbelianScheme.PolarizedFiniteLevel
