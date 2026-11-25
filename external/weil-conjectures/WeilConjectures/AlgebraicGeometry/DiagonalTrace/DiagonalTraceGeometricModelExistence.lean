/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorGeometryExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassLinePullbackExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjointNaturality
import all WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators

/-! # Geometric line projection data for a specified projective model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses WeilConjectures

attribute [local irreducible] lineModule adjointSection evaluatedAdjoint ordinaryAdjoint
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap

-- These helpers only use the ordinary tensor and the given normalized adjunction.
private def tensorRightIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) {N N' : Systems T (Arings l E T)} (e : N ≅ N') :
    tensorRight l E T N ≅ tensorRight l E T N' := by
  letI := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  letI := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  refine NatIso.ofComponents (fun M ↦
    { hom := SheafOfModules.siteSheafTensorSecondMap M e.hom
      inv := SheafOfModules.siteSheafTensorSecondMap M e.inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · apply SheafOfModules.tensor_ext.{u + 1, u, u + 1} (systemRing l E T)
    intro U x y
    change (SheafOfModules.siteSheafTensorSecondMap M e.inv).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap M e.hom).val.app U
        (SheafOfModules.siteSheafTensorTmul M N U x y)) = _
    rw [SheafOfModules.tensor_second.{u + 1, u, u + 1},
      SheafOfModules.tensor_second.{u + 1, u, u + 1}]
    have hy : e.inv.val.app U (e.hom.val.app U y) = y :=
      congrArg (fun a ↦ a.val.app U y) e.hom_inv_id
    exact congrArg (fun z ↦ SheafOfModules.siteSheafTensorTmul M N U x z) hy
  · apply SheafOfModules.tensor_ext.{u + 1, u, u + 1} (systemRing l E T)
    intro U x y
    change (SheafOfModules.siteSheafTensorSecondMap M e.hom).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap M e.inv).val.app U
        (SheafOfModules.siteSheafTensorTmul M N' U x y)) = _
    rw [SheafOfModules.tensor_second.{u + 1, u, u + 1},
      SheafOfModules.tensor_second.{u + 1, u, u + 1}]
    have hy : e.hom.val.app U (e.inv.val.app U y) = y :=
      congrArg (fun a ↦ a.val.app U y) e.inv_hom_id
    exact congrArg (fun z ↦ SheafOfModules.siteSheafTensorTmul M N' U x z) hy
  · intro M M' a
    exact SheafOfModules.siteSheafTensorSecondMap_naturality a e.hom

private theorem tensorRightIso_pure
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (M : Systems T (Arings l E T))
    {N N' : Systems T (Arings l E T)} (e : N ≅ N')
    (U : (ℕ × T.ProEt)ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((tensorRightIso l E T e).hom.app M).val.app U (tensorPure l E T M N U x y) =
      tensorPure l E T M N' U x (e.hom.val.app U y) := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  exact SheafOfModules.tensor_second.{u + 1, u, u + 1} (systemRing l E T) M N N' e.hom U x y

private def lineTensorComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (k : TensorPullback l E f g)
    {cY : Chern l E Y} {cX : Chern l E X} (p : LinePullback l E f g cY cX) :
    positive l E cY ⋙ g.pull ≅ g.pull ⋙ positive l E cX :=
  k.iso (lineModule l E cY) ≪≫ Functor.isoWhiskerLeft g.pull (tensorRightIso l E X p.iso)

private theorem lineTensorComparison_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (k : TensorPullback l E f g)
    {cY : Chern l E Y} {cX : Chern l E X} (p : LinePullback l E f g cY cX)
    (M : Systems Y (Arings l E Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop)))
    (y : (lineModule l E cY).val.obj (op (n, U.unop))) :
    HEq (sectionAdjoint l E g ((lineTensorComparison l E g k p).hom.app M) n U
      (pure l E cY M (op (n, U.unop)) x y))
      (pure l E cX (g.pull.obj M) (op (n, (chart f U).unop))
        (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
        (sectionAdjoint l E g p.iso.hom n U y)) := by
  have ht : sectionAdjoint l E g ((k.iso (lineModule l E cY)).hom.app M) n U
      (tensorPure l E Y M (lineModule l E cY) (op (n, U.unop)) x y) =
    tensorPure l E X (g.pull.obj M) (g.pull.obj (lineModule l E cY))
      (op (n, (chart f U).unop))
      (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
      (sectionAdjoint l E g (𝟙 (g.pull.obj (lineModule l E cY))) n U y) :=
    eq_of_heq (k.normalization M (lineModule l E cY) n U x y)
  change HEq (sectionAdjoint l E g
    ((k.iso (lineModule l E cY)).hom.app M ≫
      (tensorRightIso l E X p.iso).hom.app (g.pull.obj M)) n U
        (tensorPure l E Y M (lineModule l E cY) (op (n, U.unop)) x y)) _
  rw [sectionAdjoint_postcomp, ht]
  have he := tensorRightIso_pure l E X (g.pull.obj M) p.iso
    (op (n, (chart f U).unop))
    (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
    (sectionAdjoint l E g (𝟙 (g.pull.obj (lineModule l E cY))) n U y)
  have hp := sectionAdjoint_postcomp l E g
    (𝟙 (g.pull.obj (lineModule l E cY))) p.iso.hom n U y
  simp only [Category.id_comp] at hp
  exact (heq_of_eq he).trans (heq_of_eq (congrArg
    (fun z ↦ tensorPure l E X (g.pull.obj M) (lineModule l E cX)
      (op (n, (chart f U).unop))
      (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x) z) hp.symm))

private def transportedLineComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (k : TensorPullback l E f g)
    {cY : Chern l E Y} {cX : Chern l E X} (p : LinePullback l E f g cY cX)
    (F : Systems Y (Arings l E Y) ⥤ Systems Y (Arings l E Y))
    (G : Systems X (Arings l E X) ⥤ Systems X (Arings l E X))
    (hF : F = positive l E cY) (hG : G = positive l E cX) :
    F ⋙ g.pull ≅ g.pull ⋙ G := by
  subst F
  subst G
  exact lineTensorComparison l E g k p

private theorem transportedLineComparison_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (k : TensorPullback l E f g)
    {cY : Chern l E Y} {cX : Chern l E X} (p : LinePullback l E f g cY cX)
    (F : Systems Y (Arings l E Y) ⥤ Systems Y (Arings l E Y))
    (G : Systems X (Arings l E X) ⥤ Systems X (Arings l E X))
    (hF : F = positive l E cY) (hG : G = positive l E cX)
    (M : Systems Y (Arings l E Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop)))
    (y : (lineModule l E cY).val.obj (op (n, U.unop)))
    (v : (F.obj M).val.obj (op (n, U.unop)))
    (hv : HEq v (pure l E cY M (op (n, U.unop)) x y)) :
    HEq (sectionAdjoint l E g
      ((transportedLineComparison l E g k p F G hF hG).hom.app M) n U v)
      (pure l E cX (g.pull.obj M) (op (n, (chart f U).unop))
        (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
        (sectionAdjoint l E g p.iso.hom n U y)) := by
  subst F
  subst G
  have hv' : v = pure l E cY M (op (n, U.unop)) x y := eq_of_heq hv
  subst v
  exact lineTensorComparison_normalization l E g k p M n U x y

private theorem positivePullback_nonempty
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (k : TensorPullback l E f g)
    {cY : Chern l E Y} {cX : Chern l E X}
    (tY : Twisting l E cY) (tX : Twisting l E cX)
    (p : LinePullback l E f g cY cX) :
    Nonempty (PositivePullback l E f g tY tX p) := by
  refine ⟨{
    iso := transportedLineComparison l E g k p
      tY.equivalence.functor tX.equivalence.functor tY.forward tX.forward
    normalization := ?_ }⟩
  intro M n U x y v x' y' hv hx hy
  have hx' : x' = sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x :=
    eq_of_heq (hx.trans (sectionAdjoint_heq l E g (𝟙 (g.pull.obj M)) n U x).symm)
  have hy' : y' = sectionAdjoint l E g p.iso.hom n U y :=
    eq_of_heq (hy.trans (sectionAdjoint_heq l E g p.iso.hom n U y).symm)
  have hn := transportedLineComparison_normalization l E g k p
    tY.equivalence.functor tX.equivalence.functor tY.forward tX.forward M n U x y v hv
  have h0 := sectionAdjoint_heq l E g
    ((transportedLineComparison l E g k p tY.equivalence.functor
      tX.equivalence.functor tY.forward tX.forward).hom.app M) n U v
  have hxy := congrArg₂
    (fun (a : (g.pull.obj M).val.obj (op (n, (chart f U).unop)))
      (z : (lineModule l E cX).val.obj (op (n, (chart f U).unop))) ↦
      pure l E cX (g.pull.obj M) (op (n, (chart f U).unop)) a z) hx'.symm hy'.symm
  exact h0.symm.trans (hn.trans (heq_of_eq hxy))

private theorem lineProjection_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {X S : Scheme.{u}} {f : X ⟶ S}
    (g : SpTowerShriek.Geometry l E b f)
    {cS : Chern l E S} {cX : Chern l E X}
    {tS : Twisting l E cS} {tX : Twisting l E cX}
    {p : LinePullback l E f g cS cX}
    (v : PositivePullback l E f g tS tX p) (M : D X (Arings l E X)) :
    IsIso (projection l E g v M) := by
  let a := SpTowerShriek.adjunction l E b g
  let e := v.derivedIso l E
  have hi : IsIso (mateEquiv a a e.hom) :=
    isIso_mateEquiv_of_isEquivalence_of_fullyFaithful a a (tS.T l E) (tX.T l E) e
  have he : projection l E g v M = (mateEquiv a a e.hom).app M := by
    dsimp only [a, e]
    simp only [projection, Adjunction.homEquiv_unit, mateEquiv_apply,
      NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Category.id_comp, Functor.map_comp]
    erw [Category.comp_id]
  rw [he]
  infer_instance

/-- The normalized line pullback and projection mate exist on the given model.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
and `sk-prop-sp-tower-geometric-classes.proof.md`, clause (4).
(blueprint: lem-sfb-diagonal-trace-geometric-model-existence).

Proof: use exists_tensorGeometry to choose the sequence-site coefficient calculus
and normalized ordinary inverse-image/direct-image adjunction, with the unital
coefficient comparison and the ordinary tensor comparison. Apply
linePullback_nonempty to the given normalized Chern data. Specialize ordinary
tensor pullback to the base line and postcompose with tensor in the second factor
by its line pullback. On pure sections, adjunction naturality identifies the second
factor with the adjoint of the line comparison; this proves PositivePullback with
its prescribed normalization, not just an arbitrary functor isomorphism.
Localize this ordinary comparison. The derived twists are equivalences, so the
right mate is invertible. Expanding the mate and homEquiv_unit identifies its
component with exactly the specified projection. Set model to m and over_eq to hm.
No cohomological splitting, trace, or local-freeness theorem is used for this mate
argument. Empty schemes and empty charts obey the same formulas.
-/
theorem exists_diagonalTraceGeometricModel (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) (m : X ≅ ProjectiveLine S)
    (hm : m.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (l : Γ(S, ⊤)))
    (cS : Chern l (ULift.{u} (Padic l)) S)
    (cX : Chern l (ULift.{u} (Padic l)) X)
    (nS : cS.Normalized l (ULift.{u} (Padic l)))
    (nX : cX.Normalized l (ULift.{u} (Padic l)))
    (tS : Twisting l (ULift.{u} (Padic l)) cS)
    (tX : Twisting l (ULift.{u} (Padic l)) cX) :
    ∃ b : SpTowerShriek.Base l (ULift.{u} (Padic l)),
      ∃ g : Model l (ULift.{u} (Padic l)) b S X f cS cX tS tX,
        g.model = m := by
  obtain ⟨b, g, ⟨q⟩, ⟨k⟩⟩ := exists_tensorGeometry l (ULift.{u} (Padic l)) f
  obtain ⟨p⟩ := linePullback_nonempty l (ULift.{u} (Padic l))
    f g q k hS cS cX nS nX
  obtain ⟨v⟩ := positivePullback_nonempty l (ULift.{u} (Padic l)) g k tS tX p
  let G : Model l (ULift.{u} (Padic l)) b S X f cS cX tS tX := {
    model := m
    over_eq := hm
    geometry := g
    coefficientPullback := q
    linePullback := p
    positivePullback := v
    projection_iso := lineProjection_isIso l (ULift.{u} (Padic l)) g v
      (unit X (Arings l (ULift.{u} (Padic l)) X)) }
  exact ⟨b, G, rfl⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
