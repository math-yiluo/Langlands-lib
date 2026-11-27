import Langlands.GroupScheme.Torus.CocharacterFieldTransport
import Langlands.GroupScheme.Torus.WeilCocharacterTransfer
import Langlands.GroupScheme.Torus.LatticeBaseInvariants

/-! # Cocharacter values on a tower of fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace cocharacterLattice

open StarActionFiniteStage

variable (F E M : Type u) [Field F] [Field E] [Field M]
  [Algebra F E] [Algebra F M] [Algebra E M] [IsScalarTower F E M]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

local notation "b" => algebraBaseMap F E
local notation "j" => algebraBaseMap E M
local notation "c" => algebraBaseMap F M
local notation "hc" => Lie.algebraBaseMap_tower (k := F) (K := E) (L := M)
local notation "TE" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "TM" => Functor.obj (CommGroupScheme.baseChange c) T
local notation "iso" => towerIsoOf b j T c hc

private theorem groupTowerIsoOf_inv_fst {S U V : Scheme.{u}} (b' : U ⟶ S) (j' : V ⟶ U)
    (G : GroupScheme S) (c' : V ⟶ S) (hc' : j' ≫ b' = c') :
    (groupTowerIsoOf b' j' c' hc' G).inv.hom.hom.left ≫ pullback.fst G.X.hom c' =
      pullback.fst (pullback.snd G.X.hom b') j' ≫ pullback.fst G.X.hom b' := by
  subst c'
  rw [groupTowerIsoOf, eqToIso_refl, Iso.refl_trans]
  exact baseChangeCompIso_inv_fst b' j' G

variable {F E M} in
private theorem cocharacterValue_apply
    (ν : (Gm (Spec (CommRingCat.of E))).toGrp ⟶ (GroupScheme.baseChange b).obj T.toGrp)
    (a : Mˣ) :
    WeilGm.cocharacterValue F E T ν M a =
      Lie.affineBaseChangeEquiv F E T.toGrp M
        ((Gm.algebraPointsEquiv (R := CommRingCat.of E) M).symm a ≫ ν.hom.hom) := rfl

variable {F E M} in
private theorem cocharacterValue_left
    (ν : (Gm (Spec (CommRingCat.of E))).toGrp ⟶ (GroupScheme.baseChange b).obj T.toGrp)
    (a : Mˣ) :
    (WeilGm.cocharacterValue F E T ν M a).left =
      ((Gm.algebraPointsEquiv (R := CommRingCat.of E) M).symm a).left ≫
        ν.hom.hom.left ≫ pullback.fst T.X.hom b := by
  change (Lie.affineBaseChangeEquiv F E T.toGrp M
    ((Gm.algebraPointsEquiv (R := CommRingCat.of E) M).symm a ≫ ν.hom.hom)).left = _
  simp only [Lie.affineBaseChangeEquiv_left, Over.comp_left, Category.assoc]

private theorem groupHom_congr_towerIso_symm
    (ν : cocharacterLattice ((CommGroupScheme.baseChange j).obj TE)) :
    CommGroupScheme.groupHom (cocharacterLattice.congr (iso).symm ν) =
      CommGroupScheme.groupHom ν ≫ (groupTowerIsoOf b j c hc T.toGrp).inv := by
  change CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom (iso).inv = _
  rw [groupHom_towerIsoOf_inv]

/-- Projecting a cocharacter evaluation through the direct base change gives
its evaluation through the iterated base change. -/
theorem cocharacterValue_towerIso (ν : cocharacterLattice ((CommGroupScheme.baseChange j).obj TE))
    (a : Mˣ) :
    WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom (cocharacterLattice.congr (iso).symm ν)) M a =
      Lie.affineBaseChangeEquiv F E T.toGrp M
        (WeilGm.cocharacterValue E M TE (CommGroupScheme.groupHom ν) M a) := by
  apply Over.OverMorphism.ext
  rw [cocharacterValue_left T, Lie.affineBaseChangeEquiv_left, cocharacterValue_left TE,
    groupHom_congr_towerIso_symm, Grp.comp_hom_hom, Over.comp_left]
  simp only [Category.assoc, groupTowerIsoOf_inv_fst]
  rfl

omit [Algebra F M] [IsScalarTower F E M] in
private theorem cocharacterValue_baseChange (ν : cocharacterLattice TE) (a : Mˣ) :
    WeilGm.cocharacterValue E M TE (CommGroupScheme.groupHom
      (cocharacterLattice.baseChange j TE ν)) M a =
      (Gm.algebraPointsEquiv (R := CommRingCat.of E) M).symm a ≫
        (CommGroupScheme.groupHom ν).hom.hom := by
  let U := (algSpec (CommRingCat.of M)).obj (op (CommAlgCat.of M M))
  let V := (algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E M))
  let x := (Gm.algebraPointsEquiv (R := CommRingCat.of M) M).symm a
  let y := (Gm.algebraPointsEquiv (R := CommRingCat.of E) M).symm a
  let t := (Lie.affineBaseTestIso E M M).inv
  have hx : t ≫ (Gm.pointsEquiv _ ((Over.map j).obj U)).symm (Gm.pointsEquiv _ U x) = y := by
    apply (Gm.pointsEquiv (Spec (CommRingCat.of E)) V).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    apply Units.ext
    apply (Scheme.ΓSpecIso (CommRingCat.of M)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of M)).hom
       (Units.map t.left.appTop.hom.toMonoidHom (Gm.pointsEquiv _ U x)).val = _
    have ht : t.left = 𝟙 (Spec (CommRingCat.of M)) := rfl
    rw [ht, Scheme.Hom.id_appTop]
    change (Gm.algebraPointsEquiv (R := CommRingCat.of M) M x : M) =
      (Gm.algebraPointsEquiv (R := CommRingCat.of E) M y : M)
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  change t ≫ baseChangePointsEquiv j (TE).toGrp U
      (x ≫ (CommGroupScheme.groupHom (cocharacterLattice.baseChange j TE ν)).hom.hom) =
    y ≫ (CommGroupScheme.groupHom ν).hom.hom
  rw [cocharacterLattice.baseChange_points, ← Category.assoc, hx]

/-- Extending a cocharacter to the last field of a tower preserves its value
at every unit of that field in the original coefficient-point group. -/
theorem cocharacterValue_towerExtension (ν : cocharacterLattice TE) (a : Mˣ) :
    WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom (towerExtension F E M T ν)) M a =
      WeilGm.cocharacterValue F E T (CommGroupScheme.groupHom ν) M a := by
  let νM := cocharacterLattice.baseChange j TE ν
  have hν : towerExtension F E M T ν = cocharacterLattice.congr (iso).symm νM := rfl
  calc
    _ = WeilGm.cocharacterValue F M T
        (CommGroupScheme.groupHom (cocharacterLattice.congr (iso).symm νM)) M a :=
      congrArg (fun ψ : cocharacterLattice TM =>
        WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom ψ) M a) hν
    _ = Lie.affineBaseChangeEquiv F E T.toGrp M
        (WeilGm.cocharacterValue E M TE (CommGroupScheme.groupHom νM) M a) :=
      cocharacterValue_towerIso F E M T νM a
    _ = _ := (congrArg (fun p : Lie.AffinePoints (TE).toGrp M =>
      Lie.affineBaseChangeEquiv F E T.toGrp M p)
        (cocharacterValue_baseChange F E M T ν a)).trans
      (cocharacterValue_apply T (CommGroupScheme.groupHom ν) a).symm

end cocharacterLattice

/-- Cocharacter evaluation on a field tower is independent of whether the
cocharacter is first extended to the top field. -/
def CocharacterFieldValueStatement : Prop :=
  ∀ (F E M : Type u) [Field F] [Field E] [Field M]
    [Algebra F E] [Algebra F M] [Algebra E M] [IsScalarTower F E M]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T))
    (a : Mˣ),
    WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom
        (cocharacterLattice.towerExtension F E M T ν)) M a =
      WeilGm.cocharacterValue F E T (CommGroupScheme.groupHom ν) M a

theorem cocharacterFieldValue : CocharacterFieldValueStatement.{u} := by
  intro F E M _ _ _ _ _ _ _ T ν a
  exact cocharacterLattice.cocharacterValue_towerExtension F E M T ν a

end Langlands.GroupScheme
