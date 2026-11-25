/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.CyclicModuleConstantReflection
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite constant values for cyclic module sheaves

Source: Stacks Project, Tags 03RU and 03RW(2),(3), with cyclic coefficients.
(blueprint: lem-weil-pbc-finite-local-cyclic-module-forget).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private noncomputable def abelianConstantValueStalkIso {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : Y.Etale) (E : AddCommGrpCat.{u + 1})
    (e : G.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U)
      AddCommGrpCat.{u + 1}).obj E)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj G ≅ E := by
  let ePullback : (Etale.upperStar AddCommGrpCat.{u + 1} U.hom).obj G ≅
      (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E :=
    (overSheafEquivFunctorObjOverIso AddCommGrpCat.{u + 1} U G).symm ≪≫
      (Etale.overSheafEquiv U AddCommGrpCat.{u + 1}).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
        AddCommGrpCat.{u + 1} CategoryTheory.Over.mkIdTerminal).app E
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} U.hom s).app G).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso ePullback ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso E

private noncomputable def forgetConstantValueIso {Y : Scheme.{u}}
    (n : ℕ) [NeZero n]
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    (U : Y.Etale) (E : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
    (e : M.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))).obj E) :
    ((sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1})).obj M).over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
          AddCommGrpCat.{u + 1}).obj E) := by
  have : (Y.smallEtaleTopology.over U).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1}) := by
    apply GrothendieckTopology.instPreservesSheafification
  exact (sheafCompose (Y.smallEtaleTopology.over U)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).mapIso e ≪≫
    (constantCommuteCompose (Y.smallEtaleTopology.over U)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1})).app E

/-- For cyclic coefficients, finite abelian local systems are exactly the module sheaves
admitting trivializations with finite constant values.
Source: Stacks Project, Definitions 03RU and 03RW(2),(3); the constant-stalk argument in
lem-weil-pbc-constructible-torsion-modules-agree, proof steps 4--6.
(blueprint: lem-weil-pbc-finite-local-cyclic-module-forget)

Proof: In the forward direction forget every finite module trivialization. Constants commute
with forgetting. Lift any geometric point through the etale cover and identify its stalk
with the finite constant value; this gives finite abelian stalks. Conversely discard empty
members of an abelian trivializing cover. The constant abelian value on a remaining member
is its stalk at a geometric point, hence finite and annihilated by n. Give it its canonical
Z/n-action and lift the scalars to ULift (ZMod n). Constants commute with forgetting, and
additive maps between cyclic modules are linear, so the abelian trivialization lifts to a
module trivialization. These lifts supply both the LocallyConstantDatum and its finite
values. Empty cover members must be discarded: constancy on an empty scheme implies
neither finiteness nor annihilation of the chosen constant value. For n = 1 all modules are
zero and the same argument applies; the empty base uses the empty cover.
-/
theorem finite_local_cyclic_module_forget_iff {Y : Scheme.{u}}
    (n : ℕ) [NeZero n]
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) :
    let G := (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})).obj M
    (IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G)) ↔
    ∃ d : LocallyConstantDatum M, ∀ i : d.cover.I₀,
      ∃ A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)), Finite A ∧
        Nonempty ((M.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))).obj A) := by
  classical
  dsimp only
  let V := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
    AddCommGrpCat.{u + 1}
  let G := (sheafCompose Y.smallEtaleTopology V).obj M
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  constructor
  · rintro ⟨hlocal, hfinite⟩
    obtain ⟨d₀⟩ := hlocal.nonempty_locallyConstantDatum
    let 𝒰 : Cover.{u} etalePrecoverage Y :=
      { I₀ := { i : d₀.cover.I₀ // Nonempty (d₀.cover.X i) }
        X i := d₀.cover.X i.1
        f i := d₀.cover.f i.1
        mem₀ := by
          refine (presieve₀_mem_precoverage_iff _).mpr
            ⟨fun x ↦ ?_, fun i ↦ d₀.cover.map_prop i.1⟩
          obtain ⟨i, y, hy⟩ := d₀.cover.exists_eq x
          exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩ }
    have hconstant (i : 𝒰.I₀) : (M.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) := by
      apply cyclic_module_isConstant_of_forget n
      exact d₀.isConstant i.1
    let d : LocallyConstantDatum M := ⟨𝒰, hconstant⟩
    refine ⟨d, fun i ↦ ?_⟩
    have := hconstant i
    obtain ⟨E, ⟨e⟩⟩ :=
      (M.over (𝒰.etalePrecoverageToEtale i)).mem_essImage_of_isConstant
    let U := 𝒰.etalePrecoverageToEtale i
    have : Nonempty U.left := i.2
    let x : U.left := Classical.arbitrary _
    let Ω := AlgebraicClosure (U.left.residueField x)
    let s : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).2
      ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
    let eStalk := abelianConstantValueStalkIso G U (V.obj E)
      (forgetConstantValueIso n M U E e.symm) s
    have : Finite (((pointSmallEtale (s ≫ U.hom)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G) := hfinite Ω (s ≫ U.hom)
    have hE : Finite E := Finite.of_equiv _ eStalk.addCommGroupIsoToAddEquiv.toEquiv
    exact ⟨E, hE, ⟨e.symm⟩⟩
  · rintro ⟨d, hd⟩
    have hconstant (i : d.cover.I₀) :
        (G.over (d.cover.etalePrecoverageToEtale i)).IsConstant
          (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i)) := by
      obtain ⟨E, -, ⟨e⟩⟩ := hd i
      exact Sheaf.isConstant_of_iso _
        (forgetConstantValueIso n M (d.cover.etalePrecoverageToEtale i) E e)
    refine ⟨⟨⟨⟨d.cover, hconstant⟩⟩⟩, ?_⟩
    intro Ω _ _ s
    obtain ⟨i, x, hx⟩ := d.cover.exists_eq (s default)
    have : Etale (d.cover.f i) := d.cover.map_prop i
    obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (d.cover.f i) s x hx
    obtain ⟨E, hE, ⟨e⟩⟩ := hd i
    have : Finite E := hE
    let eStalk := abelianConstantValueStalkIso G (d.cover.etalePrecoverageToEtale i)
      (V.obj E) (forgetConstantValueIso n M (d.cover.etalePrecoverageToEtale i) E e) t
    have hfin : Finite (((pointSmallEtale (t ≫ d.cover.f i)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G) :=
      Finite.of_equiv E eStalk.addCommGroupIsoToAddEquiv.toEquiv.symm
    simpa only [ht] using hfin

end AlgebraicGeometry.Scheme
