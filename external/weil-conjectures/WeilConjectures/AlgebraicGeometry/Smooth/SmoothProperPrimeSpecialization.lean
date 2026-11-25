/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantTorsionLocalAcyclicity
import WeilConjectures.AlgebraicGeometry.Proper.ProperLocallyAcyclicSpecialization
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothLocalAcyclicity

/-!
# Prime-to-characteristic specialization for smooth proper morphisms

Source: Stacks Project, Tag 0GKD, lemma-sp-isom-proper-loc-cst-torsion.
(blueprint: lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Restrict a geometric germ through the strict localization and then take its germ
at `t`. The first arrow is the uniquely characterized pointed-neighbourhood restriction;
the last arrow is the canonical inverse-image stalk comparison. Thus this is the
specified specialization map, with target at the composite point on `S`.
Source: Stacks Project, Tag 0GKD and the specialization construction preceding Tag 0GJW.
(blueprint: lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic). -/
noncomputable def strictLocalSpecialization
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale s).sheafFiber.obj G ⟶
      (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.obj
        G :=
  Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G) ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s))
        (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
        Over.mkIdTerminal)).hom.app _ ≫
    (Scheme.pointSmallEtale t).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
      (Over.homMk t (by simp))
      ((upperStar AddCommGrpCat.{u + 1} (Scheme.strictHenselizationStructuralMap s)).obj G).obj ≫
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (Scheme.strictHenselizationStructuralMap s) t).hom.app G

/-- Prime-to-characteristic specialization invariance, with no finite-stalk or
relative-dimension condition. Higher direct images here are formed after forgetting
scalars to abelian sheaves, as allowed in the node.
Source: Stacks Project, Tag 0GKD, degree-q consequence.
(blueprint: lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic).

Proof: forgetting scalars makes F a locally constant abelian sheaf, killed by the
prime ell. Since ell is a unit in each local ring of S, it remains a unit in every
residue field of X, so the torsion orders are prime to residue characteristic.
The smooth-local-acyclicity lemma gives universal local acyclicity, hence local
acyclicity. The locally-constant-torsion-local-acyclicity lemma gives local acyclicity
relative to this underlying sheaf. Apply proper-locally-acyclic-specialization in
degree q to obtain invertibility of the pointed-neighbourhood restriction map.
If direct images are interpreted in module sheaves, the module/abelian derived
direct-image comparison commutes with cohomology and geometric germs and transports
this assertion to the module specialization map; its bijective inverse is linear. -/
theorem isIso_strictLocalSpecialization_smooth_proper_prime
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f]
    (ell : ℕ) [Fact ell.Prime]
    (hunit : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))))
    [Scheme.IsLocallyConstantSheaf F]
    (q : ℕ) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso (strictLocalSpecialization s t
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))
                AddCommGrpCat.{u + 1})).obj F))))) := by
  let R := ULift.{u + 1} (ZMod ell)
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let G := (sheafCompose X.smallEtaleTopology U).obj F
  have hkill (M : ModuleCat.{u + 1} R) (m : M) : ell • m = 0 := by
    rw [← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero R ell, zero_smul]
  have : Scheme.IsLocallyConstantSheaf G := by
    obtain ⟨d⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    refine ⟨⟨⟨d.cover, fun i ↦ ?_⟩⟩⟩
    let := d.isConstant i
    have : GrothendieckTopology.PreservesSheafification
        (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i)) U :=
      GrothendieckTopology.instPreservesSheafification _ _
    change ((sheafCompose (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
      U).obj (F.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
    infer_instance
  have hG : G.IsTorsion := by
    refine Sheaf.IsTorsion.of_forall_isAddTorsion fun V m ↦ ?_
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨ell, (Fact.out : ell.Prime).pos, hkill (F.obj.obj V) m⟩
  have hf : IsLocallyAcyclicRelative f G := by
    apply isLocallyAcyclicRelative_of_locallyConstant_torsion f (smooth_localAcyclicity f).2
    intro K _ _ x m
    have : LocallySmall.{u} X.Etale := locallySmall_self _
    have : PreservesFilteredColimitsOfSize.{u, u} U :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let e := ((Scheme.pointSmallEtale x).sheafFiberCompIso U).app F
    have hm : ell • m = 0 := by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      simpa only [map_nsmul, map_zero] using
        hkill (((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)).obj F)
          (e.hom m)
    refine ⟨isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨ell, (Fact.out : ell.Prime).pos, hm⟩, ?_⟩
    by_cases hc : ringChar (X.residueField (x default)) = 0
    · exact Or.inl hc
    · apply Or.inr
      have hu : IsUnit (ell : X.residueField (x default)) := by
        simpa only [map_natCast] using
          (hunit (f (x default))).map
            ((X.residue (x default)).hom.comp (f.stalkMap (x default)).hom)
      have hp : ell.Coprime (ringChar (X.residueField (x default))) :=
        (Fact.out : ell.Prime).coprime_iff_not_dvd.mpr
          ((isUnit_iff_not_dvd_char_of_ringChar_ne_zero _ ell hc).mp hu)
      exact hp.of_dvd_left (addOrderOf_dvd_of_nsmul_eq_zero hm)
  have hsp := isIso_etaleStalkSpecialization_of_proper_locallyAcyclic f G hG hf q s t
  exact hsp

end AlgebraicGeometry.Etale
