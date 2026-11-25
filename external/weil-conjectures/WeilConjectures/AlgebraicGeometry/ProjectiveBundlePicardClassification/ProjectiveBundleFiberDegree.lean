/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleFiberTwistModel
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.StandardUnitCocycleNormalization
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line.LineInvertibleClassification
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistGenerator
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Degrees of invertible modules on projective-bundle fibres

## References

* Stacks Project, Tag 0BXJ
* EGA II, Remark 4.2.7
* EGA II, Remark 4.2.7, field calculation
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

private theorem standard_chart_frame (k : Type u) [Field k]
    (r : ℕ) (L : ℙ(ULift.{u} (Fin r); Spec (.of k)).Modules) [L.IsInvertible]
    (i : ULift.{u} (Fin r)) :
    ∃ g : Γ(L, ProjectiveSpace.standardOpen _ (Spec (.of k)) i), IsFreeGenerator g := by
  let U := ProjectiveSpace.standardOpen (ULift.{u} (Fin r)) (Spec (.of k)) i
  let e := ProjectiveSpace.chartRingEquiv (ULift.{u} (Fin r)) k i
  have : IsDomain Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), U) :=
    e.symm.toMulEquiv.isDomain _
  have : UniqueFactorizationMonoid Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), U) :=
    e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have : IsGCDMonoid Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), U) :=
    ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  have hU := ProjectiveSpace.isAffineOpen_standardOpen (ULift.{u} (Fin r)) (Spec (.of k)) i
  have := invertible_sections_of_isAffineOpen L hU
  obtain ⟨f⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), U) Γ(L, U))
  refine ⟨f.symm 1, isFreeGenerator_of_bijective_smul L hU ?_⟩
  convert f.symm.bijective using 1
  funext a
  rw [← f.symm.map_smul, smul_eq_mul, mul_one]

private theorem exists_standard_degree (k : Type u) [Field k] (r : ℕ) (hr : 2 ≤ r)
    (L : ℙ(ULift.{u} (Fin r); Spec (.of k)).Modules) [L.IsInvertible] :
    ∃ d : ℤ, Nonempty (L ≅ ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) d) := by
  classical
  by_cases hr2 : r = 2
  · subst r
    exact (ProjectiveLine.existsUnique_degree_of_isInvertible k
      (ProjectiveSpace.twist _ _) (fun d ↦ ⟨ProjectiveLine.twistData _ d⟩) L).exists
  have hr3 : 3 ≤ r := by omega
  let N := ULift.{u} (Fin r)
  let S := Spec (.of k)
  let X := ℙ(N; S)
  let U := ProjectiveSpace.standardOpen N S
  obtain ⟨g, hg⟩ : ∃ g : ∀ i : N, Γ(L, U i), ∀ i, IsFreeGenerator (g i) := by
    choose g hg using standard_chart_frame k r L
    exact ⟨g, hg⟩
  choose t ht using fun i j : N ↦
    ((hg j).map (inf_le_right : U i ⊓ U j ≤ U j)).exists_unit_smul_eq
      ((hg i).map (inf_le_left : U i ⊓ U j ≤ U i))
  have htrans (i j : N) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
      L.presheaf.map (homOfLE hi).op (g i) =
        X.presheaf.map (homOfLE (le_inf hi hj)).op (t i j).val •
          L.presheaf.map (homOfLE hj).op (g j) := by
    have h := congrArg (L.presheaf.map (homOfLE (le_inf hi hj)).op) (ht i j)
    simpa only [Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE] using h
  have hc (i j l : N) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j)
      (hl : W ≤ U l) :
      X.presheaf.map (homOfLE (le_inf hi hj)).op (t i j).val *
        X.presheaf.map (homOfLE (le_inf hj hl)).op (t j l).val =
        X.presheaf.map (homOfLE (le_inf hi hl)).op (t i l).val := by
    apply ((hg l).map hl).smul_left_injective
    dsimp only
    rw [mul_smul, ← htrans j l W hj hl, ← htrans i j W hi hj,
      ← htrans i l W hi hl]
  obtain ⟨d, a, ha⟩ := ProjectiveSpace.exists_standardUnitCocycle_normalization k r hr3 t hc
  let f (i : N) : Γ(L, U i) := (a i).val • g i
  have hf (i : N) : IsFreeGenerator (f i) := (hg i).units_smul (a i)
  have hftrans (i j : N) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
      L.presheaf.map (homOfLE hi).op (f i) =
        X.presheaf.map (homOfLE (le_inf hi hj)).op
            (ProjectiveSpace.transitionUnit N S d i j).val •
          L.presheaf.map (homOfLE hj).op (f j) := by
    have ha' : X.presheaf.map (homOfLE inf_le_left).op (a i).val * (t i j).val =
        (ProjectiveSpace.transitionUnit N S d i j).val *
          X.presheaf.map (homOfLE inf_le_right).op (a j).val := ha i j
    have h := congrArg (X.presheaf.map (homOfLE (le_inf hi hj)).op) ha'
    rw [map_mul, map_mul, Scheme.presheaf_map_map_apply,
      Scheme.presheaf_map_map_apply] at h
    dsimp only [f]
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, htrans i j W hi hj, smul_smul, smul_smul]
    exact congrArg (fun b ↦ b • L.presheaf.map (homOfLE hj).op (g j)) h
  let T := ProjectiveSpace.twist N S d
  have httrans (i j : N) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
      T.presheaf.map (homOfLE hi).op (ProjectiveSpace.twistGenerator N S d i) =
        X.presheaf.map (homOfLE (le_inf hi hj)).op
            (ProjectiveSpace.transitionUnit N S d i j).val •
          T.presheaf.map (homOfLE hj).op (ProjectiveSpace.twistGenerator N S d j) := by
    have h' : T.presheaf.map (homOfLE inf_le_left).op
          (ProjectiveSpace.twistGenerator N S d i) =
        (ProjectiveSpace.transitionUnit N S d i j).val •
          T.presheaf.map (homOfLE inf_le_right).op
            (ProjectiveSpace.twistGenerator N S d j) :=
      ProjectiveSpace.map_twistGenerator_eq_transitionUnit_smul N S d i j
    have h := congrArg (T.presheaf.map (homOfLE (le_inf hi hj)).op) h'
    rw [Scheme.Modules.map_smul, Scheme.Modules.presheaf_map_map_apply,
      Scheme.Modules.presheaf_map_map_apply] at h
    exact h
  refine ⟨d, ⟨isoOfIsFreeGenerator (ProjectiveSpace.iSup_standardOpen N S) hf
    (ProjectiveSpace.isFreeGenerator_twistGenerator N S d) ?_⟩⟩
  intro i j W hi hj b c hbc
  rw [hftrans i j W hi hj, smul_smul] at hbc
  rw [httrans i j W hi hj, smul_smul, ((hf j).map hj).smul_left_injective hbc]

private theorem standard_twist_degree_le (k : Type u) [Field k] (r : ℕ) (hr : 2 ≤ r)
    (a b : ℤ)
    (e : ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) a ≅
      ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) b) : a ≤ b := by
  classical
  let N := ULift.{u} (Fin r)
  let S := Spec (.of k)
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  have : Nontrivial N := inferInstance
  by_contra hab
  have hneg : b - a < 0 := by omega
  obtain ⟨ea⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso N S (-a) a
  obtain ⟨eb⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso N S (-a) b
  have ez : ProjectiveSpace.twist N S 0 ≅ ProjectiveSpace.twist N S (b - a) := by
    simpa only [neg_add_cancel, sub_eq_add_neg, add_comm (-a) b] using
      (ea.symm ≪≫ (Iso.refl _ ⊗ᵢ e) ≪≫ eb)
  have := ProjectiveSpace.subsingleton_H_zero_twist_of_neg (n := N) k hneg
  have := subsingleton_H_of_iso ez.symm 0
  obtain ⟨c⟩ := ProjectiveSpace.nonempty_H_zero_twist_equiv N k (r - 1) (by simp [N]; omega) 0
  have : Subsingleton (MvPolynomial.homogeneousSubmodule N k 0) := c.toEquiv.symm.subsingleton
  have h := Subsingleton.elim
    (⟨1, MvPolynomial.isHomogeneous_one N k⟩ : MvPolynomial.homogeneousSubmodule N k 0) 0
  exact one_ne_zero (congrArg Subtype.val h)

private theorem line_power_to_twist {X : Scheme.{u}} (k : Type u) [Field k]
    (r : ℕ) (g : ℙ(ULift.{u} (Fin r); Spec (.of k)) ⟶ X)
    (A : X.Modules) (hA : A.IsInvertible)
    (h : (tensorPullback g).obj A ≅
      ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) 1) (m : ℤ) :
    Nonempty ((tensorPullback g).obj (integerLinePower A hA m) ≅
      ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) m) := by
  classical
  let N := ULift.{u} (Fin r)
  let S := Spec (.of k)
  let F := tensorPullback g
  let e := lineTensorInverse A hA
  let e' := lineTensorInverse (ProjectiveSpace.twist N S 1) inferInstance
  let unitIso : F.obj (𝟙_ X.Modules) ≅ 𝟙_ ℙ(N; S).Modules :=
    ((tensorPullbackSectionAdjunction g).leftAdjointUniq
      (pullbackPushforwardAdjunction g)).app _ ≪≫ pullbackObjUnitIso g
  obtain ⟨t, _⟩ := module_pullback_tensor g
  obtain ⟨tinv⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso N S 1 (-1)
  have tinv' : ProjectiveSpace.twist N S 1 ⊗ ProjectiveSpace.twist N S (-1) ≅
      𝟙_ ℙ(N; S).Modules := by
    exact tinv ≪≫ (ProjectiveSpace.unitIsoTwistZero N S).symm
  let dualIso : F.obj e.obj ≅ ProjectiveSpace.twist N S (-1) :=
    e'.fullyFaithfulTensorLeft.preimageIso
      ((h.symm ⊗ᵢ Iso.refl _) ≪≫ (t A e.obj).symm ≪≫ F.mapIso e.rightIso ≪≫
        unitIso ≪≫ tinv'.symm)
  have natPower (B : X.Modules) (q : ℤ)
      (hB : F.obj B ≅ ProjectiveSpace.twist N S q) (n : ℕ) :
      Nonempty (F.obj (tensorPowNat B n) ≅ ProjectiveSpace.twist N S (q * n)) := by
    induction n with
    | zero => simpa only [Nat.cast_zero, mul_zero] using
        (⟨unitIso ≪≫ ProjectiveSpace.unitIsoTwistZero N S⟩ :
          Nonempty (F.obj (tensorPowNat B 0) ≅ ProjectiveSpace.twist N S 0))
    | succ n ih =>
      obtain ⟨v⟩ := ih
      obtain ⟨w⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso N S q (q * n)
      exact ⟨t B _ ≪≫ (hB ⊗ᵢ v) ≪≫ w ≪≫
        eqToIso (congrArg (ProjectiveSpace.twist N S) (by push_cast; ring))⟩
  cases m with
  | ofNat n =>
    change Nonempty (F.obj (tensorPowNat A n) ≅ ProjectiveSpace.twist N S (n : ℤ))
    simpa only [one_mul] using natPower A 1 h n
  | negSucc n =>
    change Nonempty (F.obj (tensorPowNat e.obj (n + 1)) ≅
      ProjectiveSpace.twist N S (Int.negSucc n))
    simpa only [Int.negSucc_eq, neg_mul, one_mul, Nat.cast_add, Nat.cast_one] using
      natPower e.obj (-1) dualIso (n + 1)

/-- A line has a unique integer degree on each residue-field fibre. This assertion
only concerns modules on the fibre, and asserts no extension to a neighbourhood. -/
theorem projective_bundle_fiber_degree (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (D : TautologicalQuotient E)
    (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (hL : L.IsInvertible) (s : S) :
    ∃! m : ℤ, Nonempty
      ((tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj L ≅
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj
          (integerLinePower D.line D.invertible m)) := by
  obtain ⟨e, ⟨he⟩⟩ := exists_projective_bundle_fiber_twist_model S E r hr D s
  let f := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s
  let M := (tensorPullback f).obj L
  have hinv {X Y : Scheme.{u}} (g : X ⟶ Y) (A : Y.Modules) (hA : A.IsInvertible) :
      ((tensorPullback g).obj A).IsInvertible := by
    have : A.IsInvertible := hA
    let c := (tensorPullbackSectionAdjunction g).leftAdjointUniq
      (pullbackPushforwardAdjunction g)
    exact IsInvertible.of_iso (c.app A).symm
  have : M.IsInvertible := hinv f L hL
  have : ((tensorPullback e.hom).obj M).IsInvertible := hinv e.hom M inferInstance
  obtain ⟨m, ⟨v⟩⟩ := exists_standard_degree (S.residueField s) r hr
    ((tensorPullback e.hom).obj M)
  have hp (m : ℤ) : Nonempty
      ((tensorPullback e.hom).obj
        ((tensorPullback f).obj (integerLinePower D.line D.invertible m)) ≅
          ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of (S.residueField s))) m) := by
    have h : (tensorPullback (e.hom ≫ f)).obj D.line ≅
        ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of (S.residueField s))) 1 :=
      (tensorPullbackSectionComp e.hom f).app D.line ≪≫ he
    obtain ⟨t⟩ := line_power_to_twist (S.residueField s) r (e.hom ≫ f) D.line D.invertible h m
    exact ⟨((tensorPullbackSectionComp e.hom f).app _).symm ≪≫ t⟩
  obtain ⟨tm⟩ := hp m
  let c : 𝟭 ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiber s).Modules ≅
      tensorPullback e.hom ⋙ tensorPullback e.inv :=
    (tensorPullbackSectionId _).symm ≪≫
      eqToIso (congrArg (fun g ↦ tensorPullback g) e.inv_hom_id.symm) ≪≫
        tensorPullbackSectionComp e.inv e.hom
  refine ⟨m, ⟨c.app M ≪≫ (tensorPullback e.inv).mapIso (v ≪≫ tm.symm) ≪≫
    (c.app ((tensorPullback f).obj (integerLinePower D.line D.invertible m))).symm⟩, ?_⟩
  rintro n ⟨w⟩
  obtain ⟨tn⟩ := hp n
  let z := v.symm ≪≫ (tensorPullback e.hom).mapIso w ≪≫ tn
  exact le_antisymm
    (standard_twist_degree_le (S.residueField s) r hr n m z.symm)
    (standard_twist_degree_le (S.residueField s) r hr m n z)

end AlgebraicGeometry.ProjectiveBundlePicardClassification
