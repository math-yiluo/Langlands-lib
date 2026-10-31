import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPullbackProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeEquivalence
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality

/-! # Base change of the actual universal smooth-family property -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The geometric-fibre smooth-family condition transports through an actual
isomorphism of the underlying group schemes. -/
lemma isFibrewiseAlgebraicallyTrivialViaSmoothFamily_pullback_groupIso_iff
    {X : Scheme.{u}} (A B : AbelianScheme X) (e : A.toGrp ≅ B.toGrp)
    (L : LineBundle B.X.left) :
    IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A
        ((LineBundle.pullback e.hom.hom.hom.left).obj L) ↔
      IsFibrewiseAlgebraicallyTrivialViaSmoothFamily B L := by
  have fibre_iff (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ X) :
      IsAlgebraicallyTrivialViaSmoothFamily ((baseChange s).obj A)
        (fibreLineBundle A ((LineBundle.pullback e.hom.hom.hom.left).obj L) s) ↔
      IsAlgebraicallyTrivialViaSmoothFamily ((baseChange s).obj B)
        (fibreLineBundle B L s) := by
    let d := (GroupScheme.baseChange s).mapIso e
    have hd : d.hom.hom.hom.left ≫ pullback.fst B.X.hom s =
        pullback.fst A.X.hom s ≫ e.hom.hom.hom.left := by
      change ((Over.pullback s).map e.hom.hom.hom).left ≫ _ = _
      simp
    have hdi : d.inv.hom.hom.left ≫ d.hom.hom.hom.left = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.hom.left) d.inv_hom_id
    let c : (LineBundle.pullback d.hom.hom.hom.left).obj (fibreLineBundle B L s) ≅
        fibreLineBundle A ((LineBundle.pullback e.hom.hom.hom.left).obj L) s :=
      (LineBundle.pullbackComp _ _).app L ≪≫
        eqToIso (congrArg (fun f ↦ (LineBundle.pullback f).obj L) hd) ≪≫
        ((LineBundle.pullbackComp _ _).app L).symm
    constructor
    · intro h
      have h' := isAlgebraicallyTrivialViaSmoothFamily_pullback_hom
        ((baseChange s).obj B) ((baseChange s).obj A) d.inv.hom.hom
        (isAlgebraicallyTrivialViaSmoothFamily_of_iso _ c.symm h)
      refine isAlgebraicallyTrivialViaSmoothFamily_of_iso _ ?_ h'
      exact (LineBundle.pullbackComp _ _).app _ ≪≫
        eqToIso (congrArg (fun f ↦ (LineBundle.pullback f).obj (fibreLineBundle B L s))
          hdi) ≪≫
        (LineBundle.pullbackId _).app _
    · intro h
      exact isAlgebraicallyTrivialViaSmoothFamily_of_iso _ c
        (isAlgebraicallyTrivialViaSmoothFamily_pullback_hom
          ((baseChange s).obj A) ((baseChange s).obj B) d.hom.hom.hom h)
  exact ⟨fun h K _ _ s ↦ (fibre_iff K s).mp (h K s),
    fun h K _ _ s ↦ (fibre_iff K s).mpr (h K s)⟩

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

/-- Actual ground-base pullback preserves and reflects the geometric-fibre
smooth-family condition on rigidified families. -/
theorem isAlgebraicallyTrivialFamilyViaSmoothFamily_familyBaseChange_iff (T : Over S')
    (L : RigidifiedFamily A ((Over.map b).obj T)) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A L ↔
      IsAlgebraicallyTrivialFamilyViaSmoothFamily ((baseChange b).obj A)
        ((familyBaseChange b A T).obj L) :=
  (isFibrewiseAlgebraicallyTrivialViaSmoothFamily_pullback_groupIso_iff
    ((baseChange T.hom).obj ((baseChange b).obj A))
    ((baseChange ((Over.map b).obj T).hom).obj A)
    (familyBaseChangeGroupIso b A T) (familyLineBundle A L)).symm.trans
      (isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_iso _
        (familyBaseChangeLineBundleIso b A T L))

/-- An actual universal smooth-family algebraically trivial family on
quasi-separated tests remains universal on quasi-separated tests after the
explicit simultaneous change of its parameter scheme and ground base. -/
theorem smoothFamilyUniversalBaseChange :
    SmoothFamilyUniversalBaseChangeStatement.{u} := by
  intro S S' b A P L ⟨hL, universal⟩
  refine ⟨?_, ?_⟩
  · exact (isAlgebraicallyTrivialFamilyViaSmoothFamily_familyBaseChange_iff b A
      ((Over.pullback b).obj P) _).mp
      (smoothFamilyPullback S A _ P (baseChangeParameterMap b P) L hL)
  · intro T _ q
    obtain ⟨q, hq⟩ := q
    change ∃! h : T ⟶ (Over.pullback b).obj P, _ = q
    revert hq
    refine Quotient.inductionOn q (fun M hM ↦ ?_)
    change IsAlgebraicallyTrivialFamilyViaSmoothFamily _ M at hM
    change ∃! h : T ⟶ (Over.pullback b).obj P, _ =
      RigidifiedLineBundle.classOf _ _ _ M
    simp only [RigidifiedLineBundle.classifyingMap_eq_iff]
    let F := familyBaseChange b A T
    let G := familyBaseChangeInverse b A T
    let N := G.obj M
    have hN : IsAlgebraicallyTrivialFamilyViaSmoothFamily A N :=
      (isAlgebraicallyTrivialFamilyViaSmoothFamily_familyBaseChange_iff b A T N).mpr
        ((isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_iso _
          ((familyBaseChangeCounitIso b A T).app M)).mpr hM)
    have : QuasiSeparatedSpace ((Over.map b).obj T).left :=
      ‹QuasiSeparatedSpace T.left›
    obtain ⟨g, hg, hguniq⟩ := universal ((Over.map b).obj T)
      ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) N, hN⟩
    obtain ⟨eg⟩ := (RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ L N g).mp hg
    let e := baseChangeParameterEquiv b T P
    have mate : baseChangeParameterMate b (e.symm g) = g := e.apply_symm_apply g
    refine ⟨e.symm g, ?_, ?_⟩
    · refine ⟨(baseChangeFamilyPullbackIso b A (e.symm g)).app L ≪≫
        F.mapIso (?_ ≪≫ eg) ≪≫ (familyBaseChangeCounitIso b A T).app M⟩
      exact eqToIso (congrArg (fun k ↦
        (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) k).obj L) mate)
    · intro k hk
      apply e.injective
      rw [e.apply_symm_apply]
      apply hguniq (e k)
      obtain ⟨ek⟩ := hk
      exact (RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ L N (e k)).mpr
        ⟨((familyBaseChangeUnitIso b A T).app
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A) (e k)).obj L)).symm ≪≫
          G.mapIso (((baseChangeFamilyPullbackIso b A k).app L).symm ≪≫ ek)⟩

end Langlands.AbelianScheme
