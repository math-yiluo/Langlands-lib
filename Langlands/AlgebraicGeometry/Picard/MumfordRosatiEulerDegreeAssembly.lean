import Langlands.AlgebraicGeometry.Picard.MumfordProductMultiplicationTwist
import Langlands.AlgebraicGeometry.Picard.MumfordMapPicardClass
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordMapIsogeny
import Langlands.AlgebraicGeometry.Picard.AmplePowerTwistProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence
import Langlands.AlgebraicGeometry.Modules.SmoothProperLineBundleFiniteCohomologyProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Degrees of `n • λ + f^∨ λ f` from the Euler-characteristic square formula -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme.MumfordPicardClass

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AbelianScheme.Rosati

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The line bundle `L ^ n`, with carrier the iterated tensor power `tensorPow L.obj n`. -/
abbrev powLineBundle {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) : LineBundle X :=
  Langlands.AbelianScheme.MultiplicationTwist.powLB L n

set_option synthInstance.maxHeartbeats 1000000 in
lemma classOf_powLineBundle {X : Scheme.{u}}
    (preservation : pullbackTensorComparisonIsIsoStatement.{u}) (L : LineBundle X) (n : ℕ) :
    (powLineBundle L n).classOf = n • L.classOf := by
  induction n with
  | zero =>
    rw [zero_smul, ← LineBundle.classOf_trivial X]
    exact (LineBundle.classOf_eq_iff _ _).2 ⟨Iso.refl _⟩
  | succ n ih =>
    have h : (powLineBundle L (n + 1)).classOf =
        (LineBundle.tensor preservation L (powLineBundle L n)).classOf := rfl
    rw [h, LineBundle.classOf_tensor, ih, succ_nsmul']

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The content of `MumfordEulerDegreeStatement` for explicit data: for all large `n`,
`n • lam + f ≫ lam ≫ f^∨` is an isogeny whose degree is the square of the Euler characteristic
of `f^* L ⊗ L ^ n`. -/
theorem eulerDegree (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (lam : A ⟶ W.dual P)
    (L : LineBundle A.X.left)
    (B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj)
      B.obj ≅ structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize P.preservation A.X.hom (unitSection A)
        (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅
          structureSheaf A.X.left)
    (hL : L.IsAmple)
    (hlam : (groupHom lam).hom.hom =
      mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
        P.square W.hasDual)
    (f : A ⟶ A) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsIsogeny (n • lam + (f ≫ lam ≫
        dualAbelianSchemeMapFromEvaluation W.hasDual W.geometry P.preservation
          W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
          P.associativity P.comparison P.symmetry W.hasDual W.geometry W.inversePoincare
          W.evaluation f : A ⟶ W.dual P)) ∧
      ∀ y : (W.dual P).X.left,
        ((hom (n • lam + (f ≫ lam ≫
          dualAbelianSchemeMapFromEvaluation W.hasDual W.geometry P.preservation
            W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
            P.associativity P.comparison P.symmetry W.hasDual W.geometry W.inversePoincare
            W.evaluation f : A ⟶ W.dual P))).finrank y : ℚ) =
          coherentEulerSequence A.X.hom ((LineBundle.pullback (hom f)).obj L).obj
            (hasFiniteAffineSections_lineBundle _) L n ^ 2 := by
  let fL : LineBundle A.X.left := (LineBundle.pullback (hom f)).obj L
  obtain ⟨b₀, hb₀⟩ := amplePowerTwist A.X.left L fL hL
  refine ⟨b₀, fun n hn => ?_⟩
  let D := dualAbelianSchemeMapFromEvaluation W.hasDual W.geometry P.preservation
    W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry W.hasDual W.geometry W.inversePoincare
    W.evaluation f
  let ψ : A ⟶ W.dual P := n • lam + (f ≫ lam ≫ D : A ⟶ W.dual P)
  let L' : LineBundle A.X.left := LineBundle.tensor P.preservation fL (powLineBundle L n)
  have hL' : L'.IsAmple := hb₀ n hn L' ⟨Iso.refl _⟩
  -- an explicit Mumford presentation of `L'`
  obtain ⟨t⟩ := fieldLineBundleTriviality k ((LineBundle.pullback (unitSection A)).obj L')
  let B' : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) := LineBundle.trivial _
  let evB' : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L'.obj) B'.obj ≅
      structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    tensorRightUnitor _ ≪≫ t
  obtain ⟨M', ⟨ev'⟩⟩ := ((RigidifiedLineBundle.forget (unitSection A)).obj
    (LineBundle.normalize P.preservation A.X.hom (unitSection A) (unitSection_comp A) L' B'
      evB')).exists_tensorObj_iso_structureSheaf
  -- the homomorphism is the Mumford map of `L'`
  have hD : (groupHom D).hom.hom = dualSchemeMap homPicardZeroPullback f W.hasDual W.hasDual :=
    Over.OverMorphism.ext (dualAbelianSchemeMapFromEvaluation_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f)
  have hcomp : (groupHom (f ≫ lam ≫ D : A ⟶ W.dual P)).hom.hom =
      (groupHom f).hom.hom ≫ (groupHom lam).hom.hom ≫ (groupHom D).hom.hom := rfl
  have heq : (groupHom ψ).hom.hom = mumfordSchemeMapOfLineBundle P.preservation A L' B' evB'
      M' ev' P.square W.hasDual := by
    apply pointClass_injective P A W
    rw [hom_add_eq_mul, hom_nsmul_eq_pow, pointClass_mul, pointClass_pow, hcomp, hD, hlam,
      pointClass_comp_mumford_comp_dual, pointClass_mumfordSchemeMapOfLineBundle,
      pointClass_mumfordSchemeMapOfLineBundle, classOf_mumfordFamily P k A,
      classOf_mumfordFamily P k A]
    have hcl : L'.classOf = fL.classOf + n • L.classOf := by
      rw [LineBundle.classOf_tensor, classOf_powLineBundle P.preservation]
    rw [hcl]
    simp only [map_add, map_nsmul]
    have key : ∀ {G : Type (u + 1)} [AddCommGroup G] (a b c a' b' c' : G) (m : ℕ),
        m • (a - b - c) + (a' - b' - c') = (a' + m • a) - (b' + m • b) - (c' + m • c) := by
      intros
      simp only [smul_sub]
      abel
    exact key _ _ _ _ _ _ n
  have hiso : IsIsogeny ψ :=
    AmpleMumfordIsogeny.isIsogeny P k A W ψ L' B' evB' M' ev' hL' heq
  refine ⟨hiso, fun y => ?_⟩
  have hfc : HasFiniteCohomology A.X.hom L'.obj :=
    smoothProperLineBundleFiniteCohomology k A.X.left A.X.hom inferInstance inferInstance L'
  have hsq := algClosedFieldAmpleMumfordEulerSquare P.preservation P.square k A W.hasDual L' hL'
    hfc B' evB' M' ev' (groupHom ψ).hom.hom heq hiso.1 hiso.2.1 y
  have hcs : coherentEulerSequence A.X.hom fL.obj (hasFiniteAffineSections_lineBundle _) L n =
      ((eulerCharacteristic A.X.hom L'.obj hfc : ℤ) : ℚ) := rfl
  rw [hcs]
  exact_mod_cast hsq.symm

end Langlands.AbelianScheme.MumfordPicardClass
