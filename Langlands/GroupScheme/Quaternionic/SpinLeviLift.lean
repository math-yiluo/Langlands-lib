import Langlands.GroupScheme.Quaternionic.SpinKernelAssembly
import Langlands.GroupScheme.Quaternionic.BinaryQuaternionSpinLift

/-!
# Levi lifts into a quaternionic spin cover from simple connectedness of `SL₁`

Assuming `CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`, the binary lifts
`BinarySpinLift.scalar` and `BinarySpinLift.normOne` lift the Levi morphism `leviHom h`
(`IsLeviLift`). Hence that statement implies `SpinKernel.SpinLeviLiftStatement`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite Langlands.CentralSimple
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

open LeviScheme

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D]

/-- The all-test coordinate of the affine `𝔾_m` point `t` is `t` transported along the
inverse section isomorphism. -/
theorem gm_pointsEquiv_gmPoint (A : CommAlgCat.{u} (CommRingCat.of K)) (t : Aˣ) :
    Gm.pointsEquiv (Spec (CommRingCat.of K)) ((algSpec (CommRingCat.of K)).obj (op A))
        (gmPoint A t) =
      Units.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom t := by
  apply Units.ext
  have hx : (Gm.affineUnitsEquiv (CommRingCat.of K) A (gmPoint A t) : A) = t := by
    simp only [gmPoint, MulEquiv.apply_symm_apply]
  have hv : (Gm.affineUnitsEquiv (CommRingCat.of K) A (gmPoint A t) : A) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (Gm.pointsEquiv (Spec (CommRingCat.of K)) ((algSpec (CommRingCat.of K)).obj (op A))
          (gmPoint A t)).val := rfl
  rw [Units.coe_map]
  change _ = (Corepresented.affineSectionsIso A).inv.hom.toRingHom (t : A)
  rw [Corepresented.affineSectionsIso_inv_ringHom, ← hx, hv]
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) _).symm

omit [Algebra.IsCentral K D] in
/-- The all-test coordinate of the affine `GL₁(D)` point `a`. -/
theorem pointsEquiv_unitPoint (A : CommAlgCat.{u} (CommRingCat.of K)) (a : (A ⊗[K] D)ˣ) :
    FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) _ (unitPoint A a) =
      Units.map (Algebra.TensorProduct.map (Corepresented.affineSectionsIso A).inv.hom
        (AlgHom.id K D)).toMonoidHom a := by
  rw [pointsEquiv_affine]
  simp only [unitPoint, MulEquiv.apply_symm_apply]

variable [Infinite K] (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- The binary norm-one lift agrees with the Levi morphism on every relative test point. -/
theorem normOne_comp_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (CentralSimpleUnits.normOne K D).X) :
    (x ≫ (BinarySpinLift.normOne σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom =
      (x ≫ (CentralSimpleUnits.normOneι K D).hom.hom) ≫ (leviHom h).hom.hom := by
  have : Mono (σ.isometryGroupι q).hom.hom := (σ.isClosedSubgroup_isometryGroupι q).mono_overHom
  apply (cancel_mono (σ.isometryGroupι q).hom.hom).mp
  apply (HyperbolicScheme.matrixPointsEquiv n T).injective
  rw [BinarySpinLift.normOne_levi_points, leviHom_points]
  rfl

/-- **Levi lifts.** Under the degree-two simple-connectedness premise, the binary scalar and
norm-one lifts into the spin cover lift the Levi morphism of `h`. -/
theorem isLeviLift_binarySpinLift :
    IsLeviLift h π (BinarySpinLift.scalar σ hdim hsym h hπ hsc)
      (BinarySpinLift.normOne σ hdim hsym h hπ hsc) := by
  have : Mono (σ.isometryGroupι q).hom.hom := (σ.isClosedSubgroup_isometryGroupι q).mono_overHom
  constructor
  · intro A t
    apply (cancel_mono (σ.isometryGroupι q).hom.hom).mp
    apply (HyperbolicScheme.matrixPointsEquiv n _).injective
    rw [BinarySpinLift.scalar_points, unitMap_apply, leviHom_points, pointsEquiv_unitPoint,
      gm_pointsEquiv_gmPoint, normCoverScalarUnits_map]
  · apply Grp.hom_ext
    have hx := normOne_comp_points σ hdim hsym h hπ hsc _
      (𝟙 (CentralSimpleUnits.normOne K D).X)
    simp only [Category.id_comp] at hx
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom, hx]

end Langlands.GroupScheme.Quaternionic.SpinKernel

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

/-- **Levi-lift statement from simple connectedness of `SL₁`.** The degree-two norm-one
simple-connectedness statement implies `SpinLeviLiftStatement`. -/
theorem spinLeviLift_of_degreeTwoNormOneSimplyConnected
    (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u}) :
    SpinLeviLiftStatement.{u} := by
  intro K _ _ _ _ D _ _ _ _ hD σ hsym m hm q hq hw S π hπ e f h
  have : Infinite K := Langlands.LocalField.infinite_of_isNonarchimedeanLocalField K
  exact ⟨_, _, isLeviLift_binarySpinLift σ hD hsym h hπ hsc⟩

end Langlands.GroupScheme.Quaternionic.SpinKernel
