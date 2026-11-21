import Langlands.GroupScheme.OrthogonalMatrix.SplitCoverKernelDegree
import Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryProof
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.CentralIsogeny.GaloisLiftScalarExtension
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # The geometric kernel of a scalar even spin cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

private def kernelPointsEquiv_postcompIso {S : Scheme.{u}} {G H J : GroupScheme S}
    (p : G ⟶ H) (e : H ≅ J) (T : Over S) :
    (T ⟶ (kernel p).X) ≃ (T ⟶ (kernel (p ≫ e.hom)).X) :=
  (kernelPointsEquiv p T).toEquiv.trans (by
    refine (Equiv.subtypeEquivRight (fun x => ?_)).trans (kernelPointsEquiv (p ≫ e.hom) T).symm.toEquiv
    change x ≫ p.hom.hom = 1 ↔ x ≫ (p ≫ e.hom).hom.hom = 1
    rw [Grp.comp_hom_hom, ← Category.assoc]
    have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
    rw [← MonObj.one_comp e.hom.hom.hom]
    exact (cancel_mono e.hom.hom.hom).symm)

namespace Quaternionic.FirstKindInvolution

variable {F : Type u} [Field F] [CharZero F] {n : ℕ} [NeZero (2 * n)]
  (q : (scalar F).QuadraticForms (Fin (2 * n)))

local notation "τ" => scalar F
local notation "O" => isometryGroup τ q
local notation "S" => Spec (CommRingCat.of F)

omit [NeZero (2 * n)] in
/-- The simply connected cover of the scalar even orthogonal identity component
has two geometric kernel points in characteristic zero. -/
theorem natCard_scalarEvenSpinKernel [Smooth (O).X.hom]
    (hn : 3 ≤ n) (hq : (τ).IsNondegenerateQuadratic q)
    {G : GroupScheme S} (p : G ⟶ identityComponent (O))
    (hG : IsSimplyConnected G) (hp : IsCentralIsogeny p) :
    Nat.card (affinePoints (kernel p) (CommAlgCat.of F (AlgebraicClosure F))) = 2 := by
  let Ω := AlgebraicClosure F
  let b := algebraBaseMap F Ω
  let B := GroupScheme.baseChange b
  let A := CommAlgCat.of Ω Ω
  let T := (algSpec (CommRingCat.of Ω)).obj (op A)
  have hos : Nonempty (B.obj (O) ≅ OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of Ω)) := by
    obtain ⟨M, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact OrthogonalMatrix.nonempty_splittingIso (K := F) (L := Ω) (m := n)
      (by rw [Fintype.card_fin]) M ((isNondegenerateQuadratic_scalar_mk_iff M).mp hq)
  obtain ⟨o⟩ := hos
  let d := IdentityComponent.baseChangeIso (O) (algebraMap F Ω) ≪≫ IdentityComponent.mapIso o
  let r := B.map p ≫ d.hom
  have hr : IsCentralIsogeny r := (hp.baseChange b).comp_iso d
  have hΩ : IsSimplyConnected (B.obj G) := isSimplyConnectedFieldExtension F Ω G hG
  let e := IsCentralIsogeny.scalarExtensionKernelPointsEquiv (F := F) (K := Ω) (M := Ω) (f := p)
  let j := kernelPointsEquiv_postcompIso (B.map p) d T
  have hcard := OrthogonalMatrix.natCard_splitCoverKernel_points hr hΩ (by simpa only [Fintype.card_fin] using hn)
  exact (Nat.card_congr (e.symm.toEquiv.trans j)).trans hcard

/-- The degree-two geometric kernel of the actual scalar even spin cover. -/
def ScalarEvenSpinKernelDegreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (n : ℕ) (q : (scalar F).QuadraticForms (Fin (2 * n)))
    [Smooth ((scalar F).isometryGroup q).X.hom],
    3 ≤ n → (scalar F).IsNondegenerateQuadratic q →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F)))
      (p : G ⟶ identityComponent ((scalar F).isometryGroup q)),
      IsSimplyConnected G → IsCentralIsogeny p →
      Nat.card (affinePoints (kernel p) (CommAlgCat.of F (AlgebraicClosure F))) = 2

end Quaternionic.FirstKindInvolution

end Langlands.GroupScheme
