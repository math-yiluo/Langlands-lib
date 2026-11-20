import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple
import Langlands.GroupScheme.Reductive.SimpleFactorPresentation
import Langlands.GroupScheme.Reductive.FiniteProductCenter
import Langlands.GroupScheme.Reductive.FiniteProductHomKernel

/-! # The number-field adjoint Hasse kernel reduces to almost-simple groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The number-field finite Galois Hasse kernel for almost-simple adjoint groups. -/
def NumberFieldAlmostSimpleAdjointGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsAdjoint G → IsAlmostSimple G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (Over.mk (algebraBaseMap F L))), ξ.LocallyTrivial → ξ.IsTrivial

set_option backward.isDefEq.respectTransparency false in
/-- Triviality for all almost-simple adjoint groups implies the full adjoint kernel. -/
theorem numberFieldAdjointGaloisHasseKernel_of_almostSimple
    (h : NumberFieldAlmostSimpleAdjointGaloisHasseKernelStatement.{u}) :
    NumberFieldAdjointGaloisHasseKernelStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ hξ
  obtain ⟨I, _, A, p, hsimple, hclosed, _, hp⟩ :=
    SimpleFactor.exists_almostSimplePresentation G hG.isSemisimple
  have hmono (i : I) : Mono (piFactorInclusionHom A i ≫ p).hom.hom := by
    let : IsClosedImmersion (piFactorInclusionHom A i ≫ p).hom.hom.left := hclosed i
    exact Over.mono_of_mono_left _
  let iso : G ≅ pi A :=
    (piHomIso_of_isAdjoint A p (fun i => (hsimple i).isSemisimple) hG hmono hp.surjective).symm
  have hadj (i : I) : IsAdjoint (A i) :=
    ⟨(hsimple i).isSemisimple, center_factor_eq_bot_of_productIso A iso hG.center_eq_bot i⟩
  have hz : (ξ.map iso.hom).IsTrivial := by
    apply Cocycle.isTrivial_of_pi
    intro i
    exact h F (A i) (hadj i) (hsimple i) L _ ((hξ.map iso.hom).map (Pi.π A i))
  obtain ⟨c, hc⟩ := hz.map iso.inv
  refine ⟨c, fun a b => ?_⟩
  have he := hc a b
  change (ξ.toFun a b ≫ iso.hom.hom.hom) ≫ iso.inv.hom.hom = _ at he
  rw [Category.assoc, ← Grp.comp_hom_hom, iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at he
  exact he

end Langlands.GroupScheme
