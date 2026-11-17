import Langlands.Algebra.BialgebraSpreading
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocalization

/-! # Bialgebra isomorphisms over localizations spread to principal localizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BialgebraSpreading

section Localization

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- Transition maps in the directed system of principal localizations, as
algebra homomorphisms over the original ring. -/
def awayMapAlgHom (a b : DivIndex M) (h : a ≤ b) :
    Localization.Away a.val →ₐ[R] Localization.Away b.val :=
  { awayMap h with commutes' := awayMap_algebraMap h }

instance awayDirectedSystem :
    DirectedSystem (fun a : DivIndex M => Localization.Away a.val)
      (fun a b h => ⇑(awayMapAlgHom M a b h)) where
  map_self := by
    intro a x
    exact congrArg (fun g : _ →+* _ => g x) awayMap_id
  map_map := by
    intro c b a hab hbc x
    exact congrArg (fun g : _ →+* _ => g x) (awayMap_comp hab hbc)

variable (L : Type u) [CommRing L] [Algebra R L] [IsLocalization M L]

local instance awayAlgebra (a : DivIndex M) : Algebra (Localization.Away a.val) L :=
  (toLoc M L a).toAlgebra

local instance awayTower (a : DivIndex M) : IsScalarTower R (Localization.Away a.val) L :=
  IsScalarTower.of_algebraMap_eq (fun r => (toLoc_algebraMap M L a r).symm)

/-- The explicit direct-limit predicate for principal localizations. -/
theorem isDirectLimit_away :
    IsDirectLimit (fun a b h => ⇑(awayMapAlgHom M a b h))
      (fun a => ⇑(algebraMap (Localization.Away a.val) L)) where
  surj := exists_toLoc_eq M L
  inj _a _b x y h := exists_awayMap_eq M L x y h
  compatibility _a _b h x :=
    congrArg (fun g : _ →+* _ => g x) (toLoc_comp_awayMap M L h)

/-- An isomorphism of finitely presented bialgebras over a localization
already exists over one principal localization from its multiplicative set. -/
theorem exists_away_bialgEquiv
    (A B : Type u) [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
    (e : L ⊗[R] A ≃ₐc[L] L ⊗[R] B) :
    ∃ s ∈ M, Nonempty
      (Localization.Away s ⊗[R] A ≃ₐc[Localization.Away s] Localization.Away s ⊗[R] B) := by
  obtain ⟨a, ha⟩ := exists_bialgEquiv R
    (fun a : DivIndex M => Localization.Away a.val) (awayMapAlgHom M) L
    (isDirectLimit_away M L) A B e
  exact ⟨a.val, a.val_mem, ha⟩

end Localization

end Langlands.BialgebraSpreading
