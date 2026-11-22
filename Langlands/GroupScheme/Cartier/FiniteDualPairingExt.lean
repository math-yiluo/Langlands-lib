import Langlands.GroupScheme.Cartier.FiniteSchemeDualCharacters

/-! # Extensionality of finite Cartier points by evaluation -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.Cartier.FiniteDual

/-- Pair a dual point with every primal point after each restriction of its test scheme. -/
def schemeDualPairingOnRestrictions {R : CommRingCat.{u}} (G : CommGroupScheme (Spec R))
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (T : Over (Spec R)) (y : T ⟶ (schemeDual G).X) :
    ∀ (U : Over (Spec R)) (_ : U ⟶ T), (U ⟶ G.X) → (U ⟶ (Gm (Spec R)).X) :=
  fun U a x => finiteSchemePairing G U (a ≫ y) x

/-- The evaluations after every restriction distinguish the actual finite Cartier points. -/
theorem schemeDualPoint_ext_of_pairing {R : CommRingCat.{u}} (G : CommGroupScheme (Spec R))
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    {T : Over (Spec R)} {y z : T ⟶ (schemeDual G).X}
    (h : ∀ (U : Over (Spec R)) (a : U ⟶ T) (x : U ⟶ G.X),
      finiteSchemePairing G U (a ≫ y) x = finiteSchemePairing G U (a ≫ z) x) : y = z := by
  apply Additive.ofMul.injective
  apply ((schemeDualCharacters G).app (op T)).addCommGroupIsoToAddEquiv.injective
  apply relativeHom_ext
  intro U a x
  rw [← Category.id_comp a, ← relativeHomLocalPoints_restrict, ← relativeHomLocalPoints_restrict,
    relativeHomLocalPoints_id, relativeHomLocalPoints_id]
  change evaluation (restrict G (Gm (Spec R)) a
      ((schemeDualCharacters G).hom.app (op T) (Additive.ofMul y))) x =
    evaluation (restrict G (Gm (Spec R)) a
      ((schemeDualCharacters G).hom.app (op T) (Additive.ofMul z))) x
  rw [schemeDualCharacters_restrict, schemeDualCharacters_restrict,
    schemeDualCharacters_evaluation, schemeDualCharacters_evaluation]
  exact h U a x

theorem schemeDualPairingOnRestrictions_injective {R : CommRingCat.{u}} (G : CommGroupScheme (Spec R))
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] (T : Over (Spec R)) :
    Function.Injective (schemeDualPairingOnRestrictions G T) :=
  fun _ _ h => schemeDualPoint_ext_of_pairing G (fun U a x => congrFun (congrFun (congrFun h U) a) x)

end Langlands.GroupScheme.Cartier.FiniteDual
