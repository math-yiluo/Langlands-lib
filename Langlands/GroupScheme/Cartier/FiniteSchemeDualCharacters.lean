import Langlands.GroupScheme.Cartier.FiniteDualAffineCharacters
import Langlands.GroupScheme.Cartier.FiniteDualNaturalPairing
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # The actual finite dual spectrum represents relative characters -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier.FiniteDual

attribute [local instance] finiteScheme_isAffine finiteScheme_cocomm finiteScheme_finite
  finiteScheme_projective

variable {R : CommRingCat.{u}} (G : CommGroupScheme (Spec R)) [IsFinite G.X.hom] [Flat G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

local notation "A" => AffineCoordinates.hopfAlgebra G.toGrp

private def specComparison : specGroup R A ≅ G :=
  CommGroupScheme.isoOfGroupIso (AffineCoordinates.hopfSpecIso G.toGrp)

/-- The actual finite dual spectrum represents the relative characters of the
original scheme, by its evaluation pairing. -/
def schemeDualCharacters : additivePoints (schemeDual G).toGrp ≅ characters G := by
  let c := characterComparison R A
  have h (B : Type u) [CommRing B] [Algebra R B] :
      Function.Bijective (c.app (op (specOver R B))) :=
    (affineCharacterEquiv R A B).bijective.comp Additive.toMul.bijective
  let : IsIso c := isIso_additivePoints_characters_of_bijective c h
  exact asIso c ≪≫ charactersIso (specComparison G).symm

/-- The relative character evaluates by the actual finite Cartier pairing. -/
theorem schemeDualCharacters_evaluation (T : Over (Spec R))
    (y : T ⟶ (schemeDual G).X) (x : T ⟶ G.X) :
    evaluation ((schemeDualCharacters G).hom.app (op T) (Additive.ofMul y)) x =
      finiteSchemePairing G T y x := by
  let b : G ⟶ specGroup R A := (specComparison G).inv
  let χ : RelativeHom (specGroup R A) (Gm (Spec R)) T := characterOfPoint R A y
  let z : T ⟶ (specGroup R A).X := x ≫ b.toMul.hom.hom
  exact (evaluation_precompose b χ x).trans (characterOfPoint_evaluation R A (T := T) y z)

/-- The represented character restricts along the actual test map. -/
theorem schemeDualCharacters_restrict {T U : Over (Spec R)} (b : U ⟶ T) (y : T ⟶ (schemeDual G).X) :
    restrict G (Gm (Spec R)) b ((schemeDualCharacters G).hom.app (op T) (Additive.ofMul y)) =
      (schemeDualCharacters G).hom.app (op U) (Additive.ofMul (b ≫ y)) := by
  let i : G ⟶ specGroup R A := (specComparison G).inv
  change restrict G (Gm (Spec R)) b (precompose (Gm (Spec R)) i T (characterOfPoint R A y)) =
    precompose (Gm (Spec R)) i U (characterOfPoint R A (b ≫ y))
  rw [restrict_precompose, characterOfPoint_restrict]

variable {G} {H : CommGroupScheme (Spec R)} [IsFinite H.X.hom] [Flat H.X.hom]
  [LocallyOfFinitePresentation H.X.hom]

/-- The actual transpose map is precomposition on represented relative characters. -/
theorem schemeDualCharacters_precompose (f : G ⟶ H) (T : Over (Spec R)) (y : T ⟶ (schemeDual H).X) :
    (schemeDualCharacters G).hom.app (op T) (Additive.ofMul (y ≫ (schemeDualMap f).toMul.hom.hom)) =
      precompose (Gm (Spec R)) f T ((schemeDualCharacters H).hom.app (op T) (Additive.ofMul y)) := by
  apply relativeHom_ext
  intro V a x
  rw [← Category.id_comp a, ← relativeHomLocalPoints_restrict, ← relativeHomLocalPoints_restrict,
    relativeHomLocalPoints_id, relativeHomLocalPoints_id, restrict_precompose,
    schemeDualCharacters_restrict, schemeDualCharacters_restrict]
  let χ : RelativeHom H (Gm (Spec R)) V :=
    (schemeDualCharacters H).hom.app (op V) (Additive.ofMul (a ≫ y))
  change evaluation ((schemeDualCharacters G).hom.app (op V)
      (Additive.ofMul (a ≫ y ≫ (schemeDualMap f).toMul.hom.hom))) x =
    evaluation (precompose (Gm (Spec R)) f V χ) x
  calc
    _ = finiteSchemePairing G V ((a ≫ y) ≫ (schemeDualMap f).toMul.hom.hom) x := by
      rw [Category.assoc]
      exact schemeDualCharacters_evaluation G V _ x
    _ = finiteSchemePairing H V (a ≫ y) (x ≫ f.toMul.hom.hom) :=
      (finiteSchemePairing_dualMap f V x (a ≫ y)).symm
    _ = evaluation (precompose (Gm (Spec R)) f V χ) x :=
      ((evaluation_precompose f χ x).trans (schemeDualCharacters_evaluation H V _ _)).symm

end Langlands.GroupScheme.Cartier.FiniteDual
