import Langlands.GroupScheme.Reductive.BicovariantTorusWeight
import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.Torus.Maximal

/-! # Actual torus characters fixed by unit-valued normalizer points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k]
    {G H Q : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A normalizing point intertwines two supplied factorizations of the same
torus embedding through the inverse normalizing automorphism. -/
theorem isIntertwiningPoint_of_normalizer
    (i : H ⟶ G) (q : Q ⟶ G) (j : T.toGrp ⟶ G)
    (jH : T.toGrp ⟶ H) (jQ : T.toGrp ⟶ Q)
    (hH : jH ≫ i = j) (hQ : jQ ≫ q = j) [Mono j.hom.hom.left]
    (n : normalizerPoints j) :
    IsIntertwiningPoint i q jH jQ
      (CommGroupScheme.groupHom (normalizingAut j n).inv) n.val := by
  intro U t
  have he := congrArg
    (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom)
    (isNormalizingPoint_normalizingAut j n).inv
  simp only [Grp.comp_hom_hom] at he
  rw [← Category.assoc, comp_innerIso_hom, constantPoint_inv] at he
  have he' :
      (G.constantPoint n.val U)⁻¹ * (t ≫ j.hom.hom) * G.constantPoint n.val U =
        t ≫ (CommGroupScheme.groupHom (normalizingAut j n).inv).hom.hom ≫
          j.hom.hom := by simpa only [inv_inv, Iso.symm_hom] using he
  have hH' : jH.hom.hom ≫ i.hom.hom = j.hom.hom :=
    congrArg (fun f : T.toGrp ⟶ G => f.hom.hom) hH
  have hQ' : jQ.hom.hom ≫ q.hom.hom = j.hom.hom :=
    congrArg (fun f : T.toGrp ⟶ G => f.hom.hom) hQ
  simp only [← Category.assoc, hH', hQ']
  simp only [Category.assoc]
  rw [← he']
  group

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]

local instance bicovariantNormalizerCharacterIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bicovariantNormalizerCharacterIsAffine2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
local instance bicovariantNormalizerCharacterIsAffine3 : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom

variable (i : H ⟶ G) (q : Q ⟶ G) (j : T.toGrp ⟶ G)
    (jH : T.toGrp ⟶ H) (jQ : T.toGrp ⟶ Q)
    (eta : rationalCharacters H) (ψ : rationalCharacters Q) (d : algebra G)
    (hd : d ∈ leftCovariantSubspace i (characterCoordinate H eta))
    (hr : ∀ (U : Over (Spec (CommRingCat.of k))) (h : U ⟶ Q.X) (g : U ⟶ G.X),
      pointAlgebraHom G U (g * (h ≫ q.hom.hom)⁻¹) d =
        pointAlgebraHom Q U h (characterCoordinate Q ψ) * pointAlgebraHom G U g d)
    (hH : jH ≫ i = j) (hQ : jQ ≫ q = j)
    (hopp : characterRestrict jQ ψ = -characterRestrict jH eta)
    [Mono j.hom.hom.left]

include hd hr hH hQ hopp

/-- Bi-covariance with opposite torus characters forces every unit-valued
normalizing point to fix the actual restricted character. -/
theorem weylAction_fixed_of_unit_bicovariant
    (n : normalizerPoints j)
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d)) :
    weylAction j n (rationalCharacters.equivCharacterLattice T (characterRestrict jH eta)) =
      rationalCharacters.equivCharacterLattice T (characterRestrict jH eta) := by
  let φ := CommGroupScheme.groupHom (normalizingAut j n).inv
  have he : characterRestrict φ (characterRestrict jH eta) = characterRestrict jH eta := by
    apply rationalCharacters.ext_characterEval
    intro U t
    apply Units.ext
    have h := pointAlgebraHom_comp_eq_of_normalizes i q hd hr jH jQ φ n.val
      (isIntertwiningPoint_of_normalizer i q j jH jQ hH hQ n) hu U t
    rw [pointAlgebraHom_characterCoordinate, pointAlgebraHom_characterCoordinate,
      map_inv] at h
    have hψ : characterEval ψ U (t ≫ φ.hom.hom ≫ jQ.hom.hom) =
        (characterEval (characterRestrict jH eta) U (t ≫ φ.hom.hom))⁻¹ := by
      rw [← Category.assoc,
        ← characterEval_characterRestrict jQ ψ U (t ≫ φ.hom.hom), hopp,
        characterEval_neg]
    rw [hψ, inv_inv] at h
    rw [characterEval_characterRestrict]
    simpa only [characterEval_characterRestrict] using h.symm
  have h := congrArg (rationalCharacters.equivCharacterLattice T) he
  exact h

/-- The actual restricted torus character, certified to lie in the fixed
character lattice of the supplied unit-valued normalizing point. -/
def unitNormalizerFixedCharacter
    (n : normalizerPoints j)
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d)) :
    {x : characterLattice T // weylAction j n x = x} :=
  ⟨rationalCharacters.equivCharacterLattice T (characterRestrict jH eta),
    weylAction_fixed_of_unit_bicovariant i q j jH jQ eta ψ d hd hr hH hQ hopp n hu⟩

theorem unitNormalizerFixedCharacter_val
    (n : normalizerPoints j)
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d)) :
    (unitNormalizerFixedCharacter i q j jH jQ eta ψ d hd hr hH hQ hopp n hu).val =
      rationalCharacters.equivCharacterLattice T (characterRestrict jH eta) :=
  rfl

end AffineCoordinates

end Langlands.GroupScheme
