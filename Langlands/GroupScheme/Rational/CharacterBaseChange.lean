import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Base change and descent fixedness of actual rational characters -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace rationalCharacters

variable {B S : Scheme.{u}} (b : S ⟶ B) {G H : GroupScheme B}

private def baseChangeRaw (χ : rationalCharacters G) :
    rationalCharacters ((GroupScheme.baseChange b).obj G) :=
  Additive.ofMul ((GroupScheme.baseChange b).map χ.toMul ≫ (Gm.baseChangeIso b).hom)

private theorem characterEval_baseChangeRaw (χ : rationalCharacters G)
    (V : Over S) (x : V ⟶ ((GroupScheme.baseChange b).obj G).X) :
    characterEval (baseChangeRaw b χ) V x =
      characterEval χ ((Over.map b).obj V) (baseChangePointsEquiv b G V x) := by
  rw [characterEval_apply]
  change Gm.pointsEquiv S V
      (x ≫ ((GroupScheme.baseChange b).map χ.toMul ≫ (Gm.baseChangeIso b).hom).hom.hom) = _
  rw [Grp.comp_hom_hom, ← Category.assoc, Gm.pointsEquiv_baseChangeIso_hom,
    Gm.baseChangeUnitsEquiv_apply, baseChangePointsEquiv_comp]
  rfl

/-- Pull back an actual rational character and identify the pulled-back multiplicative group. -/
def baseChange : rationalCharacters G →+
    rationalCharacters ((GroupScheme.baseChange b).obj G) where
  toFun := baseChangeRaw b
  map_zero' := by
    apply ext_characterEval
    intro V x
    rw [characterEval_baseChangeRaw, characterEval_zero, characterEval_zero]
  map_add' χ ψ := by
    apply ext_characterEval
    intro V x
    rw [characterEval_baseChangeRaw, characterEval_add, characterEval_add,
      characterEval_baseChangeRaw, characterEval_baseChangeRaw]

/-- The underlying morphism is the actual pullback followed by the canonical Gm comparison. -/
theorem baseChange_toMul (χ : rationalCharacters G) :
    (baseChange b χ).toMul =
      (GroupScheme.baseChange b).map χ.toMul ≫ (Gm.baseChangeIso b).hom := rfl

/-- Base change preserves the character value on every test scheme. -/
theorem characterEval_baseChange (χ : rationalCharacters G)
    (V : Over S) (x : V ⟶ ((GroupScheme.baseChange b).obj G).X) :
    characterEval (baseChange b χ) V x =
      characterEval χ ((Over.map b).obj V) (baseChangePointsEquiv b G V x) :=
  characterEval_baseChangeRaw b χ V x

/-- Base change commutes with restriction along any actual group-scheme morphism. -/
theorem baseChange_characterRestrict (f : H ⟶ G) (χ : rationalCharacters G) :
    baseChange b (characterRestrict f χ) =
      characterRestrict ((GroupScheme.baseChange b).map f) (baseChange b χ) := by
  apply ext_characterEval
  intro V x
  rw [characterEval_baseChange, characterEval_characterRestrict,
    characterEval_characterRestrict, characterEval_baseChange, baseChangePointsEquiv_comp]

variable (a : S ⟶ S) (ha : a ≫ b = b)

/-- A rational character from the original base is fixed by canonical descent transport. -/
theorem transportCharacter_baseChange (χ : rationalCharacters G) :
    transportCharacter b a ha G (baseChange b χ).toMul = (baseChange b χ).toMul := by
  apply hom_ext_points
  intro V x
  apply (Gm.pointsEquiv S V).injective
  rw [transportCharacter_points]
  change characterEval (baseChange b χ) ((Over.map a).obj V)
      (descentPoint b a ha G V x) = characterEval (baseChange b χ) V x
  rw [characterEval_baseChange, characterEval_baseChange,
    baseChangePointsEquiv_descentPoint, characterEval_naturality]
  change Units.map (𝟙 V.left : V.left ⟶ V.left).appTop.hom.toMonoidHom _ = _
  simp

end rationalCharacters

section Lattice

variable {B S : Scheme.{u}} (b : S ⟶ B)
    {T : CommGroupScheme B} {G : GroupScheme B}

/-- Base change commutes with restriction to the actual character lattice. -/
theorem characterLattice.baseChange_torusCharacterRestrict
    (j : T.toGrp ⟶ G) (χ : rationalCharacters G) :
    characterLattice.baseChange b T (torusCharacterRestrict j χ) =
      torusCharacterRestrict ((GroupScheme.baseChange b).map j)
        (rationalCharacters.baseChange b χ) := by
  change Additive.ofMul
      ((GroupScheme.baseChange b).map (j ≫ χ.toMul) ≫ (Gm.baseChangeIso b).hom) =
    Additive.ofMul
      ((GroupScheme.baseChange b).map j ≫
        (GroupScheme.baseChange b).map χ.toMul ≫ (Gm.baseChangeIso b).hom)
  rw [Functor.map_comp, Category.assoc]

/-- Every character from the original base is fixed by the canonical lattice transport. -/
theorem characterLattice.transport_baseChange
    (a : S ⟶ S) (ha : a ≫ b = b) (χ : characterLattice T) :
    characterLattice.transport b a ha T (characterLattice.baseChange b T χ) =
      characterLattice.baseChange b T χ :=
  congrArg Additive.ofMul
    (rationalCharacters.transportCharacter_baseChange b a ha (G := T.toGrp) χ)

end Lattice

/-- Over any algebra extension, a base-changed character is fixed by every base automorphism. -/
theorem characterLattice.galoisRepresentation_baseChange
    (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (σ : K ≃ₐ[k] K) (χ : characterLattice T) :
    characterLattice.galoisRepresentation k K T σ
        (characterLattice.baseChange (algebraBaseMap k K) T χ) =
      characterLattice.baseChange (algebraBaseMap k K) T χ :=
  characterLattice.transport_baseChange (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) χ

end Langlands.GroupScheme
