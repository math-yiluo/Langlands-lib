import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddings
import Langlands.GroupScheme.HomScheme.ClosedEmbeddingAction
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismTestLocality
import Langlands.GroupScheme.Torus.DiagonalizablePower

/-! # Character automorphisms acting on finite diagonalizable embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M]

/-- The finite character-automorphism group in the order of the parameter action. -/
abbrev CharacterActionGroup := (Multiplicative (M ≃+ M))ᵐᵒᵖ

/-- Identity character restriction is the identity group-scheme map. -/
theorem restrictMap_refl :
    Diagonalizable.restrictMap R (AddEquiv.refl M).toAddMonoidHom =
      𝟙 (Diagonalizable.groupScheme R M).toGrp := by
  apply hom_ext_points
  intro T x
  apply (Diagonalizable.characterPointsEquiv R M T).injective
  apply MonoidHom.ext
  intro m
  change Diagonalizable.characterPointsEquiv R M T
    (x ≫ (Diagonalizable.restrictMap R (AddEquiv.refl M).toAddMonoidHom).hom.hom)
      (.ofAdd m.toAdd) =
    Diagonalizable.characterPointsEquiv R M T x (.ofAdd m.toAdd)
  exact Diagonalizable.pointsEquiv_restrictMap R (AddEquiv.refl M).toAddMonoidHom x m.toAdd


/-- An additive equivalence of characters induces an actual diagonalizable isomorphism. -/
def characterIso (g : M ≃+ M) :
    (Diagonalizable.groupScheme R M).toGrp ≅ (Diagonalizable.groupScheme R M).toGrp where
  hom := Diagonalizable.restrictMap R g.toAddMonoidHom
  inv := Diagonalizable.restrictMap R g.symm.toAddMonoidHom
  hom_inv_id := by
    rw [Diagonalizable.restrictMap_comp]
    have he : g.toAddMonoidHom.comp g.symm.toAddMonoidHom =
        (AddEquiv.refl M).toAddMonoidHom := by ext m; simp
    rw [he, restrictMap_refl]
  inv_hom_id := by
    rw [Diagonalizable.restrictMap_comp]
    have he : g.symm.toAddMonoidHom.comp g.toAddMonoidHom =
        (AddEquiv.refl M).toAddMonoidHom := by ext m; simp
    rw [he, restrictMap_refl]

/-- Source automorphisms indexed by the opposite character group. -/
def sourceCharacterIso (k : CharacterActionGroup M) :
    (Diagonalizable.groupScheme R M).toGrp ≅ (Diagonalizable.groupScheme R M).toGrp :=
  characterIso R M k.unop.toAdd

@[simp]
theorem sourceCharacterIso_one : (sourceCharacterIso R M 1).hom = 𝟙 _ :=
  restrictMap_refl R M

theorem sourceCharacterIso_mul (g h : CharacterActionGroup M) :
    (sourceCharacterIso R M (g * h)).hom =
      (sourceCharacterIso R M h).hom ≫ (sourceCharacterIso R M g).hom := by
  change Diagonalizable.restrictMap R _ =
    Diagonalizable.restrictMap R _ ≫ Diagonalizable.restrictMap R _
  rw [Diagonalizable.restrictMap_comp]
  congr 1

variable [Fintype M]

/-- The opposite character automorphism group is finite. -/
instance : Finite (CharacterActionGroup M) := by
  have : Finite (M ≃+ M) :=
    Finite.of_injective (fun e : M ≃+ M => (e : M → M)) DFunLike.coe_injective
  exact Finite.of_injective (fun k : CharacterActionGroup M => k.unop.toAdd)
    (by intro a b h; apply MulOpposite.unop_injective; exact Multiplicative.toAdd.injective h)

variable (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

omit [Fintype M] in
/-- Distinct character indices remain distinct on every nonempty scheme test. -/
theorem sourceCharacterIso_baseChange_injective (T : Over (Spec R)) [Nonempty T.left] :
    Function.Injective (fun k : CharacterActionGroup M =>
      (GroupScheme.baseChange T.hom).map (sourceCharacterIso R M k).hom) := by
  intro g h he
  apply MulOpposite.unop_injective
  apply Multiplicative.toAdd.injective
  exact Diagonalizable.restrictEquiv_baseChange_injective T he

/-- The actual finite free action of character automorphisms on closed embeddings. -/
def characterAction :
    Langlands.AlgebraicGeometry.FiniteFreeSchemeAction (CharacterActionGroup M)
      (embeddingModel R M G).scheme.left :=
  (embeddingModel R M G).precompositionAction (sourceCharacterIso R M)
    (sourceCharacterIso_one R M) (sourceCharacterIso_mul R M)
      (sourceCharacterIso_baseChange_injective R M)

/-- The action automorphism is the underlying precomposition parameter map. -/
@[simp]
theorem characterAction_hom (k : CharacterActionGroup M) :
    ((characterAction R M G).act k).hom =
      ((embeddingModel R M G).precompose (sourceCharacterIso R M k)).left := rfl

/-- Character precomposition preserves the original coefficient base. -/
theorem characterAction_over (k : CharacterActionGroup M) :
    ((characterAction R M G).act k).hom ≫ (embeddingModel R M G).scheme.hom =
      (embeddingModel R M G).scheme.hom :=
  (embeddingModel R M G).precompositionAction_over (sourceCharacterIso R M)
    (sourceCharacterIso_one R M) (sourceCharacterIso_mul R M)
      (sourceCharacterIso_baseChange_injective R M) k

end Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddings
