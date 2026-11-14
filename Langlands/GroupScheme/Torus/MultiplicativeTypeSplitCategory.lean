import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Category.FGModuleCat.Basic

/-! # Multiplicative-type groups split by a specified field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DiagonalizableCharacter

variable (k : Type u) [Field k] (M : Type u) [AddCommGroup M]

/-- The evaluation characters, with their actual additive law. -/
def evalCharacterAddHom :
    M →+ characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) M) :=
  AddMonoidHom.mk' (evalCharacter (CommRingCat.of k) M) fun a b => by
    apply characterLattice.ext_points
    intro U x
    rw [evalCharacter_apply, comp_groupHom_add, map_mul,
      evalCharacter_apply, evalCharacter_apply]
    exact map_mul _ _ _

@[simp]
theorem evalCharacterAddHom_apply (m : M) :
    evalCharacterAddHom k M m = evalCharacter (CommRingCat.of k) M m := rfl

/-- Evaluation identifies the full group of actual characters with the model group. -/
theorem evalCharacterAddHom_bijective :
    Function.Bijective (evalCharacterAddHom k M) := by
  constructor
  · intro a b h
    have hb : ∀ (U : Over (Spec (CommRingCat.of k)))
        (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) M).X),
        (NaturalUnits.ofCharacter (evalCharacter (CommRingCat.of k) M a)).app U x =
          Diagonalizable.characterPointsEquiv (CommRingCat.of k) M U x (.ofAdd b) := by
      intro U x
      change Gm.pointsEquiv _ U
        (x ≫ (CommGroupScheme.groupHom (evalCharacter (CommRingCat.of k) M a)).hom.hom) = _
      rw [← evalCharacterAddHom_apply, h, evalCharacterAddHom_apply]
      exact evalCharacter_apply _ M b U x
    exact (NaturalUnits.ofCharacter (evalCharacter (CommRingCat.of k) M a)).existsUnique.unique
      (evalCharacter_apply _ M a) hb
  · intro χ
    obtain ⟨m, hm, -⟩ := (NaturalUnits.ofCharacter χ).existsUnique
    refine ⟨m, ?_⟩
    apply characterLattice.ext_points
    intro U x
    exact (evalCharacter_apply _ M m U x).trans (hm U x).symm

/-- The additive evaluation equivalence, including groups with torsion. -/
def evalCharacterEquiv :
    M ≃+ characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) M) :=
  AddEquiv.ofBijective (evalCharacterAddHom k M) (evalCharacterAddHom_bijective k M)

@[simp]
theorem evalCharacterEquiv_apply (m : M) :
    evalCharacterEquiv k M m = evalCharacter (CommRingCat.of k) M m := rfl

end DiagonalizableCharacter

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The specified extension splits the full multiplicative-type group, with a
finitely generated abelian model group. Splitting models are a property, not
additional data on objects or restrictions on morphisms. -/
def multiplicativeTypeSplitBy :
    ObjectProperty (CommGroupScheme (Spec (CommRingCat.of k))) :=
  fun T => ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
    Nonempty (((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T) ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M)

/-- Actual commutative group schemes split by `L/k`, with all their ground-field
homomorphisms. No splitting model is chosen as part of an object. -/
abbrev SplitMultiplicativeType :=
  (multiplicativeTypeSplitBy k L).FullSubcategory

namespace multiplicativeTypeSplitBy

variable {k L}
  {G H : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The fixed-extension splitting property is preserved by actual isomorphisms. -/
theorem of_iso (e : H ≅ G) (hG : multiplicativeTypeSplitBy k L G) :
    multiplicativeTypeSplitBy k L H := by
  obtain ⟨M, hM, hfg, ⟨d⟩⟩ := hG
  exact ⟨M, hM, hfg,
    ⟨(CommGroupScheme.baseChange (algebraBaseMap k L)).mapIso e ≪≫ d⟩⟩

/-- Forgetting the specified splitting field gives the existing multiplicative-type
predicate, with its full finitely generated diagonalizable model. -/
theorem isMultiplicativeType (hG : multiplicativeTypeSplitBy k L G) :
    IsMultiplicativeType G.toGrp := by
  obtain ⟨M, hM, hfg, ⟨d⟩⟩ := hG
  refine ⟨L, inferInstance, inferInstance, M, hM, hfg, ⟨?_⟩⟩
  exact ⟨CommGroupScheme.groupHom d.hom, CommGroupScheme.groupHom d.inv,
    congrArg CommGroupScheme.groupHom d.hom_inv_id,
    congrArg CommGroupScheme.groupHom d.inv_hom_id⟩

/-- The actual characters over the specified splitting field are finitely generated. -/
theorem character_fg (hG : multiplicativeTypeSplitBy k L G) :
    AddGroup.FG
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj G)) := by
  obtain ⟨M, hM, hfg, ⟨d⟩⟩ := hG
  let e := (DiagonalizableCharacter.evalCharacterEquiv L M).trans
    (characterLattice.congr d).symm
  exact AddGroup.fg_of_surjective (f := e.toAddMonoidHom) e.surjective

end multiplicativeTypeSplitBy

namespace SplitMultiplicativeType

/-- Forgetting the splitting condition retains the actual ground-field group and maps. -/
abbrev inclusion :
    SplitMultiplicativeType k L ⥤ CommGroupScheme (Spec (CommRingCat.of k)) :=
  (multiplicativeTypeSplitBy k L).ι

instance (T : SplitMultiplicativeType k L) :
    AddGroup.FG
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T.obj)) :=
  T.property.character_fg

/-- The full character group over `L`, as an existing finitely generated integral
module. The construction retains torsion. -/
def characterModule (T : SplitMultiplicativeType k L) : FGModuleCat.{u} ℤ := by
  letI : Module.Finite ℤ
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T.obj)) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact FGModuleCat.of ℤ
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T.obj))

end SplitMultiplicativeType

end Langlands.GroupScheme
