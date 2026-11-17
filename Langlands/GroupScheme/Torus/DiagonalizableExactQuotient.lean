import Langlands.GroupScheme.Torus.DiagonalizablePower
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Exact quotients of diagonalizable groups -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

variable (R : CommRingCat.{u}) {Λ Γ : Type u} [AddCommGroup Λ] [AddCommGroup Γ]
    (p : Λ →+ Γ)

/-- Restriction expressed in the explicit character point model. -/
theorem characterPointsEquiv_restrictMap {U : Over (Spec R)}
    (x : U ⟶ (groupScheme R Γ).X) (l : Λ) :
    characterPointsEquiv R Λ U (x ≫ (restrictMap R p).hom.hom) (.ofAdd l) =
      characterPointsEquiv R Γ U x (.ofAdd (p l)) :=
  pointsEquiv_restrictMap R p x l

/-- The quotient of `D(Λ)` by the subgroup induced by a surjection `Λ → Γ`. -/
def exactQuotientMap :
    (groupScheme R Λ).toGrp ⟶ (groupScheme R p.ker).toGrp :=
  restrictMap R p.ker.subtype

/-- The full kernel of restriction to `ker p` is the image of `D(Γ)`. -/
theorem kernel_exactQuotientMap (hp : Function.Surjective p) :
    SubgroupFunctor.range (kernelι (exactQuotientMap R p)) =
      SubgroupFunctor.range (restrictMap R p) := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff]
  constructor
  · intro hx
    let χ := characterPointsEquiv R Λ U x
    let φ : Λ →+ Additive (Γ(U.left, ⊤))ˣ :=
      { toFun := fun l => .ofMul (χ (.ofAdd l))
        map_zero' := congrArg Additive.ofMul χ.map_one
        map_add' := fun l m =>
          congrArg Additive.ofMul (χ.map_mul (.ofAdd l) (.ofAdd m)) }
    have hφ : p.ker ≤ φ.ker := by
      intro l hl
      have hχ : χ (.ofAdd l) = 1 := by
        calc
          _ = characterPointsEquiv R p.ker U
              (x ≫ (exactQuotientMap R p).hom.hom) (.ofAdd ⟨l, hl⟩) :=
            (pointsEquiv_restrictMap R p.ker.subtype x ⟨l, hl⟩).symm
          _ = 1 := by rw [hx, map_one]; rfl
      exact congrArg Additive.ofMul hχ
    let e := QuotientAddGroup.quotientKerEquivOfSurjective p hp
    let ψ := (QuotientAddGroup.lift p.ker φ hφ).comp e.symm.toAddMonoidHom
    have hψ (l : Λ) : ψ (p l) = φ l := by
      change QuotientAddGroup.lift p.ker φ hφ (e.symm (p l)) = φ l
      rw [show p l = e (QuotientAddGroup.mk l) from rfl, e.symm_apply_apply]
      rfl
    let t := (characterPointsEquiv R Γ U).symm (AddMonoidHom.toMultiplicative ψ)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨t, ?_⟩
    apply (characterPointsEquiv R Λ U).injective
    apply MonoidHom.ext
    intro l
    change characterPointsEquiv R Λ U (t ≫ (restrictMap R p).hom.hom)
      (.ofAdd l.toAdd) = χ l
    rw [characterPointsEquiv_restrictMap]
    change characterPointsEquiv R Γ U
      ((characterPointsEquiv R Γ U).symm (AddMonoidHom.toMultiplicative ψ))
        (.ofAdd (p l.toAdd)) = χ l
    rw [MulEquiv.apply_symm_apply]
    exact congrArg Additive.toMul (hψ l.toAdd)
  · intro hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply (characterPointsEquiv R p.ker U).injective
    apply MonoidHom.ext
    intro l
    change characterPointsEquiv R p.ker U
      ((t ≫ (restrictMap R p).hom.hom) ≫ (restrictMap R p.ker.subtype).hom.hom)
        (.ofAdd l.toAdd) = _
    rw [characterPointsEquiv_restrictMap, characterPointsEquiv_restrictMap]
    change characterPointsEquiv R Γ U t (.ofAdd (p l.toAdd.val)) =
      characterPointsEquiv R p.ker U 1 l
    rw [show p l.toAdd.val = 0 from l.toAdd.property]
    simp

/-- Over a nonzero Noetherian base ring, the explicit map is the actual fppf quotient. -/
theorem isFppfQuotient_exactQuotientMap [Nontrivial R] [IsNoetherianRing R]
    [AddGroup.FG Λ] (hp : Function.Surjective p) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (restrictMap R p))
      (exactQuotientMap R p) := by
  obtain ⟨hf, hs⟩ :=
    flat_and_surjective_restrictMap R p.ker.subtype (Subtype.val_injective)
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have : Module.Finite ℤ p.ker :=
    Module.Finite.of_injective p.ker.subtype.toIntLinearMap Subtype.val_injective
  have : AddGroup.FG p.ker := Module.Finite.iff_addGroup_fg.mp inferInstance
  have : IsLocallyNoetherian (groupScheme R p.ker).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (groupScheme R p.ker).X.hom
  have : LocallyOfFiniteType
      ((exactQuotientMap R p).hom.hom.left ≫ (groupScheme R p.ker).X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (exactQuotientMap R p).hom.hom.left :=
    locallyOfFiniteType_of_comp _ (groupScheme R p.ker).X.hom
  exact ⟨hf, hs, inferInstance, kernel_exactQuotientMap R p hp⟩

end Langlands.GroupScheme.Diagonalizable
