import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Relative tori as groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- The finite free diagonalizable model of a split torus over any base. -/
def splitTorusDiagonalizableIso (S : Scheme.{u}) (I : Type u) [Fintype I] :
    RelativeMultiplicativeType.diagonalizable S (I → ℤ) ≅ splitTorus S I := by
  classical
  exact (baseChange (Gm.toSpecZ S)).mapIso
      (Diagonalizable.splitIso (CommRingCat.of (ULift.{u} ℤ)) (AddEquiv.refl (I → ℤ))) ≪≫
    splitTorus.baseChangeIso (Gm.toSpecZ S) I

/-- A split torus is relatively diagonalizable, with a finite free character group. -/
theorem IsSplitTorus.isRelativeDiagonalizable {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsSplitTorus G) : RelativeMultiplicativeType.IsDiagonalizable G := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  exact ⟨I → ℤ, inferInstance, inferInstance, ⟨e ≪≫ (splitTorusDiagonalizableIso S I).symm⟩⟩

/-- Every relative torus is of multiplicative type in the relative fppf sense. -/
theorem RelativeTorus.IsTorus.isMultiplicativeType {S : Scheme.{u}} {G : GroupScheme S}
    (hG : RelativeTorus.IsTorus G) : RelativeMultiplicativeType.IsMultiplicativeType G := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun k => ?_), fun k => (h𝒰 k).isRelativeDiagonalizable⟩
  have : Etale (𝒰.f k) := 𝒰.map_prop k
  exact ⟨inferInstance, inferInstance⟩

end Langlands.GroupScheme
