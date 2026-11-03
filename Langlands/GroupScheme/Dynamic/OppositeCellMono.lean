import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Monomorphism of opposite dynamic multiplication -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

/-- Multiplication of the opposite dynamic unipotent and the dynamic
parabolic is a monomorphism for any affine group scheme over a field. -/
theorem mono_oppositeCellMul {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {U P : GroupScheme (Spec (CommRingCat.of k))} {iU : U ⟶ G} {iP : P ⟶ G}
    (hU : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy iU)
    (hP : (parabolic χ).IsRepresentedBy iP) :
    Mono (SubgroupFunctor.cellMultiplication iU iP) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Mono iU.hom.hom := hU.1
  have : Mono iP.hom.hom := hP.1
  refine ⟨fun {T} a b hab => ?_⟩
  let ua : T ⟶ G.X := a ≫ fst U.X P.X ≫ iU.hom.hom
  let ub : T ⟶ G.X := b ≫ fst U.X P.X ≫ iU.hom.hom
  let pa : T ⟶ G.X := a ≫ snd U.X P.X ≫ iP.hom.hom
  let pb : T ⟶ G.X := b ≫ snd U.X P.X ≫ iP.hom.hom
  have hprod : ua * pa = ub * pb := by
    simpa only [SubgroupFunctor.cellMultiplication, MonObj.comp_mul, Category.assoc] using hab
  have hmemU (x : T ⟶ U.X) :
      x ≫ iU.hom.hom ∈ (unipotent (oppositeCocharacter χ)).carrier T := by
    rw [oppositeCocharacter, ← hU.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  have hmemP (x : T ⟶ P.X) :
      x ≫ iP.hom.hom ∈ (parabolic χ).carrier T := by
    rw [← hP.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  have hratio : ub⁻¹ * ua = pb * pa⁻¹ := by
    calc
      ub⁻¹ * ua = ub⁻¹ * (ua * pa) * pa⁻¹ := by simp [mul_assoc]
      _ = ub⁻¹ * (ub * pb) * pa⁻¹ := by rw [hprod]
      _ = pb * pa⁻¹ := by simp
  have hratioU : ub⁻¹ * ua ∈ (unipotent (oppositeCocharacter χ)).carrier T :=
    ((unipotent (oppositeCocharacter χ)).carrier T).mul_mem
      (((unipotent (oppositeCocharacter χ)).carrier T).inv_mem
        (hmemU (b ≫ fst U.X P.X))) (hmemU (a ≫ fst U.X P.X))
  have hratioP : ub⁻¹ * ua ∈ (parabolic χ).carrier T := by
    rw [hratio]
    exact ((parabolic χ).carrier T).mul_mem (hmemP (b ≫ snd U.X P.X))
      (((parabolic χ).carrier T).inv_mem (hmemP (a ≫ snd U.X P.X)))
  have hone : ub⁻¹ * ua = 1 :=
    eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hratioU hratioP
  have hu : ua = ub := (inv_mul_eq_one.mp hone).symm
  have hp : pa = pb := by
    rw [hu] at hprod
    exact mul_left_cancel hprod
  apply CartesianMonoidalCategory.hom_ext
  · apply (cancel_mono iU.hom.hom).mp
    simpa only [Category.assoc] using hu
  · apply (cancel_mono iP.hom.hom).mp
    simpa only [Category.assoc] using hp

end Langlands.GroupScheme.Dynamic
