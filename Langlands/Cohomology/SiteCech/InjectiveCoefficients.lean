import Langlands.Cohomology.SiteCech.FreeNerve
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Injective coefficients in the free sheaf Čech complex -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w uD vD

variable (R : Type w) [CommRing R]

/-- Hom into an injective object carries positive-degree exactness of a chain
complex to exactness of its linear Hom cochain complex. -/
theorem exactAt_linearYonedaObj_of_injective
    {D : Type uD} [Category.{vD} D] [Abelian D] [Linear R D]
    (P : ChainComplex D ℕ) (I : D) [Injective I] (n : ℕ)
    (hP : P.ExactAt (n + 1)) :
    (P.linearYonedaObj R I).ExactAt (n + 1) := by
  have h := (HomologicalComplex.exactAt_iff' P (n + 2) (n + 1) n
    (by simp) (by simp)).1 hP
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change P.d (n + 2) (n + 1) ≫ x = 0 at hx
  exact ⟨h.descToInjective x hx, h.comp_descToInjective x hx⟩

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasSheafify J (ModuleCat.{w} R)]
variable (f : Arrow (Cᵒᵖ ⥤ Type w))

/-- The defined Čech cochain complex is the linear Hom complex of the free sheaf
Čech chain complex. The comparison is the identity in each degree. -/
def cochainComplexIsoLinearYoneda (F : Sheaf J (ModuleCat.{w} R)) :
    (cochainComplexFunctor J R f).obj F ≅
      (freeCechChainComplex J R f).linearYonedaObj R F := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  rintro n j (rfl : n + 1 = j)
  change ModuleCat.ofHom (Linear.leftComp R F
    ((freeCechChainComplex J R f).d (n + 1) n)) =
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((freeCechNerve J R f).rightOp ⋙ (linearYoneda R _).obj F)).d n (n + 1)
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  change ((linearYoneda R (Sheaf J (ModuleCat.{w} R))).obj F).map
      (((freeCechChainComplex J R f).d (n + 1) n).op) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((linearYoneda R (Sheaf J (ModuleCat.{w} R))).obj F).map
        (((freeCechNerve J R f).δ i).op)
  simp only [freeCechChainComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, op_sum, op_zsmul,
    Functor.map_sum, Functor.map_zsmul]

/-- An exact free sheaf Čech augmentation implies vanishing positive Čech
cohomology for injective coefficients. -/
theorem isZero_cohomologyFunctor_obj_of_injective
    [QuasiIso (freeCechAugmentation J R f)]
    (I : Sheaf J (ModuleCat.{w} R)) [Injective I] (n : ℕ) :
    IsZero ((cohomologyFunctor J R f (n + 1)).obj I) := by
  have hP : (freeCechChainComplex J R f).ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt (freeCechAugmentation J R f) (n + 1)).2
      (ChainComplex.exactAt_succ_single_obj _ n)
  exact ((exactAt_linearYonedaObj_of_injective R _ I n hP).of_iso
    (cochainComplexIsoLinearYoneda R J f I).symm).isZero_homology

end Langlands.Cohomology.SiteCech
