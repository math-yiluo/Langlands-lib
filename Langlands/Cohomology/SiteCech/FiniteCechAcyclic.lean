import Langlands.Cohomology.SiteCech.FiniteCechSystem
import Langlands.Cohomology.RightDerivedSequence
import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Higher-derived vanishing from a finite augmented test system -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open ZeroObject

universe u v a b w

variable {D : Type u} [Category.{v} D] [Abelian D] [EnoughInjectives D]
variable {ι : Type a} {B : ι → D} (K : FiniteCechSystem.{u, v, a, b} B)
variable (R : Type w) [CommRing R] [Linear R D]

/-- Higher right-derived linear Hom vanishes on all test objects. -/
def DerivedHomAcyclic (B : ι → D) (R : Type w) [CommRing R] [Linear R D]
    (F : D) : Prop :=
  ∀ i n, IsZero ((((linearCoyoneda R D).obj (op (B i))).rightDerived (n + 1)).obj F)

omit [EnoughInjectives D] in
/-- Test-object Hom sends a short exact sequence with Hom-acyclic kernel
coefficient to an epimorphism at its second arrow. -/
theorem FiniteCechSystem.epi_linearCoyoneda_map (S : ShortComplex D)
    (hS : S.ShortExact) (hF : K.HomAcyclic R S.X₁) (i : ι) :
    Epi (((linearCoyoneda R D).obj (op (B i))).map S.g) := by
  apply (ModuleCat.epi_iff_surjective _).2
  intro s
  exact K.exists_lift R S hS hF i s

/-- The finite augmented test-system hypotheses and positive Hom exactness
imply vanishing of all higher right-derived test-object Hom functors. -/
theorem FiniteCechSystem.derivedHomAcyclic_of_homAcyclic (F : D)
    (hF : K.HomAcyclic R F) : DerivedHomAcyclic B R F := by
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard (ModuleCat.{v} R)
  intro i n
  let T := (linearCoyoneda R D).obj (op (B i))
  have : PreservesLimits T := by
    have : PreservesLimits (T ⋙ forget (ModuleCat.{v} R)) :=
      (inferInstance : PreservesLimits (coyoneda.obj (op (B i))))
    exact preservesLimits_of_reflects_of_preserves T (forget (ModuleCat.{v} R))
  induction n generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance
    have : Epi (T.map S.g) := K.epi_linearCoyoneda_map R S hS hF i
    have he : (T.rightDerived 0).map S.g =
        T.rightDerivedZeroIsoSelf.hom.app S.X₂ ≫ T.map S.g ≫
          T.rightDerivedZeroIsoSelf.inv.app S.X₃ := by
      rw [← Category.assoc, ← T.rightDerivedZeroIsoSelf.hom.naturality,
        Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have : Epi ((T.rightDerived 0).map S.g) := by
      rw [he]
      infer_instance
    have : Epi (DerivedPlus.rightDerivedδ T hS 0 1 rfl) :=
      DerivedPlus.epi_rightDerivedδ_of_isZero T hS 0 1 rfl
        (T.isZero_rightDerived_obj_injective_succ 0 (Injective.under F))
    exact IsZero.of_epi_eq_zero _ (zero_of_epi_comp _
      (DerivedPlus.rightDerived_map_comp_δ T hS 0 1 rfl))
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance
    have hQ := K.homAcyclic_quotient R S hS hF
    have : Epi (DerivedPlus.rightDerivedδ T hS (n + 1) (n + 1 + 1) rfl) :=
      DerivedPlus.epi_rightDerivedδ_of_isZero T hS _ _ rfl
        (T.isZero_rightDerived_obj_injective_succ (n + 1) (Injective.under F))
    exact IsZero.of_epi (DerivedPlus.rightDerivedδ T hS (n + 1) (n + 1 + 1) rfl)
      (ih S.X₃ hQ)

/-- The actual higher-derived test-object Hom module identified with zero. -/
def FiniteCechSystem.derivedHomZeroIso (F : D) (hF : K.HomAcyclic R F) (i : ι) (n : ℕ) :
    ((((linearCoyoneda R D).obj (op (B i))).rightDerived (n + 1)).obj F) ≅ 0 :=
  (K.derivedHomAcyclic_of_homAcyclic R F hF i n).isoZero

end Langlands.Cohomology.SiteCech
