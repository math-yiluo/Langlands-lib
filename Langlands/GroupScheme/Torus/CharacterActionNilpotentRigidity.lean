import Langlands.GroupScheme.Torus.CharacterActionGrading
import Langlands.Algebra.NilpotentModuleReduction
import Mathlib.RingTheory.Ideal.Maps

/-! # Nilpotent rigidity of a diagonalizable action in affine coordinates -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {B : CommAlgCat.{u} R} (a : Action (M := M) B)

/-- The homogeneous projection of the coordinate action in degree `m`. -/
def projection (m : M) : Module.End R B where
  toFun b := ((coaction a).hom b).coeff m
  map_add' b c := by simp
  map_smul' r b := by
    change ((coaction a).hom (r • b)).coeff m = r • ((coaction a).hom b).coeff m
    rw [map_smul]
    rfl

@[simp]
theorem projection_apply (m : M) (b : B) :
    projection a m b = ((coaction a).hom b).coeff m := rfl

theorem projection_idempotent (m : M) : IsIdempotentElem (projection a m) := by
  ext b
  change ((coaction a).hom (((coaction a).hom b).coeff m)).coeff m =
    ((coaction a).hom b).coeff m
  rw [coaction_coefficient_homogeneous, AddMonoidAlgebra.coeff_single]
  simp

/-- A coaction congruent to the trivial one modulo a nilpotent base ideal is trivial. -/
theorem coaction_eq_constant_of_coeff_sub_mem (I : Ideal R) (hI : IsNilpotent I)
    (h : ∀ (m : M) (b : B),
      ((coaction a).hom b).coeff m - ((constant B).hom b).coeff m ∈
        I • (⊤ : Submodule R B)) :
    coaction a = constant B := by
  classical
  have hp (m : M) : projection a m = if m = 0 then 1 else 0 := by
    apply Langlands.NilpotentModuleReduction.eq_of_sub_mem I hI
      (projection_idempotent a m)
    · split <;> simp [IsIdempotentElem]
    · split <;> simp [Commute, SemiconjBy]
    · intro b
      have hb := h m b
      change ((coaction a).hom b).coeff m - (AddMonoidAlgebra.single 0 b).coeff m ∈
        I • (⊤ : Submodule R B) at hb
      by_cases hm : m = 0
      · simpa [hm] using hb
      · simpa [hm, Ne.symm hm] using hb
  apply CommAlgCat.hom_ext
  ext b m
  change ((coaction a).hom b).coeff m = (AddMonoidAlgebra.single 0 b).coeff m
  have hb := LinearMap.congr_fun (hp m) b
  by_cases hm : m = 0
  · simpa [hm] using hb
  · simpa [hm, Ne.symm hm] using hb

/-- It suffices to check triviality on algebras annihilated by the base ideal. -/
theorem coaction_eq_constant_of_nilpotent_quotient (I : Ideal R) (hI : IsNilpotent I)
    (h : ∀ (C : CommAlgCat.{u} R),
      (∀ r : R, r ∈ I → algebraMap R C r = 0) →
        ∀ (t : Multiplicative M →* Cˣ) (x : B ⟶ C), a.act t x = x) :
    coaction a = constant B := by
  let J := I.map (algebraMap R B)
  let C := CommAlgCat.of R (B ⧸ J)
  let q : B ⟶ C := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)
  have hC : ∀ r : R, r ∈ I → algebraMap R (algebra (M := M) C) r = 0 := by
    intro r hr
    change AddMonoidAlgebra.single 0 (Ideal.Quotient.mk J (algebraMap R B r)) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr
      (Ideal.mem_map_of_mem (algebraMap R B) hr)]
    exact AddMonoidAlgebra.single_zero _
  have he := h (algebra (M := M) C) hC (universal C) (q ≫ constant C)
  rw [act_universal] at he
  apply coaction_eq_constant_of_coeff_sub_mem a I hI
  intro m b
  have hb := congrArg (fun f : B ⟶ algebra (M := M) C => (f.hom b).coeff m) he
  change ((coefficientMap q).hom ((coaction a).hom b)).coeff m =
    (AddMonoidAlgebra.single 0 (q.hom b)).coeff m at hb
  rw [coefficientMap_coeff] at hb
  have heq : q.hom (((coaction a).hom b).coeff m) =
      q.hom (((constant B).hom b).coeff m) := by
    change q.hom (((coaction a).hom b).coeff m) =
      q.hom ((AddMonoidAlgebra.single 0 b).coeff m)
    by_cases hm : m = 0
    · simpa [hm] using hb
    · simpa [hm, Ne.symm hm] using hb
  rw [Ideal.smul_top_eq_map]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp heq

/-- An affine character action trivial over a nilpotent quotient is trivial on
every algebra, with no smoothness or finite-presentation assumption. -/
theorem act_eq_of_nilpotent_quotient (I : Ideal R) (hI : IsNilpotent I)
    (h : ∀ (C : CommAlgCat.{u} R),
      (∀ r : R, r ∈ I → algebraMap R C r = 0) →
        ∀ (t : Multiplicative M →* Cˣ) (x : B ⟶ C), a.act t x = x)
    {C : CommAlgCat.{u} R} (t : Multiplicative M →* Cˣ) (x : B ⟶ C) :
    a.act t x = x := by
  rw [act_eq_coaction_evaluate, coaction_eq_constant_of_nilpotent_quotient a I hI h,
    constant_evaluate]

end Langlands.GroupScheme.CharacterAction
