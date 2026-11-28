import Langlands.Global.AdelicIntertwiningLeviQuotient

/-! # Split-centre invariance and norm-one evaluation of normalized Levi slices

The translated slice of Mœglin–Waldspurger I.2.17 uses the inverse half modulus.
Lapid's split-component covariance cancels it on the positive split centre, and
the character logarithm vanishes on the norm-one Levi.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open GroupScheme InducedInnerProductIntegrable

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {φ : AdelicGroupPoints F G → ℂ}

/-- The normalized restriction at any translate is left invariant under the
positive split centre of the Levi whenever `φ` has half-modulus covariance. -/
theorem normalizedLeviValue_splitComponent_mul (hφ : IsSplitComponentEquivariant p l φ)
    {a : AdelicGroupPoints F M} (ha : a ∈ RestrictionSplitCentre.canonicalSubgroup F M)
    (m : AdelicGroupPoints F M) (k : AdelicGroupPoints F G) :
    normalizedLeviValue p l φ (a * m) k = normalizedLeviValue p l φ m k := by
  unfold normalizedLeviValue
  rw [form_canonical_mul hφ ha, map_mul, parameterPower_mul, mul_mul_mul_comm,
    ← parameterPower_add, neg_add_cancel, parameterPower_zero, one_mul]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- On the norm-one Levi the normalizing factor is one, so the normalized
restriction is ordinary evaluation through the composite `M ⟶ P ⟶ G`. -/
theorem normalizedLeviValue_of_mem_normOne {m : AdelicGroupPoints F M}
    (hm : m ∈ normOneSubgroup F M) (k : AdelicGroupPoints F G) :
    normalizedLeviValue p l φ m k = φ (map F M G (l ≫ p) m * k) := by
  rw [normalizedLeviValue, parameterPower_map_of_mem_normOne _ l hm, one_mul, map_comp_apply]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

/-- The normalized Levi slice is left `A_M`-invariant for a half-modulus-equivariant
inducing function. On `M(𝔸)^1` it equals the ordinary slice for any function. -/
def NormalizedLeviSliceComparisonStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom],
    ∀ (p : P ⟶ G) (l : M ⟶ P) (φ : AdelicGroupPoints F G → ℂ),
      (IsSplitComponentEquivariant p l φ →
        ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F M,
          ∀ (m : AdelicGroupPoints F M) (k : AdelicGroupPoints F G),
            normalizedLeviValue p l φ (a * m) k = normalizedLeviValue p l φ m k) ∧
      (∀ m ∈ normOneSubgroup F M, ∀ k : AdelicGroupPoints F G,
        normalizedLeviValue p l φ m k = φ (map F M G (l ≫ p) m * k))

theorem normalizedLeviSliceComparison : NormalizedLeviSliceComparisonStatement := by
  intro F _ _ G P M _ _ _ _ _ _ p l φ
  exact ⟨fun hφ _ ha m k => normalizedLeviValue_splitComponent_mul hφ ha m k,
    fun _ hm k => normalizedLeviValue_of_mem_normOne hm k⟩

end Langlands.Global
