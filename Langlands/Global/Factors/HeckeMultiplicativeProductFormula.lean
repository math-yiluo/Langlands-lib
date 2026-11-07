import Langlands.Global.Factors.HeckeProductFormula

/-! # Actual multiplicative product formulas for Hecke characters -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeFunctionalEquation

universe u

variable {K : Type u} [Field K] [NumberField K]

local instance : DecidableEq (FinitePlace K) := Classical.decEq _
local instance : DecidableEq (InfinitePlace K) := Classical.decEq _

/-- A finite set controlling the Hecke character on the full product of local
integral units. -/
def multiplicativeIntegralControl (χ : HeckeCharacter K) : Finset (FinitePlace K) :=
  Classical.choose (exists_finset_mul_kernel (χ.onIdeles.comp (integralUnitIdeles K)))

theorem multiplicativeIntegralControl_spec (χ : HeckeCharacter K)
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ)
    (hx : ∀ v ∈ multiplicativeIntegralControl χ, x v = 1) :
    χ.onIdeles (integralUnitIdeles K x) = 1 :=
  Classical.choose_spec
    (exists_finset_mul_kernel (χ.onIdeles.comp (integralUnitIdeles K))) x hx

/-- The finite places where the value or inverse of an idele is nonintegral. -/
def nonunitPlaces (a : Ideles K) : Finset (FinitePlace K) :=
  nonintegralPlaces a.val.2 ∪ nonintegralPlaces a.inv.2

/-- At every other finite place the actual idele coordinate is an integral unit. -/
def integralUnitAt (a : Ideles K) (v : FinitePlace K) (hv : v ∉ nonunitPlaces a) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨a.val.2 v, integral_of_not_mem_nonintegralPlaces a.val.2 v
    (fun h => hv (Finset.mem_union_left _ h))⟩
  inv := ⟨a.inv.2 v, integral_of_not_mem_nonintegralPlaces a.inv.2 v
    (fun h => hv (Finset.mem_union_right _ h))⟩
  val_inv := Subtype.ext (congrArg (fun x : Adeles K => x.2 v) a.val_inv)
  inv_val := Subtype.ext (congrArg (fun x : Adeles K => x.2 v) a.inv_val)

/-- The actual finite product of the selected local idele coordinates. -/
def finiteMultiplicativePartialProduct (S : Finset (FinitePlace K)) (a : Ideles K) :
    Ideles K :=
  ∏ v ∈ S, finiteIdeleInclusion K v (finiteIdeleProjection K v a)

theorem finiteProjection_finiteMultiplicativePartialProduct
    (S : Finset (FinitePlace K)) (a : Ideles K) (v : FinitePlace K) :
    finiteProjection K v (finiteMultiplicativePartialProduct S a).val =
      if v ∈ S then a.val.2 v else 1 := by
  rw [finiteMultiplicativePartialProduct, Units.coe_prod, map_prod]
  change (∏ w ∈ S, (Pi.mulSingle w (a.val.2 w)) v) = _
  by_cases hv : v ∈ S
  · simp only [hv, ↓reduceIte]
    rw [Finset.prod_eq_single v]
    · exact Pi.mulSingle_eq_same v (a.val.2 v)
    · intro w _ hw
      exact Pi.mulSingle_eq_of_ne (Ne.symm hw) _
    · exact fun h => False.elim (h hv)
  · simp only [hv, ↓reduceIte]
    apply Finset.prod_eq_one
    intro w hw
    have hvw : v ≠ w := by
      intro h
      subst w
      exact hv hw
    exact Pi.mulSingle_eq_of_ne hvw _

theorem infiniteProjection_finiteMultiplicativePartialProduct
    (S : Finset (FinitePlace K)) (a : Ideles K) (v : InfinitePlace K) :
    infiniteProjection K v (finiteMultiplicativePartialProduct S a).val = 1 := by
  rw [finiteMultiplicativePartialProduct, Units.coe_prod, map_prod]
  change (∏ _w ∈ S, (1 : InfiniteCompletion K v)) = 1
  simp

/-- Any idele is the product of its infinite part and finitely many actual
finite components, modulo an integral tail in the character's kernel. -/
theorem multiplicative_product_atInfinity
    (χ : HeckeCharacter K) (a : Ideles K) (S : Finset (FinitePlace K))
    (hχ : multiplicativeIntegralControl χ ⊆ S) (ha : nonunitPlaces a ⊆ S) :
    χ.onIdeles a = χ.atInfinity ((ideleProductEquiv K a).1) *
      ∏ v ∈ S, χ.finiteComponent v (finiteIdeleProjection K v a) := by
  classical
  let r : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ :=
    fun v => if hv : v ∈ S then 1 else integralUnitAt a v (fun h => hv (ha h))
  have hr : χ.onIdeles (integralUnitIdeles K r) = 1 := by
    apply multiplicativeIntegralControl_spec
    intro v hv
    simp [r, hχ hv]
  have hdecomp : a =
      infiniteIdelesInclusion K ((ideleProductEquiv K a).1) *
        finiteMultiplicativePartialProduct S a * integralUnitIdeles K r := by
    apply Units.ext
    apply Prod.ext
    · funext v
      change a.val.1 v = a.val.1 v *
        infiniteProjection K v (finiteMultiplicativePartialProduct S a).val * 1
      rw [infiniteProjection_finiteMultiplicativePartialProduct, mul_one, mul_one]
    · apply RestrictedProduct.ext
      intro v
      change a.val.2 v = 1 *
        finiteProjection K v (finiteMultiplicativePartialProduct S a).val *
          ((r v).val : FiniteCompletion K v)
      rw [finiteProjection_finiteMultiplicativePartialProduct]
      by_cases hv : v ∈ S <;> simp [r, hv, integralUnitAt]
  calc
    χ.onIdeles a = χ.onIdeles
        (infiniteIdelesInclusion K ((ideleProductEquiv K a).1) *
          finiteMultiplicativePartialProduct S a * integralUnitIdeles K r) :=
      congrArg χ.onIdeles hdecomp
    _ = χ.atInfinity ((ideleProductEquiv K a).1) *
        χ.onIdeles (finiteMultiplicativePartialProduct S a) := by
      rw [map_mul, map_mul, hr, mul_one]
      rfl
    _ = _ := by
      rw [finiteMultiplicativePartialProduct, map_prod]
      rfl

/-- The infinite idele factor is the product of all actual infinite
single-coordinate idele inclusions. -/
theorem infinite_multiplicative_product_decomposition (a : Ideles K) :
    (∏ v : InfinitePlace K, infiniteIdeleInclusion K v (infiniteIdeleProjection K v a)) =
      infiniteIdelesInclusion K ((ideleProductEquiv K a).1) := by
  apply Units.ext
  rw [Units.coe_prod]
  change (∏ v : InfinitePlace K, (Pi.mulSingle v (a.val.1 v), (1 : FiniteAdeles K))) =
    (a.val.1, (1 : FiniteAdeles K))
  rw [← prod_mk_prod]
  apply Prod.ext
  · exact Finset.univ_prod_mulSingle a.val.1
  · simp

theorem infinite_multiplicative_product (χ : HeckeCharacter K) (a : Ideles K) :
    χ.atInfinity ((ideleProductEquiv K a).1) =
      ∏ v : InfinitePlace K, χ.infiniteComponent v (infiniteIdeleProjection K v a) := by
  change χ.onIdeles (infiniteIdelesInclusion K ((ideleProductEquiv K a).1)) = _
  rw [← infinite_multiplicative_product_decomposition, map_prod]
  rfl

/-- The full local product formula for the original Hecke character on every
actual idele. -/
theorem multiplicative_product
    (χ : HeckeCharacter K) (a : Ideles K) (S : Finset (FinitePlace K))
    (hχ : multiplicativeIntegralControl χ ⊆ S) (ha : nonunitPlaces a ⊆ S) :
    χ.onIdeles a =
      (∏ v : InfinitePlace K, χ.infiniteComponent v (infiniteIdeleProjection K v a)) *
        ∏ v ∈ S, χ.finiteComponent v (finiteIdeleProjection K v a) := by
  rw [multiplicative_product_atInfinity χ a S hχ ha, infinite_multiplicative_product]

/-- The multiplicative local product equals one on every principal idele,
using precisely the original local Hecke components. -/
theorem diagonal_multiplicative_product
    (χ : HeckeCharacter K) (g : Kˣ) (S : Finset (FinitePlace K))
    (hχ : multiplicativeIntegralControl χ ⊆ S) (hg : nonunitPlaces (diagonalUnits K g) ⊆ S) :
    (∏ v : InfinitePlace K,
      χ.infiniteComponent v (infiniteIdeleProjection K v (diagonalUnits K g))) *
      (∏ v ∈ S,
        χ.finiteComponent v (finiteIdeleProjection K v (diagonalUnits K g))) = 1 :=
  (multiplicative_product χ (diagonalUnits K g) S hχ hg).symm.trans
    (χ.onIdeles_diagonalUnits g)

end Langlands.Global.HeckeFunctionalEquation
