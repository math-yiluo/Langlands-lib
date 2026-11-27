import Langlands.Algebra.LieEnvelopingSymbol
import Langlands.Algebra.LieCasimir
import Langlands.Representation.Archimedean.Kostant.Center

/-! # The enveloping algebra of an abelian Lie algebra as a polynomial ring -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Algebra.AbelianEnveloping

open Langlands.Algebra.UniversalEnveloping Langlands.Archimedean.Kostant
  Langlands.Algebra.LieWeightProjection Langlands.Algebra.LieEnvelopingSymbol MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {M : Type v} [LieRing M] [LieAlgebra k M]
  (hab : ∀ x y : M, ⁅x, y⁆ = 0)

local notation "U" => UniversalEnvelopingAlgebra k M
local notation "ι" => UniversalEnvelopingAlgebra.ι k

include hab in
theorem ι_commute (x y : M) : ι x * ι y = ι y * ι x := by
  have h := (UniversalEnvelopingAlgebra.ι k (L := M)).map_lie x y
  rw [hab, map_zero, Ring.lie_def] at h
  exact (sub_eq_zero.mp h.symm)

include hab in
/-- The enveloping algebra of an abelian Lie algebra is commutative: it equals its centre. -/
theorem mem_center (u : U) : u ∈ Subalgebra.center k U := by
  have hgen : Set.range (ι : M → U) ⊆ Subalgebra.center k U := by
    rintro _ ⟨y, rfl⟩
    exact mem_center_of_commute k M fun x => ι_commute hab x y
  have h := Algebra.adjoin_le hgen
  rw [LieCasimir.enveloping_adjoin_range] at h
  exact h trivial

variable {J : Type w} [Fintype J] [DecidableEq J] (c : Module.Basis J k M) {l : List J}
  (hl : l.Nodup) (hall : ∀ a, a ∈ l)

/-- The algebra map from the polynomial ring sending `X a` to the generator `ι (c a)`. -/
def toPoly : MvPolynomial J k →ₐ[k] Subalgebra.center k U :=
  aeval fun a => ⟨ι (c a), mem_center hab _⟩

include hl hall in
theorem toPoly_monomial (α : J →₀ ℕ) :
    (toPoly hab c (monomial α 1) : U) = orderedMonomial k M c l α := by
  classical
  let gen : J → Subalgebra.center k U := fun a => ⟨ι (c a), mem_center hab _⟩
  have h1 : toPoly hab c (monomial α 1) = ∏ a, gen a ^ α a := by
    rw [toPoly, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun a => pow_zero _)]
  have h2 : (l.map fun a => gen a ^ α a).prod = ∏ a, gen a ^ α a := by
    rw [← List.prod_toFinset _ hl]
    congr 1
    ext a
    simp [hall a]
  rw [orderedMonomial, word_expand_map, h1, ← h2]
  change (Subalgebra.val (Subalgebra.center k U)) (l.map fun a => gen a ^ α a).prod = _
  rw [map_list_prod, List.map_map]
  congr 1

include hl hall in
theorem pbwPoly_toPoly (p : MvPolynomial J k) :
    pbwPoly c hl hall (toPoly hab c p : U) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [show monomial α r = r • monomial α (1 : k) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul, Subalgebra.coe_smul, map_smul, toPoly_monomial hab c hl hall,
      pbwPoly_orderedMonomial]
  | add p q hp hq => rw [map_add, Subalgebra.coe_add, map_add, hp, hq]

include hl hall in
theorem toPoly_pbwPoly (u : U) : (toPoly hab c (pbwPoly c hl hall u) : U) = u := by
  let BU := orderedMonomialBasis c hl hall
  have h : (Subalgebra.val _).toLinearMap ∘ₗ (toPoly hab c).toLinearMap ∘ₗ pbwPoly c hl hall =
      LinearMap.id := by
    refine BU.ext fun α => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
      LinearMap.id_apply, BU, orderedMonomialBasis_apply, pbwPoly_orderedMonomial,
      toPoly_monomial hab c hl hall]
  exact LinearMap.congr_fun h u

include hl hall in
theorem toPoly_bijective : Function.Bijective (toPoly hab c) := by
  constructor
  · intro p q hpq
    rw [← pbwPoly_toPoly hab c hl hall p, ← pbwPoly_toPoly hab c hl hall q, hpq]
  · intro z
    exact ⟨pbwPoly c hl hall (z : U), Subtype.ext (toPoly_pbwPoly hab c hl hall z)⟩

/-- The enveloping algebra (equal to its centre) of an abelian Lie algebra with a finite basis is
the polynomial ring on the basis. -/
def polyEquiv : MvPolynomial J k ≃ₐ[k] Subalgebra.center k U :=
  AlgEquiv.ofBijective (toPoly hab c) (toPoly_bijective hab c hl hall)

theorem polyEquiv_symm_apply (z : Subalgebra.center k U) :
    (polyEquiv hab c hl hall).symm z = pbwPoly c hl hall (z : U) := by
  apply (polyEquiv hab c hl hall).injective
  rw [AlgEquiv.apply_symm_apply]
  exact Subtype.ext (toPoly_pbwPoly hab c hl hall z).symm

/-- The coefficients of the polynomial of a central element are its ordered PBW coordinates. -/
theorem coeff_polyEquiv_symm (z : Subalgebra.center k U) (α : J →₀ ℕ) :
    ((polyEquiv hab c hl hall).symm z).coeff α = (orderedMonomialBasis c hl hall).repr z α := by
  rw [polyEquiv_symm_apply, coeff_pbwPoly]

end Langlands.Algebra.AbelianEnveloping
