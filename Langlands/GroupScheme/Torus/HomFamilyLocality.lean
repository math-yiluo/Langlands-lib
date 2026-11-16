import Langlands.GroupScheme.Torus.HomFamilyRigidity

/-! # Matrix descriptions of split-torus families on open neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomFamily

open splitTorus TorusConjugation

variable {S : Scheme.{u}} {T D : GroupScheme S} {U V : Over S}
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (eT : T ≅ splitTorus S I) (eD : D ≅ splitTorus S J)
  {F : ∀ W : Over S, (W ⟶ U) → (W ⟶ T.X) → (W ⟶ D.X)}
  (hF : IsHomFamily F)

include hF

/-- A pointwise fixed exponent matrix determines the family on a supplied
parameter subtest, not just on the entire parameter scheme. -/
theorem actsBy_of_forall_actsAtPoint_on (m : Matrix J I ℤ) (a : V ⟶ U)
    (h : ∀ x : V.left, ActsAtPoint eT eD F m (a.left x)) :
    ActsBy eT eD F m a := by
  apply actsBy_of_forall_affine eT eD hF
  intro A s b x
  let ρ := b ≫ a
  have hd : ∀ l, ((chartFamily eT eD hF ρ).coeffs l).coeff (extMatrix m l) = 1 := by
    intro l
    have hu : IsUnit (((chartFamily eT eD hF ρ).coeffs l).coeff (extMatrix m l)) := by
      by_contra hn
      obtain ⟨P, hP, hnP⟩ := exists_max_ideal_of_mem_nonunits hn
      have hx := h (b.left ⟨P, hP.isPrime⟩)
      change ActsAtPoint eT eD F m (ρ.left ⟨P, hP.isPrime⟩) at hx
      exact (actsAtPoint_chart_iff eT eD hF ρ m ⟨P, hP.isPrime⟩).mp hx l hnP
    have hid := (chartFamily eT eD hF ρ).isIdempotentElem_coeff l (extMatrix m l)
    exact hu.mul_left_cancel (by rw [hid.eq, mul_one])
  have hb := (actsBy_chart_iff eT eD hF ρ m).mpr hd _ (𝟙 _) x
  simpa only [ρ, Category.id_comp] using hb

/-- Every parameter point has an open neighbourhood on which the split-torus
family is given by one integer matrix on all relative tests. -/
theorem exists_open_actsBy (x : U.left) :
    ∃ W : U.left.Opens, x ∈ W ∧
      ∃ m : Matrix J I ℤ, ActsBy eT eD F m (overHom (U := U) W.ι) := by
  obtain ⟨m, hm⟩ := exists_actsAtPoint eT eD hF x
  have hloc := isLocallyConstant_actsAtPoint eT eD hF m
  rw [IsLocallyConstant.iff_exists_open] at hloc
  obtain ⟨O, hO, hx, hconst⟩ := hloc x
  let W : U.left.Opens := ⟨O, hO⟩
  refine ⟨W, hx, m, actsBy_of_forall_actsAtPoint_on eT eD hF m
    (overHom (U := U) W.ι) ?_⟩
  intro y
  change ActsAtPoint eT eD F m y.val
  rw [hconst y.val y.property]
  exact hm

/-- A neighbourhood and integer matrix chosen with their full all-test
description. The choice is local at the supplied parameter point. -/
def matrixNeighbourhood (x : U.left) :
    Σ W : U.left.Opens,
      {m : Matrix J I ℤ // x ∈ W ∧
        ActsBy eT eD F m (overHom (U := U) W.ι)} := by
  let h := exists_open_actsBy eT eD hF x
  let W := h.choose
  have hW := h.choose_spec
  exact ⟨W, hW.2.choose, hW.1, hW.2.choose_spec⟩

end Langlands.GroupScheme.HomFamily
