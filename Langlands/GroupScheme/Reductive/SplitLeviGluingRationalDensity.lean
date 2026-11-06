import Langlands.GroupScheme.Reductive.SplitLeviGluingDensity
import Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularization

/-! # The Levi graph cell on actual group-scheme rational points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))

local notation "HPoints" => (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)

local instance rationalTopology : TopologicalSpace HPoints := RationalZariski.topology H

local instance rationalSeparatelyContinuousMul : SeparatelyContinuousMul HPoints where
  continuous_const_mul {a} := by
    obtain ⟨φ, hφ⟩ := exists_comp_eq_mul_left a
    have h : (fun y : HPoints => a * y) = fun y => y ≫ φ :=
      funext fun y => (hφ y).symm
    rw [h]
    exact RationalZariski.continuous_comp φ
  continuous_mul_const {a} := by
    obtain ⟨φ, hφ⟩ := exists_comp_eq_mul_right a
    have h : (fun y : HPoints => y * a) = fun y => y ≫ φ :=
      funext fun y => (hφ y).symm
    rw [h]
    exact RationalZariski.continuous_comp φ

/-- The topological closure of rational points is exactly the inverse image of the
scheme-topological closure of their locations. -/
theorem closure_eq_rationalPointClosure (S : Set HPoints) :
    closure S = rationalPointClosure H S := by
  ext x
  exact closure_induced

/-- Left multiplication by the generated subgroup preserves the rational-point
closure of the three-factor cell. All closures in the interface are intrinsic. -/
theorem generated_mul_mem_rationalPointClosure_tripleProduct
    {I : Type v} (A B : I → Subgroup HPoints) (V T U : Subgroup HPoints)
    (hA : ∀ i, A i ≤ U)
    (hV : V = Subgroup.closure (⋃ i, (B i : Set HPoints)))
    (hTV : T ≤ Subgroup.normalizer (V : Set HPoints))
    (hTU : T ≤ Subgroup.normalizer (U : Set HPoints))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ B j, Commute a b)
    (hpair : ∀ i, (A i : Set HPoints) * (B i : Set HPoints) ⊆
      rationalPointClosure H ((B i : Set HPoints) * (T : Set HPoints) * (A i : Set HPoints))) :
    ∀ g ∈ Subgroup.closure
      ((⋃ i, (A i : Set HPoints)) ∪ (V : Set HPoints) ∪ (T : Set HPoints)),
      ∀ x ∈ rationalPointClosure H ((V : Set HPoints) * (T : Set HPoints) * (U : Set HPoints)),
        g * x ∈ rationalPointClosure H
          ((V : Set HPoints) * (T : Set HPoints) * (U : Set HPoints)) := by
  have hp : ∀ i, (A i : Set HPoints) * (B i : Set HPoints) ⊆
      closure ((B i : Set HPoints) * (T : Set HPoints) * (A i : Set HPoints)) := by
    simpa only [closure_eq_rationalPointClosure H] using hpair
  simpa only [closure_eq_rationalPointClosure H] using
    generated_mul_mem_closure_tripleProduct A B V T U hA hV hTV hTU hcomm hp

/-- The action on the rational-point closure, for the actual group scheme `H`. -/
@[instance_reducible]
def rationalTripleProductClosureAction
    {I : Type v} (A B : I → Subgroup HPoints) (V T U : Subgroup HPoints)
    (hA : ∀ i, A i ≤ U)
    (hV : V = Subgroup.closure (⋃ i, (B i : Set HPoints)))
    (hTV : T ≤ Subgroup.normalizer (V : Set HPoints))
    (hTU : T ≤ Subgroup.normalizer (U : Set HPoints))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ B j, Commute a b)
    (hpair : ∀ i, (A i : Set HPoints) * (B i : Set HPoints) ⊆
      rationalPointClosure H ((B i : Set HPoints) * (T : Set HPoints) * (A i : Set HPoints))) :
    MulAction (Subgroup.closure
      ((⋃ i, (A i : Set HPoints)) ∪ (V : Set HPoints) ∪ (T : Set HPoints)))
      (rationalPointClosure H ((V : Set HPoints) * (T : Set HPoints) * (U : Set HPoints))) where
  smul g x := ⟨g.1 * x.1,
    generated_mul_mem_rationalPointClosure_tripleProduct H A B V T U hA hV hTV hTU
      hcomm hpair g.1 g.2 x.1 x.2⟩
  one_smul x := Subtype.ext (one_mul x.1)
  mul_smul g h x := Subtype.ext (mul_assoc g.1 h.1 x.1)

/-- Density of the generated subgroup's locations implies density of the cell's
locations in the actual scheme. No algebraic closure or finite type premise is
needed beyond this explicit density assumption. -/
theorem dense_rationalPointImage_tripleProduct
    {I : Type v} (A B : I → Subgroup HPoints) (V T U : Subgroup HPoints)
    (hA : ∀ i, A i ≤ U)
    (hV : V = Subgroup.closure (⋃ i, (B i : Set HPoints)))
    (hTV : T ≤ Subgroup.normalizer (V : Set HPoints))
    (hTU : T ≤ Subgroup.normalizer (U : Set HPoints))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ B j, Commute a b)
    (hpair : ∀ i, (A i : Set HPoints) * (B i : Set HPoints) ⊆
      rationalPointClosure H ((B i : Set HPoints) * (T : Set HPoints) * (A i : Set HPoints)))
    (hgen : Dense (rationalPointImage H (Subgroup.closure
      ((⋃ i, (A i : Set HPoints)) ∪ (V : Set HPoints) ∪ (T : Set HPoints)) : Set HPoints))) :
    Dense (rationalPointImage H ((V : Set HPoints) * (T : Set HPoints) * (U : Set HPoints))) := by
  have hp : ∀ i, (A i : Set HPoints) * (B i : Set HPoints) ⊆
      closure ((B i : Set HPoints) * (T : Set HPoints) * (A i : Set HPoints)) := by
    simpa only [closure_eq_rationalPointClosure H] using hpair
  have hsub : rationalPointImage H (Subgroup.closure
      ((⋃ i, (A i : Set HPoints)) ∪ (V : Set HPoints) ∪ (T : Set HPoints)) : Set HPoints) ⊆
      closure (rationalPointImage H
        ((V : Set HPoints) * (T : Set HPoints) * (U : Set HPoints))) := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' := generated_subset_closure_tripleProduct A B V T U hA hV hTV hTU hcomm hp hg
    rw [closure_eq_rationalPointClosure H] at hg'
    exact hg'
  intro x
  have hx := closure_mono hsub (hgen x)
  simpa only [closure_closure] using hx

end Langlands.GroupScheme.LeviGluing
