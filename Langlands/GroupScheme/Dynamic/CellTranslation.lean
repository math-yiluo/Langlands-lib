import Langlands.GroupScheme.Dynamic.FieldPointBasicOpen
import Langlands.GroupScheme.Dynamic.OppositeCellPoints
import Langlands.GroupScheme.Dynamic.FlagQuotientAction

/-! # Moving a field point of a dynamic parabolic quotient into the opposite cell

Let `G = Spec B` be a smooth affine corepresented group over a field `k`, `χ` a cocharacter, and
`q : G ⟶ Q` a flat surjective quasi-compact map whose fibers are the right cosets of `P_G(χ)`.
For a point `x` of `Q` over a field extension `K` of `k`, there is a nonzero `f ∈ K ⊗[k] B`
such that every `k`-point `a` of `G` with `(a ⊗ K)(f) ≠ 0` satisfies `x = q(a u)` for some
`u ∈ U_G(χ⁻¹)(K)`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  [Smooth (groupScheme F e).X.hom] [IsAffineHom (groupScheme F e).X.hom]
  [IsAffine (groupScheme F e).X.left]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)
  {Q : Over (Spec (CommRingCat.of k))} (q : (groupScheme F e).X ⟶ Q)
  (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ (groupScheme F e).X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T)
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]

include hf in
/-- **Translation into the opposite cell.** A point `x` of `Q` over a field `K` is `q(a u)`
with `u ∈ U_G(χ⁻¹)(K)` for every `k`-point `a` of `G` outside the zero locus of some nonzero
`f ∈ K ⊗[k] B`. -/
theorem exists_ne_zero_eq_mul_comp (K : Type u) [Field K] [Algebra k K]
    (x : algOver k K ⟶ Q) :
    ∃ f : K ⊗[k] B, f ≠ 0 ∧ ∀ a : B →ₐ[k] k, evalMap K a f ≠ 0 →
      ∃ u : algOver k K ⟶ (groupScheme F e).X,
        u ∈ (Dynamic.unipotent (Dynamic.OppositeCell.opposite χ)).carrier _ ∧
          x = (ofAlgHom F e ((Algebra.ofId k K).comp a) * u) ≫ q := by
  let g₀ : algOver k (K ⊗[k] B) ⟶ (groupScheme F e).X :=
    ofAlgHom F e Algebra.TensorProduct.includeRight
  let p₀ : algOver k (K ⊗[k] B) ⟶ algOver k K := algOverHom Algebra.TensorProduct.includeLeft
  let y := Dynamic.flagQuotientAct (groupScheme F e) (Dynamic.parabolic χ) q hf g₀⁻¹ (p₀ ≫ x)
  let O : Set (Spec (CommRingCat.of (K ⊗[k] B))) :=
    y.left ⁻¹' Dynamic.OppositeCell.cell χ q
  have hO : IsOpen O :=
    (Dynamic.OppositeCell.isOpen_cell χ q hf).preimage y.left.continuous
  have hne : O.Nonempty := by
    obtain ⟨K', _, _, β, y', hβy⟩ := exists_lift_of_surjective q x
    let ψ : K ⊗[k] B →ₐ[k] K' :=
      Algebra.TensorProduct.lift β (pointAlgHom y') fun _ _ => Commute.all _ _
    have hg : algOverHom ψ ≫ g₀ = y' := by
      rw [algOverHom_comp_ofAlgHom, Algebra.TensorProduct.lift_comp_includeRight',
        ofAlgHom_pointAlgHom]
    have hp : algOverHom ψ ≫ p₀ = algOverHom β := by
      rw [algOverHom_comp, Algebra.TensorProduct.lift_comp_includeLeft]
    have hy : algOverHom ψ ≫ y = (1 : algOver k K' ⟶ (groupScheme F e).X) ≫ q := by
      rw [Dynamic.flagQuotientAct_naturality, GrpObj.comp_inv, hg, ← Category.assoc, hp, hβy,
        Dynamic.flagQuotientAct_lift, inv_mul_cancel]
    obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of K')) := inferInstance
    refine ⟨(algOverHom ψ).left t, ?_⟩
    have h := Dynamic.OppositeCell.range_one_subset_cell χ q (T := algOver k K') ⟨t, rfl⟩
    rw [← hy] at h
    exact h
  obtain ⟨f, hf0, hfO⟩ := exists_ne_zero_range_subset O hO hne
  refine ⟨f, hf0, fun a ha => ?_⟩
  let a' := ofAlgHom F e ((Algebra.ofId k K).comp a)
  have hc : algOverHom (evalMap K a) ≫ y =
      Dynamic.flagQuotientAct (groupScheme F e) (Dynamic.parabolic χ) q hf a'⁻¹ x := by
    have hg : algOverHom (evalMap K a) ≫ g₀ = a' := by
      rw [algOverHom_comp_ofAlgHom]
      congr 1
      ext b
      change evalMap K a (1 ⊗ₜ b) = _
      rw [evalMap_tmul, one_mul]
      rfl
    have hp : algOverHom (evalMap K a) ≫ p₀ = 𝟙 _ := by
      rw [algOverHom_comp, ← algOverHom_id]
      congr 1
      ext l
      change evalMap K a (l ⊗ₜ 1) = l
      rw [evalMap_tmul, map_one, map_one, mul_one]
    rw [Dynamic.flagQuotientAct_naturality, GrpObj.comp_inv, hg, ← Category.assoc, hp,
      Category.id_comp]
  have hrange : Set.range (Dynamic.flagQuotientAct (groupScheme F e) (Dynamic.parabolic χ) q hf
      a'⁻¹ x).left ⊆ Dynamic.OppositeCell.cell χ q := by
    rw [← hc]
    rintro _ ⟨t, rfl⟩
    exact hfO K (evalMap K a).toRingHom ha ⟨t, rfl⟩
  obtain ⟨u, hu, huq⟩ := Dynamic.OppositeCell.exists_mem_unipotent χ q hf _ hrange
  refine ⟨u, hu, ?_⟩
  rw [← Dynamic.flagQuotientAct_lift (groupScheme F e) (Dynamic.parabolic χ) q hf, huq]
  have := Dynamic.flagQuotientAct_inv_cancel (groupScheme F e) (Dynamic.parabolic χ) q hf a'⁻¹ x
  rw [inv_inv] at this
  exact this.symm

end Corepresented

end Langlands.GroupScheme
