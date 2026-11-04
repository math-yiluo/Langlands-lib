import Langlands.GroupScheme.Dynamic.CellTranslation

/-! # Translation into the opposite cell through a homomorphism out of a base change

Let `G = Spec B` be a corepresented group over a field `k`, `Ω` a field extension of `k`, and
`π : G_Ω ⟶ H` a homomorphism with surjective underlying map to a smooth affine `Ω`-group `H`
with a cocharacter `χ''`. Let `q₀ : H ⟶ Q₀` be a flat surjective quasi-compact map whose fibers
are the right cosets of `P_H(χ'')`. For a point `x₀` of `Q₀` over a field `κ'` (over `Ω`), there
is a nonzero `f ∈ κ' ⊗[k] B` such that every `k`-point `a` of `G` with `(κ' ⊗ a)(f) ≠ 0`
satisfies `x₀ = q₀(π(a_Ω) u'')` for some `u'' ∈ U_H(χ''⁻¹)(κ')`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {Ω : Type u} [Field Ω] [Algebra k Ω]

section Naturality

variable {A A' : Type u} [CommRing A] [Algebra k A] [Algebra Ω A] [IsScalarTower k Ω A]
  [CommRing A'] [Algebra k A'] [Algebra Ω A'] [IsScalarTower k Ω A']

/-- Base-changed points are natural in the `Ω`-algebra. -/
theorem algOverHom_comp_bcPoint (ψ : A →ₐ[Ω] A') (φ : B →ₐ[k] A) :
    algOverHom ψ ≫ bcPoint F e Ω A φ = bcPoint F e Ω A' ((ψ.restrictScalars k).comp φ) := by
  apply (baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) (testOver Ω A')).injective
  rw [baseChangePointsEquiv_naturality, bcPoint, bcPoint, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ 𝟙 _ ≫ Spec.map _ = 𝟙 _ ≫ Spec.map _
  rw [Category.id_comp, Category.id_comp]
  exact (Spec.map_comp _ _).symm

/-- A point of `G_Ω` is the base change of its underlying `k`-point. -/
theorem bcPoint_basePoint (z : testOver Ω A ⟶ (baseChangeGroup F e Ω).X) :
    bcPoint F e Ω A (pointAlgHom (basePoint z)) = z := by
  apply (baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) (testOver Ω A)).injective
  rw [bcPoint, MulEquiv.apply_symm_apply, ofAlgHom_pointAlgHom, basePoint, ← Category.assoc]
  have : testOverInv (k := k) Ω A ≫ testOverHom (k := k) Ω A = 𝟙 _ :=
    Over.OverMorphism.ext (Category.id_comp _)
  rw [this, Category.id_comp]

end Naturality

variable {H : GroupScheme (Spec (CommRingCat.of Ω))} [Smooth H.X.hom] [IsAffineHom H.X.hom]
  [IsAffine H.X.left]
  (π : baseChangeGroup F e Ω ⟶ H) [Surjective π.hom.hom.left]
  (χ'' : (Gm (Spec (CommRingCat.of Ω))).toGrp ⟶ H)
  {Q₀ : Over (Spec (CommRingCat.of Ω))} (q₀ : H.X ⟶ Q₀)
  (hf₀ : ∀ (T : Over (Spec (CommRingCat.of Ω))) (g h : T ⟶ H.X),
    g ≫ q₀ = h ≫ q₀ ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ'').carrier T)
  [Flat q₀.left] [Surjective q₀.left] [QuasiCompact q₀.left]

variable (Ω) in
/-- The evaluation `κ' ⊗[k] B → κ'` at a `k`-point, as an `Ω`-algebra map. -/
def evalMapOver (κ' : Type u) [Field κ'] [Algebra Ω κ'] [Algebra k κ'] [IsScalarTower k Ω κ']
    (a : B →ₐ[k] k) : κ' ⊗[k] B →ₐ[Ω] κ' :=
  Algebra.TensorProduct.lift (AlgHom.id Ω κ') ((Algebra.ofId k κ').comp a) fun _ _ =>
    Commute.all _ _

include hf₀ in
/-- **Translation into the opposite cell of `H`.** -/
theorem exists_ne_zero_eq_mul_comp_baseChange (κ' : Type u) [Field κ'] [Algebra Ω κ']
    [Algebra k κ'] [IsScalarTower k Ω κ'] (x₀ : algOver Ω κ' ⟶ Q₀) :
    ∃ f : κ' ⊗[k] B, f ≠ 0 ∧ ∀ a : B →ₐ[k] k, evalMap κ' a f ≠ 0 →
      ∃ u'' : algOver Ω κ' ⟶ H.X,
        u'' ∈ (Dynamic.unipotent (Dynamic.OppositeCell.opposite χ'')).carrier _ ∧
          x₀ = ((bcPoint F e Ω κ' ((Algebra.ofId k κ').comp a) ≫ π.hom.hom) * u'') ≫ q₀ := by
  let g₀ : algOver Ω (κ' ⊗[k] B) ⟶ H.X :=
    bcPoint F e Ω (κ' ⊗[k] B) Algebra.TensorProduct.includeRight ≫ π.hom.hom
  let p₀ : algOver Ω (κ' ⊗[k] B) ⟶ algOver Ω κ' :=
    algOverHom (Algebra.TensorProduct.includeLeft : κ' →ₐ[Ω] κ' ⊗[k] B)
  let y := Dynamic.flagQuotientAct H (Dynamic.parabolic χ'') q₀ hf₀ g₀⁻¹ (p₀ ≫ x₀)
  let O : Set (Spec (CommRingCat.of (κ' ⊗[k] B))) :=
    y.left ⁻¹' Dynamic.OppositeCell.cell χ'' q₀
  have hO : IsOpen O :=
    (Dynamic.OppositeCell.isOpen_cell χ'' q₀ hf₀).preimage y.left.continuous
  have hne : O.Nonempty := by
    obtain ⟨K₁, _, _, β₁, h₁, hh₁⟩ := exists_lift_of_surjective q₀ x₀
    obtain ⟨K₂, _, _, β₂, h₂, hh₂⟩ := exists_lift_of_surjective π.hom.hom h₁
    let _ : Algebra k K₂ := Algebra.compHom K₂ (algebraMap k Ω)
    have : IsScalarTower k Ω K₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let γ : B →ₐ[k] K₂ := pointAlgHom (basePoint h₂)
    let ψ : κ' ⊗[k] B →ₐ[Ω] K₂ :=
      Algebra.TensorProduct.lift (β₂.comp β₁) γ fun _ _ => Commute.all _ _
    have hg : algOverHom ψ ≫ g₀ = algOverHom β₂ ≫ h₁ := by
      rw [← Category.assoc, algOverHom_comp_bcPoint, hh₂, ← bcPoint_basePoint h₂]
      congr 2
      exact Algebra.TensorProduct.lift_comp_includeRight _ _ _
    have hp : algOverHom ψ ≫ p₀ = algOverHom β₂ ≫ algOverHom β₁ := by
      rw [algOverHom_comp, algOverHom_comp, Algebra.TensorProduct.lift_comp_includeLeft]
    have hy : algOverHom ψ ≫ y = (1 : algOver Ω K₂ ⟶ H.X) ≫ q₀ := by
      rw [Dynamic.flagQuotientAct_naturality, GrpObj.comp_inv, hg, ← Category.assoc, hp,
        Category.assoc, hh₁, ← Category.assoc, Dynamic.flagQuotientAct_lift, inv_mul_cancel]
    obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of K₂)) := inferInstance
    refine ⟨(algOverHom ψ).left t, ?_⟩
    have h := Dynamic.OppositeCell.range_one_subset_cell χ'' q₀ (T := algOver Ω K₂) ⟨t, rfl⟩
    rw [← hy] at h
    exact h
  obtain ⟨f, hf0, hfO⟩ := exists_ne_zero_range_subset O hO hne
  refine ⟨f, hf0, fun a ha => ?_⟩
  let a'' := bcPoint F e Ω κ' ((Algebra.ofId k κ').comp a) ≫ π.hom.hom
  have hev : (evalMapOver Ω κ' a).toRingHom = (evalMap κ' a).toRingHom := by
    refine RingHom.ext fun m => ?_
    induction m with
    | tmul l b =>
      change evalMapOver Ω κ' a (l ⊗ₜ b) = evalMap κ' a (l ⊗ₜ b)
      rw [evalMapOver, Algebra.TensorProduct.lift_tmul, evalMap_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hc : algOverHom (evalMapOver Ω κ' a) ≫ y =
      Dynamic.flagQuotientAct H (Dynamic.parabolic χ'') q₀ hf₀ a''⁻¹ x₀ := by
    have hg : algOverHom (evalMapOver Ω κ' a) ≫ g₀ = a'' := by
      rw [← Category.assoc, algOverHom_comp_bcPoint]
      congr 2
      ext b
      change evalMapOver Ω κ' a (1 ⊗ₜ b) = _
      rw [evalMapOver, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    have hp : algOverHom (evalMapOver Ω κ' a) ≫ p₀ = 𝟙 _ := by
      rw [algOverHom_comp, ← algOverHom_id]
      congr 1
      ext l
      change evalMapOver Ω κ' a (l ⊗ₜ 1) = l
      rw [evalMapOver, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    rw [Dynamic.flagQuotientAct_naturality, GrpObj.comp_inv, hg, ← Category.assoc, hp,
      Category.id_comp]
  have hrange : Set.range (Dynamic.flagQuotientAct H (Dynamic.parabolic χ'') q₀ hf₀
      a''⁻¹ x₀).left ⊆ Dynamic.OppositeCell.cell χ'' q₀ := by
    rw [← hc]
    rintro _ ⟨t, rfl⟩
    have := hfO κ' (evalMap κ' a).toRingHom ha ⟨t, rfl⟩
    rw [← hev] at this
    exact this
  obtain ⟨u'', hu'', huq⟩ := Dynamic.OppositeCell.exists_mem_unipotent χ'' q₀ hf₀ _ hrange
  refine ⟨u'', hu'', ?_⟩
  rw [← Dynamic.flagQuotientAct_lift H (Dynamic.parabolic χ'') q₀ hf₀, huq]
  have := Dynamic.flagQuotientAct_inv_cancel H (Dynamic.parabolic χ'') q₀ hf₀ a''⁻¹ x₀
  rw [inv_inv] at this
  exact this.symm

end Corepresented

end Langlands.GroupScheme
