import Langlands.GroupScheme.Dynamic.TensorPoints
import Langlands.GroupScheme.Dynamic.ProperLocalExtension
import Langlands.GroupScheme.Dynamic.BaseChangeIntegrality

/-! # Extension of points of a dynamic parabolic quotient through a proper comparison

This is the core of the proof of CGP Proposition C.1.6 over a field `k`, for a corepresented
smooth affine group `G = Spec B` with cocharacter `χ` and quotient `q : G ⟶ Q` by `P_G(χ)`.
The comparison data over a field extension `Ω` are: a homomorphism `π : G_Ω ⟶ H`, a proper
quotient `q₀ : H ⟶ Q₀` by `P_H(χ'')`, and a map `φ : Q_Ω ⟶ Q₀` compatible with `π`. Assume
the kernel condition, rational points of geometrically reduced algebras, simultaneous density
of rational points, and the DVR property of `Ω ⊗[k] R`. Then every point of `Q` over
`Frac R` extends over `R`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

open CommutativeAlgebra.GradedDVRIntegrality Dynamic.OppositeCell

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  [Smooth (groupScheme F e).X.hom] [IsAffineHom (groupScheme F e).X.hom]
  [IsAffine (groupScheme F e).X.left] [Algebra.FiniteType k B]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)
  {Q : Over (Spec (CommRingCat.of k))} (q : (groupScheme F e).X ⟶ Q)
  (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ (groupScheme F e).X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T)
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  {Ω : Type u} [Field Ω] [Algebra k Ω]
  {H : GroupScheme (Spec (CommRingCat.of Ω))} [Smooth H.X.hom] [IsAffineHom H.X.hom]
  [IsAffine H.X.left]
  (π : baseChangeGroup F e Ω ⟶ H) [Surjective π.hom.hom.left]
  (χ'' : (Gm (Spec (CommRingCat.of Ω))).toGrp ⟶ H)
  (hχ : opposite χ'' = Dynamic.baseChangeCocharacter (scalarMap k Ω) (opposite χ) ≫ π)
  {Q₀ : Over (Spec (CommRingCat.of Ω))} (q₀ : H.X ⟶ Q₀)
  (hf₀ : ∀ (T : Over (Spec (CommRingCat.of Ω))) (g h : T ⟶ H.X),
    g ≫ q₀ = h ≫ q₀ ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ'').carrier T)
  [Flat q₀.left] [Surjective q₀.left] [QuasiCompact q₀.left] [IsProper Q₀.hom]
  (φ : (Over.pullback (scalarMap k Ω)).obj Q ⟶ Q₀)
  (hφ : (Over.pullback (scalarMap k Ω)).map q ≫ φ = π.hom.hom ≫ q₀)

include hf hχ hf₀ hφ in
/-- **Extension through a proper comparison.** -/
theorem exists_extension_of_comparison
    (hker : ∀ a : B →ₐ[k] k, IsContracting (coaction (opposite χ)).hom (counitAlgHom e) a →
      bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp a) ≫ π.hom.hom =
        bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp (counitAlgHom e)) ≫ π.hom.hom →
      a = counitAlgHom e)
    (hrat : ∀ (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra.FiniteType k R']
      [Nontrivial R'] [Algebra.IsGeometricallyReduced k R'], Nonempty (R' →ₐ[k] k))
    (hdense : ∀ (K₁ K₂ : Type u) [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]
      (f₁ : K₁ ⊗[k] B) (f₂ : K₂ ⊗[k] B), f₁ ≠ 0 → f₂ ≠ 0 →
        ∃ a : B →ₐ[k] k, Algebra.TensorProduct.map (AlgHom.id k K₁) a f₁ ≠ 0 ∧
          Algebra.TensorProduct.map (AlgHom.id k K₂) a f₂ ≠ 0)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
    (hF : Algebra.IsGeometricallyReduced k (ResidueField R))
    [IsDomain (Ω ⊗[k] R)] [IsDiscreteValuationRing (Ω ⊗[k] R)]
    (hfrac : @IsFractionRing (Ω ⊗[k] R) _ (Ω ⊗[k] FractionRing R) _
      (Algebra.TensorProduct.map (AlgHom.id k Ω)
        (IsScalarTower.toAlgHom k R (FractionRing R))).toRingHom.toAlgebra)
    (x : algOver k (FractionRing R) ⟶ Q) :
    ∃ xR : algOver k R ⟶ Q,
      algOverHom (IsScalarTower.toAlgHom k R (FractionRing R)) ≫ xR = x := by
  classical
  -- Translation of `x` into the cell.
  obtain ⟨f, hf0, hfx⟩ := exists_ne_zero_eq_mul_comp χ q hf (FractionRing R) x
  -- The comparison point over `Ω ⊗ Frac R` and its extension over `Ω ⊗ R`.
  let ιK := Algebra.TensorProduct.map (AlgHom.id k Ω)
    (IsScalarTower.toAlgHom k R (FractionRing R))
  let _ : Algebra (Ω ⊗[k] R) (Ω ⊗[k] FractionRing R) := ιK.toRingHom.toAlgebra
  have : IsFractionRing (Ω ⊗[k] R) (Ω ⊗[k] FractionRing R) := hfrac
  let _ : Field (Ω ⊗[k] FractionRing R) := IsFractionRing.toField (Ω ⊗[k] R)
  have : IsScalarTower Ω (Ω ⊗[k] R) (Ω ⊗[k] FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun ω => by
      change ω ⊗ₜ (1 : FractionRing R) = ιK (ω ⊗ₜ 1)
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
  let x'' : algOver Ω (Ω ⊗[k] FractionRing R) ⟶ Q₀ := tensorPoint Ω x ≫ φ
  obtain ⟨xA, hxA⟩ :=
    exists_extension_of_isProper Q₀ (Ω ⊗[k] R) (Ω ⊗[k] FractionRing R) x''
  -- The closed point and its translation into the cell of `H`.
  let res : Ω ⊗[k] R →ₐ[Ω] ResidueField (Ω ⊗[k] R) :=
    IsScalarTower.toAlgHom Ω (Ω ⊗[k] R) (ResidueField (Ω ⊗[k] R))
  let x₀ : algOver Ω (ResidueField (Ω ⊗[k] R)) ⟶ Q₀ := algOverHom res ≫ xA
  obtain ⟨f', hf0', hfx'⟩ :=
    exists_ne_zero_eq_mul_comp_baseChange π χ'' q₀ hf₀ (ResidueField (Ω ⊗[k] R)) x₀
  -- A rational point good for both.
  obtain ⟨a, ha, ha'⟩ := hdense _ _ f f' hf0 hf0'
  have ha₁ : evalMap (FractionRing R) a f ≠ 0 := by
    rw [evalMap_apply]
    exact (LinearEquiv.map_ne_zero_iff _).2 ha
  have ha₂ : evalMap (ResidueField (Ω ⊗[k] R)) a f' ≠ 0 := by
    rw [evalMap_apply]
    exact (LinearEquiv.map_ne_zero_iff _).2 ha'
  obtain ⟨u, hu, hxu⟩ := hfx a ha₁
  obtain ⟨u₀, hu₀, hxu₀⟩ := hfx' a ha₂
  -- The extended point is a translate of a point of `U_H(χ''⁻¹)` over `Ω ⊗ R`.
  let aA := bcPoint F e Ω (Ω ⊗[k] R) ((Algebra.ofId k (Ω ⊗[k] R)).comp a) ≫ π.hom.hom
  let y := Dynamic.flagQuotientAct H (Dynamic.parabolic χ'') q₀ hf₀ aA⁻¹ xA
  have hy0 : algOverHom res ≫ y = u₀ ≫ q₀ := by
    rw [Dynamic.flagQuotientAct_naturality, GrpObj.comp_inv, ← Category.assoc,
      algOverHom_comp_bcPoint]
    have hc : (res.restrictScalars k).comp ((Algebra.ofId k (Ω ⊗[k] R)).comp a) =
        (Algebra.ofId k (ResidueField (Ω ⊗[k] R))).comp a := by
      rw [← AlgHom.comp_assoc]
      congr 1
    rw [hc]
    change Dynamic.flagQuotientAct H (Dynamic.parabolic χ'') q₀ hf₀ _ x₀ = _
    rw [hxu₀, Dynamic.flagQuotientAct_lift, inv_mul_cancel_left]
  have hyC : Set.range y.left ⊆ cell χ'' q₀ :=
    range_subset_of_residue (Ω ⊗[k] R) y (isOpen_cell χ'' q₀ hf₀) (by
      rw [hy0]
      exact range_subset_cell χ'' q₀ hu₀)
  obtain ⟨u'', hu'', hyu''⟩ := exists_mem_unipotent χ'' q₀ hf₀ y hyC
  have hxA' : xA = (aA * u'') ≫ q₀ := by
    rw [← Dynamic.flagQuotientAct_lift H (Dynamic.parabolic χ'') q₀ hf₀, hyu'']
    have := Dynamic.flagQuotientAct_inv_cancel H (Dynamic.parabolic χ'') q₀ hf₀ aA⁻¹ xA
    rw [inv_inv] at this
    exact this.symm
  -- Comparison of the two points of `U_H(χ''⁻¹)` over `Ω ⊗ Frac R`.
  let ιΩ := IsScalarTower.toAlgHom Ω (Ω ⊗[k] R) (Ω ⊗[k] FractionRing R)
  let c := bcPoint F e Ω (Ω ⊗[k] FractionRing R)
    ((Algebra.ofId k (Ω ⊗[k] FractionRing R)).comp a) ≫ π.hom.hom
  let v₁ := tensorGPoint Ω u ≫ π.hom.hom
  let v₂ := algOverHom ιΩ ≫ u''
  have h1 : x'' = (c * v₁) ≫ q₀ := by
    have e2 : (tensorGPoint Ω (ofAlgHom F e ((Algebra.ofId k (FractionRing R)).comp a) * u) ≫
        π.hom.hom) ≫ q₀ = (c * v₁) ≫ q₀ := by
      rw [tensorGPoint_mul, MonObj.mul_comp, tensorGPoint_ofAlgHom_ofId]
    refine Eq.trans ?_ e2
    change tensorPoint Ω x ≫ φ = _
    rw [hxu, tensorPoint_comp, Category.assoc, hφ, tensorPoint_eq_tensorGPoint]
    exact (Category.assoc _ _ _).symm
  have h2 : x'' = (c * v₂) ≫ q₀ := by
    rw [← hxA, hxA', ← Category.assoc, MonObj.comp_mul, ← Category.assoc,
      algOverHom_comp_bcPoint]
    congr 4
    rw [← AlgHom.comp_assoc]
    congr 1
    exact AlgHom.ext fun r => (ιΩ.restrictScalars k).commutes r
  have hv₁ : v₁ ∈ (Dynamic.unipotent (opposite χ'')).carrier _ := by
    rw [hχ]
    exact Dynamic.unipotent_le_comap _ π _ (tensorGPoint_mem_unipotent _ hu)
  have hv₂ : v₂ ∈ (Dynamic.unipotent (opposite χ'')).carrier _ :=
    (Dynamic.unipotent (opposite χ'')).comp_mem _ hu''
  have hv : v₁ = v₂ := by
    have hP : v₁⁻¹ * v₂ ∈ (Dynamic.parabolic χ'').carrier _ := by
      have := (hf₀ _ (c * v₁) (c * v₂)).1 (h1.symm.trans h2)
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left] at this
    have hq : (v₁⁻¹ * v₂) ≫ q₀ = 1 ≫ q₀ :=
      ((hf₀ _ 1 (v₁⁻¹ * v₂)).2 (by rwa [inv_one, one_mul])).symm
    have h := eq_of_mem_unipotent χ'' q₀ hf₀
      (mul_mem (inv_mem hv₁) hv₂) (one_mem _) hq
    exact inv_mul_eq_one.1 h
  -- The integrality hypothesis of the bridge.
  have hint : ∀ g : Γ(H.X.left, ⊤), Dynamic.AffineChart.pointRing
      (bcPoint F e Ω (Ω ⊗[k] FractionRing R)
        (Algebra.TensorProduct.includeRight.comp (pointAlgHom u)) ≫ π.hom.hom) g ∈
      ιK.range := by
    intro g
    change Dynamic.AffineChart.pointRing v₁ g ∈ _
    rw [hv, Dynamic.AffineChart.pointRing_comp]
    refine ⟨Dynamic.AffineChart.pointRing u'' g, ?_⟩
    change _ = (Dynamic.AffineChart.pointRing u'' ≫
      Spec.preimage (Spec.map (CommRingCat.ofHom ιΩ.toRingHom))) g
    rw [Spec.preimage_map]
    rfl
  obtain ⟨uR, -, huRu⟩ :=
    exists_point_of_baseChange_comparison π (opposite χ) hker hF hrat u hu hint
  refine ⟨(ofAlgHom F e ((Algebra.ofId k R).comp a) * uR) ≫ q, ?_⟩
  rw [← Category.assoc, MonObj.comp_mul, algOverHom_comp_ofAlgHom_ofId, hxu]
  congr 2

end Corepresented

end Langlands.GroupScheme
