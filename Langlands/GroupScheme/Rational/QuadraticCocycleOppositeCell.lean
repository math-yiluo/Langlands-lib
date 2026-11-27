import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Rational.FiniteGaloisCocycleFactorization
import Langlands.GroupScheme.CocycleCohomology

/-! # Quadratic cocycles in an opposite cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

set_option backward.isDefEq.respectTransparency false

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]
  {G T : GroupScheme (Spec (CommRingCat.of F))}

private abbrev CoefficientPoints (G : GroupScheme (Spec (CommRingCat.of F))) :=
  G.affinePoints (CommAlgCat.of F L)

omit [FiniteDimensional F L] [IsGalois F L] in
private theorem value_one (ξ : Cocycle G (cover F L)) : value ξ 1 = 1 := by
  unfold value
  rw [arrow_one, Cocycle.toFun_self]

/-- If a twisted value of a quadratic cocycle lies in the cell with unique
coordinates `U⁺ × T × σ(U⁺)`, a second twist removes both unipotent
coordinates. The resulting torus cocycle has exactly the middle value. -/
theorem exists_torusCocycle_of_oppositeCell
    (hquad : Module.finrank F L = 2) (σ : L ≃ₐ[F] L) (hσ : σ ≠ 1)
    (j : T ⟶ G) [Mono j.hom.hom] (Uplus : Subgroup (CoefficientPoints (L := L) G))
    (hinj : Function.Injective (fun z : Uplus × CoefficientPoints (L := L) T × Uplus =>
      (z.1 : CoefficientPoints (L := L) G) * (z.2.1 ≫ j.hom.hom) *
        GaloisPoint.conjugate F L G σ z.2.2))
    (ξ : Cocycle G (cover F L)) (f : CoefficientPoints (L := L) G)
    (u v : Uplus) (t : CoefficientPoints (L := L) T)
    (hcell : value (ξ.twist f) σ = (u : CoefficientPoints (L := L) G) * (t ≫ j.hom.hom) *
      GaloisPoint.conjugate F L G σ v) :
    ∃ δ : Cocycle T (cover F L), value δ σ = t ∧ (δ.map j).Cohomologous ξ := by
  let ψ := GaloisPoint.conjugate F L G σ
  let ψT := GaloisPoint.conjugate F L T σ
  change value (ξ.twist f) σ = (u : CoefficientPoints (L := L) G) * (t ≫ j.hom.hom) * ψ v at hcell
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := (IsGalois.card_aut_eq_finrank F L).trans hquad
  obtain ⟨_, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).mp hcard
  have hcase (s : L ≃ₐ[F] L) : s = 1 ∨ s = σ := by
    by_cases hs : s = 1
    · exact Or.inl hs
    · exact Or.inr ((huniq s hs).trans (huniq σ hσ).symm)
  have hσ₂ : σ * σ = 1 := by
    simpa only [hcard, pow_two] using (pow_card_eq_one' (x := σ))
  have hψ₂ (x : CoefficientPoints (L := L) G) : ψ (ψ x) = x := by
    change GaloisPoint.conjugate F L G σ (GaloisPoint.conjugate F L G σ x) = x
    rw [← GaloisPoint.conjugate_mul, hσ₂, GaloisPoint.conjugate_one]
  have hc : value (ξ.twist f) σ = (ψ (value (ξ.twist f) σ))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← value_mul, hσ₂, value_one]
  have hj (x : CoefficientPoints (L := L) T) : ψ (x ≫ j.hom.hom) = ψT x ≫ j.hom.hom :=
    (Category.assoc (arrow F L σ) x j.hom.hom).symm
  have hcoordinates : (u, t, v) = (v⁻¹, (ψT t)⁻¹, u⁻¹) := by
    apply hinj
    change (u : CoefficientPoints (L := L) G) * (t ≫ j.hom.hom) * ψ v =
      ((v⁻¹ : Uplus) : CoefficientPoints (L := L) G) * ((ψT t)⁻¹ ≫ j.hom.hom) *
        ψ ((u⁻¹ : Uplus) : CoefficientPoints (L := L) G)
    rw [← hcell, hc, hcell, _root_.map_mul, _root_.map_mul, hj, hψ₂]
    simp only [Subgroup.coe_inv, GrpObj.inv_comp, _root_.map_inv]
    group
  have hv : v = u⁻¹ := congrArg (fun z : Uplus × CoefficientPoints (L := L) T × Uplus => z.2.2)
    hcoordinates
  let ζ := (ξ.twist f).twist (u : CoefficientPoints (L := L) G)
  have hζ : value ζ σ = t ≫ j.hom.hom := by
    change (𝟙 _ ≫ (u : CoefficientPoints (L := L) G))⁻¹ * value (ξ.twist f) σ * ψ u = _
    rw [Category.id_comp, hcell, hv, Subgroup.coe_inv, _root_.map_inv]
    group
  have hfac : ∀ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ cover F L),
      ∃ d : Z ⟶ T.X, d ≫ j.hom.hom = ζ.toFun a b := by
    apply Cocycle.factors_of_galois ζ j
    intro s
    rcases hcase s with rfl | hs
    · refine ⟨1, ?_⟩
      change (1 : CoefficientPoints (L := L) T) ≫ j.hom.hom = value ζ 1
      rw [value_one, MonObj.one_comp]
    · subst s
      exact ⟨t, hζ.symm⟩
  let δ := ζ.lift j hfac
  have hδ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ cover F L) :
      (δ.map j).toFun a b = ζ.toFun a b := ζ.lift_toFun j hfac a b
  refine ⟨δ, ?_, ?_⟩
  · apply (cancel_mono j.hom.hom).mp
    exact (hδ (𝟙 _) (arrow F L σ)).trans hζ
  · have h₁ : ξ.Cohomologous (ξ.twist f) := ⟨f, fun _ _ => rfl⟩
    have h₂ : (ξ.twist f).Cohomologous (δ.map j) := ⟨u, hδ⟩
    exact (h₁.trans h₂).symm

end Langlands.GroupScheme.GaloisCocycle
