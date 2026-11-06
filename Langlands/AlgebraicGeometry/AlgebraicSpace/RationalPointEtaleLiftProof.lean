import Langlands.AlgebraicGeometry.AlgebraicSpace.RationalPointEtaleLiftStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisChartPoint
import Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibrePower
import Langlands.AlgebraicGeometry.AlgebraicSpace.OverActionQuotientChart

/-! # Rational points of algebraic spaces over a field lift to affine étale charts

A `k`-point `x` of an algebraic space `X` over `Spec k` lifts, over a finite Galois
extension `K/k`, to a `K`-point `v` of an affine separated scheme `V` with an étale map
`a : h_V → X`. The Galois group `G` acts on the `G`-fold fibre power `Y` of `a` by permuting
the factors, and diagonally on `Y ×_k Spec K`. The point with coordinates `(σ v)_σ` and
`id_{Spec K}` is equivariant, so the quotient of a stable affine neighbourhood gives an
affine scheme `M` with an étale map to `X` and a Galois-invariant `K`-point over `x`. That
point descends to a `k`-point of `M`, whose image in `X` agrees with `x` after base change
to `K`, hence equals `x`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard.DualNumberDouble (specOverMap specOverMap_left)
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace RationalPointEtaleLiftProof

variable {k : Type u} [Field k]

/-- A `K`-point of an étale separated chart over a `k`-point of `X`, for a finite Galois
extension `K/k`, yields an affine scheme with an étale map to `X` and a Galois-invariant
`K`-point over the same `k`-point. -/
theorem exists_invariant_chart_point (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (xh : (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf)
    {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {V : Over (Spec (CommRingCat.of k))} (a : (schemeYoneda _).obj V ⟶ X.presheaf)
    [_root_.AlgebraicGeometry.IsSeparated V.hom] (ha : IsEtale a) (v : specOver k K ⟶ V)
    (π : specOver k K ⟶ ringTest k k)
    (hv : (schemeYoneda _).map v ≫ a = (schemeYoneda _).map π ≫ xh) :
    ∃ (M : Over (Spec (CommRingCat.of k))) (tM : (schemeYoneda _).obj M ⟶ X.presheaf)
      (w : specOver k K ⟶ M), IsAffine M.left ∧ IsEtale tM ∧
        (∀ g : K ≃ₐ[k] K, specOverMap g.toAlgHom ≫ w = w) ∧
        (schemeYoneda _).map w ≫ tM = (schemeYoneda _).map π ≫ xh := by
  obtain ⟨Y, hYsep, hYet⟩ := ChartFibrePower.exists_of_finite ha (K ≃ₐ[k] K)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : OverAction (K ≃ₐ[k] K) Y.obj, ∀ g, ρ.act g = Y.act g :=
    ⟨⟨Y.act, Y.act_one, Y.act_mul⟩, fun _ => rfl⟩
  obtain ⟨σ, hσ, hσfree⟩ : ∃ σ : OverAction (K ≃ₐ[k] K) (specOver k K),
      (∀ g, σ.act g = specOverMap g.toAlgHom) ∧ σ.IsFree :=
    ⟨OverAction.galoisAction, fun _ => rfl, OverAction.galoisAction_isFree⟩
  have hfree : (ρ.prod σ).IsFree := ρ.prod_isFree σ hσfree
  have : _root_.AlgebraicGeometry.IsSeparated
      (OverAction.prodOver Y.obj (specOver k K)).hom := by
    have := hYsep
    change _root_.AlgebraicGeometry.IsSeparated
      (pullback.snd Y.obj.hom (specOver k K).hom ≫ (specOver k K).hom)
    infer_instance
  have : (OverAction.prodOver Y.obj (specOver k K)).left.IsSeparated :=
    ⟨by rw [← terminal.comp_from (OverAction.prodOver Y.obj (specOver k K)).hom]
        infer_instance⟩
  have hπ : ∀ g : K ≃ₐ[k] K, specOverMap g.toAlgHom ≫ π = π := fun _ =>
    GaloisChartPoint.ringTest_self_hom_ext _ _
  have hvg : ∀ g : K ≃ₐ[k] K, (schemeYoneda _).map (specOverMap g.toAlgHom ≫ v) ≫ a =
      (schemeYoneda _).map π ≫ xh := fun g => by
    rw [Functor.map_comp_assoc, hv, ← Functor.map_comp_assoc, hπ]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : specOver k K ⟶ Y.obj,
      ∀ g, y₀ ≫ Y.pr g = specOverMap g.toAlgHom ≫ v :=
    ⟨Y.lift (fun g => specOverMap g.toAlgHom ≫ v) fun g h => by rw [hvg, hvg], Y.lift_pr _ _⟩
  obtain ⟨z, hzfst, hzsnd⟩ : ∃ z : specOver k K ⟶ OverAction.prodOver Y.obj (specOver k K),
      z ≫ OverAction.prodFst = y₀ ∧ z ≫ OverAction.prodSnd = 𝟙 _ :=
    ⟨OverAction.prodLift y₀ (𝟙 _), OverAction.prodLift_fst _ _, OverAction.prodLift_snd _ _⟩
  have hz : ∀ g, z ≫ (ρ.prod σ).act g = σ.act g ≫ z := by
    intro g
    apply OverAction.prod_hom_ext
    · rw [Category.assoc, OverAction.prod_act_fst, reassoc_of% hzfst, Category.assoc, hzfst,
        hρ]
      apply Y.hom_ext
      intro e
      rw [Category.assoc, Y.act_pr, hy₀, Category.assoc, hy₀, ← Category.assoc]
      simp only [← hσ, σ.mul]
    · rw [Category.assoc, OverAction.prod_act_snd, reassoc_of% hzsnd, Category.assoc, hzsnd,
        Category.comp_id]
  obtain ⟨t, rfl⟩ : ∃ t : (schemeYoneda _).obj (OverAction.prodOver Y.obj (specOver k K)) ⟶
      X.presheaf, t = (schemeYoneda _).map OverAction.prodFst ≫
        (schemeYoneda _).map (Y.pr 1) ≫ a := ⟨_, rfl⟩
  have ht : IsEtale ((schemeYoneda _).map
      (OverAction.prodFst : OverAction.prodOver Y.obj (specOver k K) ⟶ Y.obj) ≫
        (schemeYoneda _).map (Y.pr 1) ≫ a) :=
    IsEtale.comp (isEtale_map _ inferInstance) (IsEtale.comp (isEtale_map _ (hYet 1)) ha)
  have hinv : ∀ g, (schemeYoneda _).map ((ρ.prod σ).act g) ≫
      (schemeYoneda _).map OverAction.prodFst ≫ (schemeYoneda _).map (Y.pr 1) ≫ a =
        (schemeYoneda _).map OverAction.prodFst ≫ (schemeYoneda _).map (Y.pr 1) ≫ a := by
    intro g
    rw [← Functor.map_comp_assoc, OverAction.prod_act_fst, Functor.map_comp_assoc, hρ,
      ← Functor.map_comp_assoc _ (Y.act g), Y.act_pr, Y.w (g * 1) 1]
  obtain ⟨M, tM, w, hM, htM, hw, hwt⟩ :=
    OverAction.exists_affine_chart_of_point X (ρ.prod σ) σ hfree _ ht hinv z hz
  refine ⟨M, tM, w, hM, htM, fun g => by rw [← hσ]; exact hw g, ?_⟩
  rw [hwt, ← Functor.map_comp_assoc, hzfst, ← Functor.map_comp_assoc, hy₀, hvg]

/-- **Knutson II.6.4, Stacks 0BBP (rational points).** Every `k`-point of a
quasi-separated algebraic space over a field `k` is the image of a `k`-point of an affine
scheme with an étale map to the space. Quasi-separatedness is not used. -/
theorem rationalPointEtaleLiftStatement : RationalPointEtaleLiftStatement.{u} := by
  intro k _ X _ x
  obtain ⟨K, _, _, _, _, V, a, -, hVsep, -, hae, v, hv⟩ :=
    GaloisChartPoint.exists_galois_chart X x
  have := hVsep
  obtain ⟨M, tM, w, hM, htM, hw, hwt⟩ := exists_invariant_chart_point X _ a hae v _ hv
  have := hM
  obtain ⟨u, hu⟩ := GaloisChartPoint.exists_desc_of_galois_invariant w hw
  refine ⟨M, AlgebraicSpace.homMk tM, hM, htM, u, ?_⟩
  apply GaloisChartPoint.changeRing_injective X K
  have e₁ : RingPoints.map (AlgebraicSpace.homMk tM : (schemeToSpace _).obj M ⟶ X)
      ((schemeRingPointsEquiv k M k).symm u) =
        uliftYonedaEquiv ((schemeYoneda _).map u ≫ tM) := by
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    rfl
  have e₂ : x = uliftYonedaEquiv
      (uliftYonedaEquiv.symm x : (schemeYoneda _).obj (ringTest k k) ⟶ X.presheaf) :=
    (Equiv.apply_symm_apply _ _).symm
  have hu' : ringTestMap k (Algebra.ofId k K) ≫ u = w := hu
  rw [e₁, e₂]
  change X.presheaf.map (ringTestMap k (Algebra.ofId k K)).op _ =
    X.presheaf.map (ringTestMap k (Algebra.ofId k K)).op _
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
  congr 1
  rw [Quiver.Hom.unop_op, ← Functor.map_comp_assoc, hu']
  exact hwt

end RationalPointEtaleLiftProof

end Langlands.AlgebraicGeometry.AlgebraicSpace
