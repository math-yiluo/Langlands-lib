import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.HomScheme.GraphBaseChange
import Langlands.GroupScheme.CentralIsogeny.Transport

/-! # Actual subgroup multiplication and base change -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {H K G : GroupScheme S}

/-- The point-defined product homomorphism is the actual commuting multiplication. -/
theorem prodHom_eq_commutingSubgroupMultiplicationHom
    (j : H ⟶ G) (i : K ⟶ G)
    (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom)) :
    prodHom j i hc = commutingSubgroupMultiplicationHom j i hc := by
  apply hom_ext_points
  intro T x
  rw [comp_prodHom]
  change ((productPointsEquiv H K T x).1 ≫ j.hom.hom) *
      ((productPointsEquiv H K T x).2 ≫ i.hom.hom) =
    x ≫ subgroupMultiplication j i
  simp only [productPointsEquiv_fst, productPointsEquiv_snd,
    subgroupMultiplication, MonObj.comp_mul, Category.assoc]

/-- The canonical product comparison respects the first coordinate on points. -/
theorem baseChangePointsEquiv_tensor_fst (b : S' ⟶ S)
    (T : Over S') (x : T ⟶ ((baseChange b).obj (H ⊗ K)).X) :
    baseChangePointsEquiv b H T
        ((x ≫ (baseChangeTensorIso b H K).hom.hom.hom) ≫
          (fst ((baseChange b).obj H) ((baseChange b).obj K)).hom.hom) =
      baseChangePointsEquiv b (H ⊗ K) T x ≫ (fst H K).hom.hom := by
  rw [Category.assoc, ← Grp.comp_hom_hom, baseChangeTensorIso_hom_fst,
    baseChangePointsEquiv_comp]

/-- The canonical product comparison respects the second coordinate on points. -/
theorem baseChangePointsEquiv_tensor_snd (b : S' ⟶ S)
    (T : Over S') (x : T ⟶ ((baseChange b).obj (H ⊗ K)).X) :
    baseChangePointsEquiv b K T
        ((x ≫ (baseChangeTensorIso b H K).hom.hom.hom) ≫
          (snd ((baseChange b).obj H) ((baseChange b).obj K)).hom.hom) =
      baseChangePointsEquiv b (H ⊗ K) T x ≫ (snd H K).hom.hom := by
  rw [Category.assoc, ← Grp.comp_hom_hom, baseChangeTensorIso_hom_snd,
    baseChangePointsEquiv_comp]

/-- Base change of multiplication agrees with multiplication of the base-changed maps. -/
theorem baseChange_prodHom (b : S' ⟶ S) (j : H ⟶ G) (i : K ⟶ G)
    (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hc' : ∀ (T : Over S') (h : T ⟶ ((baseChange b).obj H).X)
      (x : T ⟶ ((baseChange b).obj K).X),
      Commute (h ≫ ((baseChange b).map j).hom.hom)
        (x ≫ ((baseChange b).map i).hom.hom)) :
    (baseChange b).map (prodHom j i hc) =
      (baseChangeTensorIso b H K).hom ≫
        prodHom ((baseChange b).map j) ((baseChange b).map i) hc' := by
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv b G T).injective
  rw [baseChangePointsEquiv_comp, comp_prodHom, Grp.comp_hom_hom,
    ← Category.assoc, comp_prodHom, map_mul, baseChangePointsEquiv_comp,
    baseChangePointsEquiv_comp]
  simp only [productPointsEquiv_fst, productPointsEquiv_snd]
  have hf := baseChangePointsEquiv_tensor_fst (H := H) (K := K) b T x
  have hs := baseChangePointsEquiv_tensor_snd (H := H) (K := K) b T x
  simp only [Grp.fst_hom_hom] at hf
  simp only [Grp.snd_hom_hom] at hs
  rw [hf, hs]

/-- The exact base-changed map is a central isogeny whenever the product-of-fibres map is. -/
theorem isCentralIsogeny_baseChange_prodHom_iff (b : S' ⟶ S)
    (j : H ⟶ G) (i : K ⟶ G)
    (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hc' : ∀ (T : Over S') (h : T ⟶ ((baseChange b).obj H).X)
      (x : T ⟶ ((baseChange b).obj K).X),
      Commute (h ≫ ((baseChange b).map j).hom.hom)
        (x ≫ ((baseChange b).map i).hom.hom)) :
    IsCentralIsogeny ((baseChange b).map (prodHom j i hc)) ↔
      IsCentralIsogeny
        (prodHom ((baseChange b).map j) ((baseChange b).map i) hc') := by
  rw [baseChange_prodHom b j i hc hc', isCentralIsogeny_iso_comp_iff]

/-- Actual commuting multiplication is compatible with arbitrary base change,
including transport of the full central-isogeny predicate. -/
def MultiplicationBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (H K G : GroupScheme S) (b : S' ⟶ S)
    (j : H ⟶ G) (i : K ⟶ G)
    (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hc' : ∀ (T : Over S') (h : T ⟶ ((baseChange b).obj H).X)
      (x : T ⟶ ((baseChange b).obj K).X),
      Commute (h ≫ ((baseChange b).map j).hom.hom)
        (x ≫ ((baseChange b).map i).hom.hom)),
    prodHom j i hc = commutingSubgroupMultiplicationHom j i hc ∧
      (baseChange b).map (prodHom j i hc) =
        (baseChangeTensorIso b H K).hom ≫
          prodHom ((baseChange b).map j) ((baseChange b).map i) hc' ∧
      (IsCentralIsogeny ((baseChange b).map (prodHom j i hc)) ↔
        IsCentralIsogeny
          (prodHom ((baseChange b).map j) ((baseChange b).map i) hc'))

/-- The compatibility statement follows from the point formulas and isomorphism
transport. -/
theorem multiplicationBaseChange : MultiplicationBaseChangeStatement.{u} := by
  intro S S' H K G b j i hc hc'
  exact ⟨prodHom_eq_commutingSubgroupMultiplicationHom j i hc,
    baseChange_prodHom b j i hc hc',
    isCentralIsogeny_baseChange_prodHom_iff b j i hc hc'⟩

end Langlands.GroupScheme
