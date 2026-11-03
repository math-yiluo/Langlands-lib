import Langlands.GroupScheme.Rational.TorusNormalizerStatement
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection

/-! # Abstract normalizer and centralizer of split-torus rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Comparison

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  (i : T.toGrp ⟶ G)

private theorem normalizerPoints_eq_of_factorization [Mono i.hom.hom.left]
    (hfactor : ∀ f : T.X ⟶ G.X,
      (∀ x : Over.mk (𝟙 S) ⟶ T.X, ∃ y : Over.mk (𝟙 S) ⟶ T.X,
        y ≫ i.hom.hom = x ≫ f) → ∃ l : T.X ⟶ T.X, l ≫ i.hom.hom = f) :
    normalizerPoints i =
      Subgroup.normalizer ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 S)) :
        Set (Over.mk (𝟙 S) ⟶ G.X)) := by
  apply le_antisymm
  · intro n hn
    have h := normalizerPoints_le_torusNormalizer i hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      simpa only [Category.id_comp] using (h _ (𝟙 _) x hx).1
    · intro hx
      have h' := (h _ (𝟙 _) _ hx).2
      simpa only [Category.id_comp, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel_right, inv_mul_cancel, mul_one] using h'
  · intro n hn
    have hconj (m : Over.mk (𝟙 S) ⟶ G.X)
        (hm : m ∈ Subgroup.normalizer
          ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 S)) :
            Set (Over.mk (𝟙 S) ⟶ G.X))) :
        ∃ l : T.X ⟶ T.X, l ≫ i.hom.hom = (i ≫ (G.innerIso m).hom).hom.hom := by
      apply hfactor
      intro x
      have hx := (Subgroup.mem_normalizer_iff.mp hm (x ≫ i.hom.hom)).mp
        (show x ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier _ from ⟨x, rfl⟩)
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
      refine ⟨y, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self]
      exact hy
    obtain ⟨l, hl⟩ := hconj n hn
    obtain ⟨l', hl'⟩ := hconj n⁻¹ (Subgroup.inv_mem _ hn)
    apply torusNormalizer_le_normalizerPoints i
    rw [mem_torusNormalizer]
    intro V a t
    rw [comp_eq_constantPoint a n]
    constructor
    · refine ⟨t ≫ l, ?_⟩
      have h := congrArg (fun f => t ≫ f) hl.symm
      rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at h
      exact h
    · refine ⟨t ≫ l', ?_⟩
      have h := congrArg (fun f => t ≫ f) hl'.symm
      rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom,
        constantPoint_inv, inv_inv] at h
      exact h

private theorem centralizerPoints_eq_of_hom_ext
    (hext : ∀ {f g : T.X ⟶ G.X},
      (∀ x : Over.mk (𝟙 S) ⟶ T.X, x ≫ f = x ≫ g) → f = g) :
    centralizerPoints i =
      Subgroup.centralizer ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 S)) :
        Set (Over.mk (𝟙 S) ⟶ G.X)) := by
  apply le_antisymm
  · intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have h := (centralizerPoints_le_torusCentralizer i hn) _ (𝟙 _) t
    simpa only [Category.id_comp] using h.symm.eq
  · intro n hn
    rw [mem_centralizerPoints]
    apply Grp.hom_ext
    apply hext
    intro x
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self]
    have h := (Subgroup.mem_centralizer_iff.mp hn) (x ≫ i.hom.hom) ⟨x, rfl⟩
    rw [← h, mul_inv_cancel_right]

end Comparison

/-- Over an infinite field, the published normalizer and centralizer points are the
abstract normalizer and centralizer of the subgroup of torus rational points. -/
theorem normalizerPointsInfiniteField : NormalizerPointsInfiniteFieldStatement.{u} := by
  intro k _ _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion i.hom.hom.left := hi.2
  let : Mono i.hom.hom.left := hi.mono
  exact ⟨normalizerPoints_eq_of_factorization i (hi.1.exists_factor_of_kpoints i.hom.hom),
    centralizerPoints_eq_of_hom_ext i hi.1.hom_ext_kpoints⟩

end Langlands.GroupScheme
