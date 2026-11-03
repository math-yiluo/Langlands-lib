import Langlands.GroupScheme.Absolute.Borel

/-! # Solvability along a base change by a field isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Base change along a bijective map of fields `φ : K →+* K'` preserves solvability: the
algebraic closures of `K` and `K'` are identified compatibly with `φ`, which identifies the
groups of points defining both solvability conditions. -/
theorem IsSolvableGroupScheme.baseChange_of_bijective {K K' : Type u} [Field K] [Field K']
    (φ : K →+* K') (hφ : Function.Bijective φ) {B : GroupScheme (Spec (CommRingCat.of K))}
    (hB : IsSolvableGroupScheme B) :
    IsSolvableGroupScheme ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj B) := by
  let σ : K ≃+* K' := RingEquiv.ofBijective φ hφ
  let ψ : AlgebraicClosure K ≃+* AlgebraicClosure K' :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K') σ
  have hψ : (ψ : AlgebraicClosure K →+* AlgebraicClosure K').comp
      (algebraMap K (AlgebraicClosure K)) = (algebraMap K' (AlgebraicClosure K')).comp φ :=
    IsAlgClosure.equivOfEquiv_comp_algebraMap _ _ σ
  let e := Spec.map (CommRingCat.ofHom φ)
  let T : Over (Spec (CommRingCat.of K)) :=
    (Over.map (toAlgebraicClosure K)).obj (Over.mk (𝟙 _))
  let T' : Over (Spec (CommRingCat.of K)) :=
    (Over.map e).obj ((Over.map (toAlgebraicClosure K')).obj (Over.mk (𝟙 _)))
  let a : T' ≅ T := Over.isoMk (Scheme.Spec.mapIso ψ.toCommRingCatIso.op) (by
    change Spec.map (CommRingCat.ofHom (ψ : AlgebraicClosure K →+* AlgebraicClosure K')) ≫
        𝟙 _ ≫ toAlgebraicClosure K = (𝟙 _ ≫ toAlgebraicClosure K') ≫ e
    simp only [Category.id_comp, toAlgebraicClosure, e, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hψ])
  let E : (Over.mk (𝟙 _) ⟶ ((GroupScheme.baseChange (toAlgebraicClosure K')).obj
      ((GroupScheme.baseChange e).obj B)).X) ≃*
      (Over.mk (𝟙 _) ⟶ ((GroupScheme.baseChange (toAlgebraicClosure K)).obj B).X) :=
    ((baseChangePointsEquiv (toAlgebraicClosure K') ((GroupScheme.baseChange e).obj B)
      (Over.mk (𝟙 _))).trans (baseChangePointsEquiv e B _)).trans
      ((((yonedaGrp.obj B).mapIso a.op).groupIsoToMulEquiv).symm.trans
        (baseChangePointsEquiv (toAlgebraicClosure K) B (Over.mk (𝟙 _))).symm)
  let : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure K)))) ⟶
      ((GroupScheme.baseChange (toAlgebraicClosure K)).obj B).X) := hB
  exact Group.isSolvable_of_isSolvable_injective (f := E.toMonoidHom) E.injective

end Langlands.GroupScheme
