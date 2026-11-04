import Langlands.GroupScheme.Rational.DynamicSemigroupProof
import Langlands.GroupScheme.Rational.CyclicWeightQuotientAssembly

/-! # The dynamic unipotent subgroup is the first cyclic weight filtration step -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]

/-- For `𝔾_m`, the positive semigroup of the identity cocharacter is the cyclic tail of the
identity character. -/
theorem positiveSemigroup_id_eq_cyclicTail :
    positiveSemigroup (S := Gm (Spec (CommRingCat.of k))) (𝟙 _) = cyclicTail (𝟙 _) 1 := by
  ext χ
  change 0 < gmEndEquiv k (𝟙 _ ≫ χ) ↔ ∃ n : ℕ, 1 ≤ n ∧ 0 < n ∧ n • 𝟙 _ = χ
  rw [Category.id_comp]
  constructor
  · intro h
    refine ⟨(gmEndEquiv k χ).toNat, by omega, by omega, ?_⟩
    conv_rhs => rw [eq_gmEndEquiv_zsmul k χ]
    rw [← natCast_zsmul, Int.toNat_of_nonneg h.le]
  · rintro ⟨n, -, hn, rfl⟩
    rw [← natCast_zsmul, gmEndEquiv_zsmul_id]
    exact_mod_cast hn

/-- The dynamic unipotent subgroup of a cocharacter `χ` of a smooth affine group is the first
step of the cyclic weight filtration of the conjugation action of `𝔾_m` through `χ`, for the
identity character. -/
theorem dynamicUnipotent_eq_weightFiltration (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Dynamic.unipotent χ =
      weightFiltration (S := Gm (Spec (CommRingCat.of k))) (AutomorphicAction.conjugation χ)
        (𝟙 _) 1 := by
  have h := dynamicUnipotentSemigroupComparison G (Gm _) isSplitTorus_gm χ (𝟙 _)
  rw [positiveSemigroup_id_eq_cyclicTail] at h
  exact h

section Model

open Corepresented

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} {G : GroupScheme (Spec (CommRingCat.of k))}
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B) (ψ : groupScheme F e ≅ G)
  {I : Type u} [Fintype I] [DecidableEq I]
  (φ : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) (b : AutomorphicAction S.toGrp G)

/-- Every step of the cyclic weight filtration is the weight subgroup functor of the cyclic tail
of exponent vectors (the identification inside `cyclicWeightFiltration_of_model`). -/
theorem weightFiltration_eq_weightSubgroupFunctor_cyclicTail [IsAffineHom G.X.hom]
    [IsAffineHom (groupScheme F e).X.hom] [Algebra.FormallySmooth k B] [Algebra.FiniteType k B]
    (a : characterLattice S) (ha : a ≠ 0) (n : ℕ) :
    weightFiltration b a n =
      weightSubgroupFunctor e ψ φ b (Corepresented.cyclicTail (characterExponents φ a) n) := by
  have ha' : characterExponents φ a ≠ 0 := by
    intro h
    exact ha ((characterExponents φ).injective (h.trans (map_zero _).symm))
  refine weightFiltration_eq_weightSubgroupFunctor e ψ φ b ha' n ?_ ?_
  · intro χ hχ
    exact (mem_cyclicTail_characterExponents φ a n χ).1
      (actionWeightSupport_comap_weightSubgroup_subset e ψ φ b _ hχ)
  · intro F' hF' J hJ hH
    refine tangentRigid_of_actionWeightSupport_subset e ψ φ b _ (fun χ hχ => ?_) hJ hH
    exact (mem_cyclicTail_characterExponents φ a n χ).2 (hF'.2.2 hχ)

end Model

end Langlands.GroupScheme.RelativeRoot
