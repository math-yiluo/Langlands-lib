import Langlands.GroupScheme.Rational.FiniteGaloisOverlapDiscrepancy
import Langlands.GroupScheme.Rational.FiniteGaloisCocycleValues

/-! # Factorization of cocycles on finite Galois covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.Cocycle

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_galoisPair_desc {W : Over (Spec (CommRingCat.of K))}
    (d : (M ≃ₐ[K] M) → (ringTest K M ⟶ W)) :
    ∃ g : ringTest K M ⊗ ringTest K M ⟶ W, ∀ σ, galoisPair σ ≫ g = d σ := by
  let π := Sigma.desc (Descent.finiteGaloisComponent K M)
  have : IsIso π := inferInstanceAs (IsIso (Sigma.desc (Descent.finiteGaloisComponent K M)))
  let g := inv π ≫ Sigma.desc (fun i => (d (Descent.galoisIndexEquiv K M i)).left)
  have hcomp (i : Fin (Module.finrank K M)) :
      Descent.finiteGaloisComponent K M i ≫ g =
        (d (Descent.galoisIndexEquiv K M i)).left := by
    rw [← Sigma.ι_comp_desc (Descent.finiteGaloisComponent K M) i]
    change (_ ≫ π) ≫ inv π ≫ _ = _
    simp
  refine ⟨Over.homMk g ?_, fun σ => ?_⟩
  · apply (cancel_epi π).mp
    apply Sigma.hom_ext
    intro i
    change (Sigma.ι _ i ≫ π) ≫ g ≫ W.hom =
      (Sigma.ι _ i ≫ π) ≫ (ringTest K M ⊗ ringTest K M).hom
    rw [show Sigma.ι _ i ≫ π = Descent.finiteGaloisComponent K M i from
      Sigma.ι_comp_desc _ _, ← Category.assoc, hcomp, Over.w]
    rw [finiteGaloisComponent_eq_galoisPair]
    exact (Over.w (galoisPair (Descent.galoisIndexEquiv K M i))).symm
  · obtain ⟨i, rfl⟩ := (Descent.galoisIndexEquiv K M).surjective σ
    apply Over.OverMorphism.ext
    change (galoisPair (Descent.galoisIndexEquiv K M i)).left ≫ g = _
    rw [← finiteGaloisComponent_eq_galoisPair, hcomp]

variable {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- A cocycle factors on all tests if it factors on the Galois components of
the double overlap. -/
theorem factors_of_galois (ξ : Cocycle G (ringTest K M)) (j : H ⟶ G)
    (h : ∀ σ : M ≃ₐ[K] M, ∃ d : ringTest K M ⟶ H.X,
      d ≫ j.hom.hom = ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom))
    {Z : Over (Spec (CommRingCat.of K))} (a b : Z ⟶ ringTest K M) :
    ∃ d : Z ⟶ H.X, d ≫ j.hom.hom = ξ.toFun a b := by
  choose d hd using h
  obtain ⟨g, hg⟩ := exists_galoisPair_desc d
  let U := ringTest K M
  have hU : g ≫ j.hom.hom = ξ.toFun (fst U U) (snd U U) := by
    apply galoisPair_ext
    intro σ
    rw [← Category.assoc, hg, ← ξ.naturality, galoisPair_fst, galoisPair_snd]
    exact hd σ
  refine ⟨CartesianMonoidalCategory.lift a b ≫ g, ?_⟩
  rw [Category.assoc, hU, ← ξ.naturality, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd]

/-- Factorization on Galois values implies factorization on every test scheme. -/
def FiniteGaloisCocycleFactorizationStatement : Prop :=
  ∀ (K M : Type u) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (G H : GroupScheme (Spec (CommRingCat.of K))) (ξ : Cocycle G (ringTest K M)) (j : H ⟶ G),
    (∀ σ : M ≃ₐ[K] M, ∃ d : ringTest K M ⟶ H.X,
      d ≫ j.hom.hom = ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom)) →
    ∀ {Z : Over (Spec (CommRingCat.of K))} (a b : Z ⟶ ringTest K M),
      ∃ d : Z ⟶ H.X, d ≫ j.hom.hom = ξ.toFun a b

theorem finiteGaloisCocycleFactorization : FiniteGaloisCocycleFactorizationStatement.{u} := by
  intro K M _ _ _ _ _ G H ξ j h Z a b
  exact factors_of_galois ξ j h a b

end Langlands.GroupScheme.Cocycle
