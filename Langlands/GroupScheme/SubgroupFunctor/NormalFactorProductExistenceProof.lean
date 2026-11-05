import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProduct
import Langlands.GroupScheme.SubgroupFunctor.NormalFactorProductExistenceStatement
import Langlands.GroupScheme.AffineHomImageProof

/-! # Represented products of a closed subgroup with a normal closed subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace NormalFactorProduct

/-- Milne, Theorem 5.82 (Algebraic Groups, 2017): given the fppf image
factorization of every homomorphism of affine algebraic groups, the image of
the semidirect multiplication homomorphism `N ⋊ H ⟶ G` represents the fppf
product of a closed subgroup `H` and a normal closed subgroup `N`. -/
theorem exists_isFppfProduct_of_affineHomImage (himage : AffineHomImageStatement.{u})
    {k : Type u} [Field k] {G H N : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (j : N ⟶ G) (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hN : (SubgroupFunctor.range j).IsNormal) :
    ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
      SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
        (SubgroupFunctor.range j) p := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom N.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType N.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range i) :=
    fun T g x _ hx => hN T g x (Subgroup.mem_top _) hx
  -- The semidirect product `N ⋊ H`, whose underlying scheme is `N.X ⊗ H.X`.
  let a := AutomorphicAction.ofNormalizedConjugation j i hn
  let φ : a.semidirectProduct ⟶ G := SubgroupFunctor.normalizedProductHom j i hn
  have : IsAffineHom a.semidirectProduct.X.hom := by
    change IsAffineHom (pullback.fst N.X.hom H.X.hom ≫ N.X.hom)
    have : IsAffineHom (pullback.fst N.X.hom H.X.hom) := by
      set_option backward.isDefEq.respectTransparency.types false in
      exact MorphismProperty.pullback_fst _ _ ‹IsAffineHom H.X.hom›
    infer_instance
  have : LocallyOfFiniteType a.semidirectProduct.X.hom := by
    change LocallyOfFiniteType (pullback.fst N.X.hom H.X.hom ≫ N.X.hom)
    infer_instance
  obtain ⟨I, fac, inc, -, -, hinc, hfac, hfl, hsu, hlfp, -⟩ :=
    himage k a.semidirectProduct G φ
  let q : N.X ⊗ H.X ⟶ I.X := fac.hom.hom
  have : Flat q.left := hfl
  have : Surjective q.left := hsu
  have : LocallyOfFinitePresentation q.left := hlfp
  have hq : q ≫ inc.hom.hom =
      (fst N.X H.X ≫ j.hom.hom) * (snd N.X H.X ≫ i.hom.hom) := by
    change fac.hom.hom ≫ inc.hom.hom = _
    rw [← Grp.comp_hom_hom, hfac]
    exact SubgroupFunctor.normalizedProductHom_hom j i hn
  exact ⟨I, inc,
    (SubgroupFunctor.isFppfProduct_of_fppf_factorization j i inc hinc q hq).swap hN⟩

end NormalFactorProduct

/-- The normal-factor product proposition follows from the fppf image
factorization of homomorphisms of affine algebraic groups. -/
theorem normalFactorFppfProductExistence_of_affineHomImage
    (himage : AffineHomImageStatement.{u}) :
    NormalFactorFppfProductExistenceStatement.{u} := by
  intro k _ G _ _ H N i j hi hj hN
  exact NormalFactorProduct.exists_isFppfProduct_of_affineHomImage himage i j hi hj hN

/-- Milne, Theorem 5.82 (Algebraic Groups, 2017): a closed subgroup and a
normal closed subgroup of an affine algebraic group over an arbitrary field
have a represented fppf product, at arbitrary universe. -/
theorem normalFactorFppfProductExistence : NormalFactorFppfProductExistenceStatement.{u} :=
  normalFactorFppfProductExistence_of_affineHomImage affineHomImage

end Langlands.GroupScheme
