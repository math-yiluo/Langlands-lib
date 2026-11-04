import Langlands.GroupScheme.SubgroupFunctor.FppfProductCriterion
import Langlands.GroupScheme.AutomorphicAction.SemidirectHomLift
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProductExistenceStatement

/-! # Represented products of a smooth connected subgroup with a normal one -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G P : GroupScheme S}

namespace FppfLocallyInProduct

variable {F N : SubgroupFunctor G} {T : Over S} {x : T ⟶ G.X}

/-- A local product with a normal first factor is also a local product in the
opposite order: `n * f = f * (f⁻¹ * n * f)`. -/
theorem swap_of_isNormal_left (hN : N.IsNormal) (hx : FppfLocallyInProduct N F x) :
    FppfLocallyInProduct F N x := by
  obtain ⟨V, v, hf, hs, hl, n, f, hn, hf', he⟩ := hx
  refine ⟨V, v, hf, hs, hl, f, f⁻¹ * n * f, hf', ?_, ?_⟩
  · simpa only [inv_inv] using hN V f⁻¹ n (Subgroup.mem_top _) hn
  · rw [he]
    simp only [mul_assoc, mul_inv_cancel_left]

/-- A local product with a normal second factor is also a local product in the
opposite order: `f * n = (f * n * f⁻¹) * f`. -/
theorem swap_of_isNormal_right (hN : N.IsNormal) (hx : FppfLocallyInProduct F N x) :
    FppfLocallyInProduct N F x := by
  obtain ⟨V, v, hf, hs, hl, f, n, hf', hn, he⟩ := hx
  refine ⟨V, v, hf, hs, hl, f * n * f⁻¹, f, hN V f n (Subgroup.mem_top _) hn, hf', ?_⟩
  rw [he]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end FppfLocallyInProduct

/-- A closed subgroup representing the local product with a normal first factor
also represents the local product in the opposite order. -/
theorem IsFppfProduct.swap {F N : SubgroupFunctor G} {p : P ⟶ G}
    (hp : IsFppfProduct N F p) (hN : N.IsNormal) : IsFppfProduct F N p :=
  ⟨hp.isClosedSubgroup, fun T x => (hp.mem_range_iff T x).trans
    ⟨fun h => h.swap_of_isNormal_left hN, fun h => h.swap_of_isNormal_right hN⟩⟩

end SubgroupFunctor

namespace SmoothConnectedNormalFactorProduct

variable {k : Type u} [Field k]

local instance : Subsingleton (Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/-- Milne, Theorem 5.82, for smooth connected factors: the image of the
semidirect multiplication homomorphism `N ⋊ H ⟶ G` is the represented product. -/
theorem exists_isFppfProduct {G H N : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (i : H ⟶ G) (j : N ⟶ G) (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hN : (SubgroupFunctor.range j).IsNormal) :
    ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
      SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
        (SubgroupFunctor.range j) p ∧
      Smooth P.X.hom ∧ ConnectedSpace P.X.left := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom N.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range i) :=
    fun T g x _ hx => hN T g x (Subgroup.mem_top _) hx
  -- The semidirect product `N ⋊ H`, whose underlying scheme is `N.X ⊗ H.X`.
  let a := AutomorphicAction.ofNormalizedConjugation j i hn
  let φ : a.semidirectProduct ⟶ G := SubgroupFunctor.normalizedProductHom j i hn
  obtain ⟨hA, -, -, hint⟩ := smoothConnectedAffineGeometry.2 k N H inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
  have hAsm : Smooth a.semidirectProduct.X.hom := by
    change Smooth (pullback.fst N.X.hom H.X.hom ≫ N.X.hom)
    infer_instance
  have hAaff : IsAffineHom a.semidirectProduct.X.hom := hA
  have : GeometricallyIntegral a.semidirectProduct.X.hom := hint
  have hAcon : ConnectedSpace a.semidirectProduct.X.left := by
    have : IrreducibleSpace a.semidirectProduct.X.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton a.semidirectProduct.X.hom
    infer_instance
  obtain ⟨D, inc, fac, hinc, hfac, hfl, hsu, -, hlfp, hDs, hDc, -⟩ :=
    smoothConnectedHomImage k a.semidirectProduct G φ hAsm hAcon hAaff inferInstance
      inferInstance
  let q : N.X ⊗ H.X ⟶ D.X := fac.hom.hom
  have : Flat q.left := hfl
  have : Surjective q.left := hsu
  have : LocallyOfFinitePresentation q.left := hlfp
  have hq : q ≫ inc.hom.hom =
      (fst N.X H.X ≫ j.hom.hom) * (snd N.X H.X ≫ i.hom.hom) := by
    change fac.hom.hom ≫ inc.hom.hom = _
    rw [← Grp.comp_hom_hom, hfac]
    exact SubgroupFunctor.normalizedProductHom_hom j i hn
  exact ⟨D, inc,
    (SubgroupFunctor.isFppfProduct_of_fppf_factorization j i inc hinc q hq).swap hN,
    hDs, hDc⟩

end SmoothConnectedNormalFactorProduct

/-- Proof of the smooth connected normal-factor product proposition. -/
theorem smoothConnectedNormalFactorFppfProductExistence :
    SmoothConnectedNormalFactorFppfProductExistenceStatement.{u} := by
  intro k _ G _ _ H N i j hi _ _ hj _ _ hN
  exact SmoothConnectedNormalFactorProduct.exists_isFppfProduct i j hi hj hN

end Langlands.GroupScheme
