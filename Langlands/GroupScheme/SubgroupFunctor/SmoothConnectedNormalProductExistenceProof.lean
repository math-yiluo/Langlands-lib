import Langlands.GroupScheme.AutomorphicAction.SemidirectHomLift
import Langlands.GroupScheme.SubgroupFunctor.FppfProductCriterion
import Langlands.GroupScheme.SubgroupFunctor.FppfProductSmooth
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalProductExistenceStatement
import Langlands.GroupScheme.HomImage

/-! # Existence of smooth connected represented normal products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {k : Type u} [Field k]
variable {G H N : GroupScheme (Spec (CommRingCat.of k))}

set_option backward.isDefEq.respectTransparency false in
/-- The ordered fppf product of two smooth connected closed subgroups exists
when the second normalizes the first. -/
theorem exists_smoothConnected_fppfProduct
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (j : N ⟶ G) (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    [Smooth H.X.hom] [Smooth N.X.hom]
    [ConnectedSpace H.X.left] [ConnectedSpace N.X.left]
    (hn : (range i).IsNormalizedBy (range j)) :
    ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
      IsFppfProduct (range i) (range j) p ∧
        Smooth P.X.hom ∧ ConnectedSpace P.X.left := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : IsAffineHom N.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  obtain ⟨hAff, _, _, hInt⟩ := smoothConnectedAffineGeometry.2 k H N
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
  let : IsAffineHom (H.X ⊗ N.X).hom := hAff
  let : GeometricallyIntegral (H.X ⊗ N.X).hom := hInt
  let : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IrreducibleSpace (H.X ⊗ N.X).left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (H.X ⊗ N.X).hom
  let : ConnectedSpace (H.X ⊗ N.X).left := inferInstance
  let : Smooth (H.X ⊗ N.X).hom :=
    smooth_tensor H.X N.X inferInstance inferInstance
  let : ConnectedSpace
      (AutomorphicAction.ofNormalizedConjugation i j hn).semidirectProduct.X.left := by
    change ConnectedSpace (H.X ⊗ N.X).left
    infer_instance
  let f := normalizedProductHom i j hn
  obtain ⟨P, p, q, hp, hqp, hf, hs, _, hl, _, _, _⟩ := HomImage.exists_image f
  let : Flat q.hom.hom.left := hf
  let : Surjective q.hom.hom.left := hs
  let : LocallyOfFinitePresentation q.hom.hom.left := hl
  have hprod : IsFppfProduct (range i) (range j) p :=
    isFppfProduct_of_fppf_factorization i j p hp q.hom.hom (by
      calc
        q.hom.hom ≫ p.hom.hom = f.hom.hom :=
          congrArg (fun r => r.hom.hom) hqp
        _ = _ := normalizedProductHom_hom i j hn)
  let : IsClosedImmersion p.hom.hom.left := hp
  let : IsAffineHom P.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  let : LocallyOfFiniteType P.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  have hH : (range i).IsRepresentedBy i := ⟨Over.mono_of_mono_left _, rfl⟩
  have hN : (range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  exact ⟨P, p, hprod, hprod.smooth hH hN, hprod.connectedSpace hH hN⟩

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme

/-- Two smooth connected normal closed subgroups of an affine algebraic group
over any field admit a smooth connected represented fppf product. -/
theorem smoothConnectedNormalFppfProductExistence :
    SmoothConnectedNormalFppfProductExistenceStatement.{u} := by
  intro k _ G hGa hGl H N i j hi hHs hHc hn hj hNs hNc _
  let : IsAffineHom G.X.hom := hGa
  let : LocallyOfFiniteType G.X.hom := hGl
  let : Smooth H.X.hom := hHs
  let : Smooth N.X.hom := hNs
  let : ConnectedSpace H.X.left := hHc
  let : ConnectedSpace N.X.left := hNc
  have hn' : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j) :=
    fun T g x _ hx => hn T g x (Subgroup.mem_top _) hx
  exact SubgroupFunctor.exists_smoothConnected_fppfProduct i j hi hj hn'

end Langlands.GroupScheme
