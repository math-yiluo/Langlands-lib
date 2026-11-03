import Langlands.GroupScheme.Reductive.Basic
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Comparing the chosen algebraic closures after field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A chosen embedding of the first algebraic closure into the second, over `k`. -/
def algebraicClosureEmbedding : AlgebraicClosure k →ₐ[k] AlgebraicClosure K :=
  IsAlgClosed.lift

/-- The morphism of spectra induced by the chosen embedding of algebraic closures. -/
def algebraicClosureBaseMap :
    Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      Spec (CommRingCat.of (AlgebraicClosure k)) :=
  Spec.map (CommRingCat.ofHom (algebraicClosureEmbedding k K).toRingHom)

/-- The chosen closure embedding is compatible with the original scalar map. -/
theorem algebraicClosureBaseMap_comp :
    algebraicClosureBaseMap k K ≫ toAlgebraicClosure k =
      toAlgebraicClosure K ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  simp only [algebraicClosureBaseMap, toAlgebraicClosure, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  exact (algebraicClosureEmbedding k K).commutes x

/-- The two successive pullbacks to the larger chosen algebraic closure agree,
naturally in the original group scheme. -/
def algebraicClosureBaseChangeIso :
    GroupScheme.baseChange (toAlgebraicClosure k) ⋙
        GroupScheme.baseChange (algebraicClosureBaseMap k K) ≅
      GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⋙
        GroupScheme.baseChange (toAlgebraicClosure K) :=
  (Functor.mapGrpNatIso
      (Over.pullbackComp (algebraicClosureBaseMap k K) (toAlgebraicClosure k)) ≪≫
    Functor.mapGrpCompIso).symm ≪≫
  eqToIso (congrArg (fun b => GroupScheme.baseChange b)
    (algebraicClosureBaseMap_comp k K)) ≪≫
  Functor.mapGrpNatIso
    (Over.pullbackComp (toAlgebraicClosure K)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≪≫
  Functor.mapGrpCompIso

/-- Naturality identifies the actual base-changed homomorphisms. -/
theorem algebraicClosureBaseChangeIso_hom_naturality
    {G H : GroupScheme (Spec (CommRingCat.of k))} (i : G ⟶ H) :
    (GroupScheme.baseChange (algebraicClosureBaseMap k K)).map
        ((GroupScheme.baseChange (toAlgebraicClosure k)).map i) ≫
        ((algebraicClosureBaseChangeIso k K).app H).hom =
      ((algebraicClosureBaseChangeIso k K).app G).hom ≫
        (GroupScheme.baseChange (toAlgebraicClosure K)).map
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) :=
  (algebraicClosureBaseChangeIso k K).hom.naturality i

end Langlands.GroupScheme
