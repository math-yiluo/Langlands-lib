import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback
import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Langlands.AlgebraicGeometry.Stacks.SchemeAtlas
import Langlands.CategoryTheory.Sites.PseudofunctorHomLift
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.FiniteType

/-! # Smooth charts of the actual coherent-family stack through finite-type field points -/

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Stacks

variable {S : Scheme.{u}} (F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1})
  {U : Over S}

/-- Every actual point fibre of the chart object is represented on the full
slice by a scheme smooth over the test scheme. No surjectivity is required. -/
def HasSmoothPointFibers (ξ : F.obj (.mk (op U))) : Prop :=
  ∀ (T : Over S) (η : F.obj (.mk (op T))),
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        pointFiberPresheaf F ξ η) ∧
      Smooth P.hom

/-- A smooth surjective presentation has smooth point fibres. -/
lemma IsSmoothSurjectivePresentation.hasSmoothPointFibers {ξ : F.obj (.mk (op U))}
    (h : IsSmoothSurjectivePresentation F ξ) : HasSmoothPointFibers F ξ := by
  intro T η
  obtain ⟨P, e, hP, -⟩ := h T η
  exact ⟨P, e, hP⟩

end Langlands.AlgebraicGeometry.Stacks

namespace Langlands.AlgebraicGeometry.CoherentSheaves

open Langlands.AlgebraicGeometry.Deformation

/-- Let `X` be a proper scheme over a field `k`. For every field `K` of finite type
over `k` and every actual flat finitely presented family `N` on `X_K`, there are a
scheme `U` locally of finite type over `k`, an actual family `M` on `U ×_k X`
whose point fibres in the coherent-family stack are all represented by schemes
smooth over the test, and a `K`-point `p` of `U` over `k` with an actual
isomorphism from the ordinary pullback of `M` along `p` to `N`. -/
def FieldCoherentPointSmoothChartStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))), IsProper X.hom →
    ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.FiniteType k K]
      (N : FamilyGroupoid X.hom (ArtinianTest.residueBase k K)),
      ∃ (U : Over (Spec (CommRingCat.of k))) (M : FamilyGroupoid X.hom U)
        (p : ArtinianTest.residueBase k K ⟶ U),
        LocallyOfFiniteType U.hom ∧
          Stacks.HasSmoothPointFibers
            (Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{u + 1}
              (FamilyGroupoid.pseudofunctor X.hom))
            (ULiftHom.objUp.{u + 1, u + 1} M) ∧
          Nonempty ((FamilyGroupoid.pullback X.hom p).obj M ≅ N)

end Langlands.AlgebraicGeometry.CoherentSheaves
