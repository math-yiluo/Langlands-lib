import Langlands.GroupScheme.OuterIsomorphismScheme
import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.RelativeInnerForm
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Relative automorphism schemes and their outer quotient geometry -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The representability and quotient geometry of Conrad's Theorem 7.1.9(1),
with the full-centre quotient supplied independently. The local constancy
clause is an actual isomorphism to a disjoint union over an étale cover. -/
def ReductiveAutomorphismSchemeGeometryStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ I : GroupIsomorphismScheme G G,
      Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom ∧
      ∀ (A : GroupScheme S) (q : G ⟶ A) (hq : IsRelativeAdjointQuotient q),
        ∃ O : OuterIsomorphismScheme I hq.innerAction,
          Etale O.parameter.hom ∧ IsSeparated O.parameter.hom ∧
          IsAffineHom O.classMap.left ∧
          IsClosedImmersion (I.classify
            ((LocalGroupIso.ofIso (Iso.refl G) A.X).twist hq.innerAction (𝟙 A.X))).left ∧
          ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
            ∀ i : 𝒰.I₀, ∃ D : Type u,
              Nonempty ((Over.pullback (𝒰.f i)).obj O.parameter ≅
                Over.mk (Sigma.desc (fun _ : D => 𝟙 (𝒰.X i))))

end Langlands.GroupScheme
