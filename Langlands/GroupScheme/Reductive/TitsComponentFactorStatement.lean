import Langlands.GroupScheme.Reductive.TitsCartanComponent
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleWeilRestrictionStatement
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Actual factors realizing connected absolute Cartan components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- An actual absolutely almost-simple factor over a finite separable extension
realizes one connected absolute Cartan component. Its Weil restriction is a
factor of a simply connected central cover of the original group. -/
structure ComponentFactor (a : d.Vertex) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra k extension]
  [finiteDimensional : FiniteDimensional k extension]
  [separable : Algebra.IsSeparable k extension]
  factor : GroupScheme (Spec (CommRingCat.of extension))
  [affine : IsAffine factor.X.left]
  [affineHom : IsAffineHom factor.X.hom]
  [finiteType : LocallyOfFiniteType factor.X.hom]
  simplyConnected : IsSimplyConnected factor
  absolutelyAlmostSimple : IsAbsolutelyAlmostSimple factor
  complement : GroupScheme (Spec (CommRingCat.of k))
  complement_simplyConnected : IsSimplyConnected complement
  cover : (AffineWeil.groupScheme k extension factor ⊗ complement) ⟶ G
  cover_simplyConnected :
    IsSimplyConnected (AffineWeil.groupScheme k extension factor ⊗ complement)
  cover_centralIsogeny : IsCentralIsogeny cover
  index : TitsIndexData factor
  vertexEquiv : index.Vertex ≃ d.CartanComponent a
  cartan_eq : ∀ b c, d.cartan (vertexEquiv b).val (vertexEquiv c).val = index.cartan b c
  stabilizer_lift :
    ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
      d.CartanConnected a (d.star σ a) →
        ∃ τ : SeparableClosure extension ≃ₐ[extension] SeparableClosure extension,
          ∀ b, (vertexEquiv (index.star τ b)).val = d.star σ (vertexEquiv b).val
  star_lift :
    ∀ (τ : SeparableClosure extension ≃ₐ[extension] SeparableClosure extension),
      ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        ∀ b, (vertexEquiv (index.star τ b)).val = d.star σ (vertexEquiv b).val
  anisotropic : IsAnisotropic G → IsAnisotropic factor

attribute [instance] ComponentFactor.field ComponentFactor.algebra
  ComponentFactor.finiteDimensional ComponentFactor.separable
  ComponentFactor.affine ComponentFactor.affineHom ComponentFactor.finiteType

end TitsIndexData

/-- Every component of the actual absolute Cartan diagram of a semisimple group
is realized by an actual absolutely almost-simple factor over a finite separable
extension, with the full stabilizer star image and every Cartan entry retained.
This is an unproved structural prerequisite over arbitrary fields. -/
def SemisimpleTitsComponentFactorStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (a : d.Vertex),
    Nonempty (d.ComponentFactor a)

end Langlands.GroupScheme
