import Langlands.GroupScheme.HomogeneousQuotientRepresentability
import Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityCover

/-! # Homogeneous quotients from finite affine fppf covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.HomogeneousQuotientSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Quasi-affine local homogeneous quotients descend along a finite affine fppf
cover of an affine base to an actual smooth quasi-affine homogeneous quotient. -/
def quotientOfFiniteAffineCover
    {S : Scheme.{u}} [IsAffine S] {G H : GroupScheme S}
    (i : H ⟶ G) [Mono i.hom.hom] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hH : Smooth H.X.hom)
    {I : Type u} [Finite I] (B : I → Scheme.{u}) (q : ∀ k, B k ⟶ S)
    [∀ k, IsAffine (B k)] [∀ k, Flat (q k)]
    [∀ k, LocallyOfFinitePresentation (q k)]
    (hq : ∀ s : S, ∃ k, ∃ b : B k, q k b = s)
    (hlocal : ∀ k, ∃ Q : HomogeneousQuotient ((GroupScheme.baseChange (q k)).map i),
      Q.scheme.left.IsQuasiAffine) :
    {Q : HomogeneousQuotient i // Smooth Q.scheme.hom ∧ Q.scheme.left.IsQuasiAffine} := by
  classical
  let Q (k : I) := (hlocal k).choose
  let E (k : I) : (schemeYoneda (B k)).obj (Q k).scheme ≅
      (Over.map (q k)).op ⋙ presheaf i :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _)
      (Classical.choice (representableBy_baseChange i hH (q k) (Q k)))
  let M := Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent.quasiAffineModelOfFiniteCover
    (sheaf i hH).property B q hq (fun k => (Q k).scheme) E
      (fun k => (hlocal k).choose_spec)
  let : M.val.left.IsQuasiAffine := M.property.1
  let Q₀ := quotientOfIso i hH M.val (Classical.choice M.property.2)
  exact ⟨Q₀, Q₀.smooth_structure, M.property.1⟩

end Langlands.GroupScheme.HomogeneousQuotientSheaf
