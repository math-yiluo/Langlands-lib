import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.Reductive.Basic

/-! # Reductive group schemes have geometrically irreducible fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The fibre of `G` over a point `s` of the base is connected as soon as the geometric fibre
over `s` is: the geometric fibre maps onto it. -/
theorem connectedSpace_residueFiber_of_geometricFiber {S : Scheme.{u}} (G : GroupScheme S)
    (s : S) [ConnectedSpace (geometricFiber G s).X.left] :
    ConnectedSpace ↥(pullback G.X.hom (S.fromSpecResidueField s)) := by
  let a := toAlgebraicClosure (S.residueField s)
  let b := S.fromSpecResidueField s
  have : Surjective a :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have : ConnectedSpace ↥(pullback G.X.hom (a ≫ b)) :=
    inferInstanceAs (ConnectedSpace (geometricFiber G s).X.left)
  let p := (pullbackLeftPullbackSndIso G.X.hom b a).inv ≫ pullback.fst (pullback.snd G.X.hom b) a
  have : Surjective p := by
    have : Surjective (pullback.fst (pullback.snd G.X.hom b) a) := inferInstance
    infer_instance
  exact Function.Surjective.connectedSpace p.surjective p.continuous

/-- **Geometric irreducibility of reductive group schemes.** The structure morphism of a
reductive group scheme has geometrically irreducible fibres: each residue fibre is a smooth
connected affine group, hence geometrically integral. -/
theorem IsReductive.geometricallyIrreducible {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsReductive G) : GeometricallyIrreducible G.X.hom := by
  have := hG.smooth
  have := hG.isAffineHom
  rw [GeometricallyIrreducible.iff_geometricallyIrreducible_fiber]
  intro s
  let Gs := (baseChange (S.fromSpecResidueField s)).obj G
  have : ConnectedSpace (Langlands.GroupScheme.geometricFiber G s).X.left :=
    (hG.geometricFiber s).connectedSpace
  have hconn : ConnectedSpace Gs.X.left := connectedSpace_residueFiber_of_geometricFiber G s
  have hsm : Smooth Gs.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (S.fromSpecResidueField s)))
  have haff : IsAffineHom Gs.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (S.fromSpecResidueField s)))
  have : GeometricallyIntegral Gs.X.hom := smoothConnectedAffineGeometry.1 _ Gs hsm haff hconn
  exact inferInstanceAs (GeometricallyIrreducible Gs.X.hom)

end Langlands.GroupScheme
