import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport

/-! # Transport of relative-root reflection data along a commuting torus square

For isomorphisms `e : T ≅ T'` and `f : G ≅ H` with `i ≫ f.hom = e.hom ≫ j`, the coroot of
a transported relative root is the `e`-transport of the old coroot, and its reflection
representative is the `f`-image of the old normalizing point.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeRootReflectionData

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H} [Mono i.hom.hom.left] [Mono j.hom.hom.left]

/-- Coroots transported along `e` and reflection representatives along `f`, both indexed
through the actual relative-root bijection of the square. -/
def transport (D : RelativeRootReflectionData i) (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    RelativeRootReflectionData j where
  coroot a :=
    cocharacterLattice.congr e (D.coroot ((relativeRootsTransportEquiv e f h).symm a))
  representative a :=
    normalizerPointsTransportEquiv e f h
      (D.representative ((relativeRootsTransportEquiv e f h).symm a))
  pair_self a := by
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv e f h).surjective a
    rw [Equiv.symm_apply_apply]
    change latticePairing T' (characterLattice.congr e a.val)
      (cocharacterLattice.congr e (D.coroot a)) = 2
    rw [latticePairing_congr, D.pair_self]
  action a χ := by
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv e f h).surjective a
    obtain ⟨χ, rfl⟩ := (characterLattice.congr e).surjective χ
    rw [Equiv.symm_apply_apply]
    change weylAction j (normalizerPointsTransportEquiv e f h (D.representative a))
        (characterLattice.congr e χ) =
      characterLattice.congr e χ - latticePairing T' (characterLattice.congr e χ)
        (cocharacterLattice.congr e (D.coroot a)) • characterLattice.congr e a.val
    rw [weylAction_transport, D.action, latticePairing_congr, map_sub, map_zsmul]

variable (D : RelativeRootReflectionData i) (e : T ≅ T') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

/-- The coroot of a transported root is the transport of the old coroot. -/
theorem transport_coroot (a : relativeRoots i) :
    (D.transport e f h).coroot (relativeRootsTransportEquiv e f h a) =
      cocharacterLattice.congr e (D.coroot a) := by
  change cocharacterLattice.congr e
    (D.coroot ((relativeRootsTransportEquiv e f h).symm (relativeRootsTransportEquiv e f h a))) = _
  rw [Equiv.symm_apply_apply]

/-- The representative of a transported root is the `f`-image of the old one. -/
theorem transport_representative (a : relativeRoots i) :
    (D.transport e f h).representative (relativeRootsTransportEquiv e f h a) =
      normalizerPointsTransportEquiv e f h (D.representative a) := by
  change normalizerPointsTransportEquiv e f h (D.representative
    ((relativeRootsTransportEquiv e f h).symm (relativeRootsTransportEquiv e f h a))) = _
  rw [Equiv.symm_apply_apply]

end RelativeRootReflectionData
end Langlands.GroupScheme
