/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityDatum
import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumTransportDiagonal
import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumTransportCocycle
/-! # Identity and cocycle of compatible natural transport -/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- Naturality and compatibility force the diagonal and cocycle identities.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: lem-weil-pbc-finite-local-model-compatible-transport-transport)
Proof: For the diagonal, test on the universal Q-point on Q itself, which is
etale over T. The inverse of e sends that point to a section; compatibility
with equal lifts fixes the point. Naturality pulls this identity back along
any scheme point x. For the cocycle, test on R = Q times_T U times_T U, with
the first lift given by the structure map of Q and the other two by the U
factors. R is etale over T. Apply e inverse to the universal Q-point over the
first lift, obtaining s. Compatibility sends this point successively to the
points associated to s over the second and third lifts, so the composite
transport equals the direct transport. Every arbitrary x and three lifts
factor through R by the pullback universal property. Naturality pulls the
universal equality back, proving the claimed cocycle. Empty sources satisfy
the same argument. -/
theorem finiteLocalModels_descentDatum_compatibility_transport
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (t : FiniteLocalModelCompatibleTransport T E U Q e) :
    (∀ (W : Scheme.{u}) (a : W ⟶ U.left) (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      t.transport a a rfl x = x) ∧
    (∀ (W : Scheme.{u}) (a b c : W ⟶ U.left)
      (hab : a ≫ U.hom = b ≫ U.hom) (hbc : b ≫ U.hom = c ≫ U.hom)
      (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      t.transport b c hbc (t.transport a b hab x) =
        t.transport a c (hab.trans hbc) x) := by
  constructor
  · exact finiteLocalModels_descentDatum_compatibility_transport_diagonal T E U Q e t
  · exact finiteLocalModels_descentDatum_compatibility_transport_cocycle T E U Q e t
end AlgebraicGeometry.Scheme
