/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.IdentityTangentTransport
import WeilConjectures.AlgebraicGeometry.GroupScheme.IdentityTangentOperations

/-!
# The Lie algebra as the tangent space at the identity

Source: blueprint `proposition-cartier-s-theorem`, third paragraph, and
`def-wf-lie-algebra-derivation`.

## Main definitions

* `AlgebraicGeometry.GrpObj.lieIdentityTangentEquiv`: the `k`-linear equivalence between
  `Lie G` and the scheme tangent space of `G.left` at the identity.
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory
open scoped MonObj
namespace AlgebraicGeometry.GrpObj

/-- The Lie algebra identifies linearly with the scheme tangent space at the identity: it is
`lieEquiv.symm` followed by `identityTangentTransport`. The tangent space is a `k`-module by
restriction of scalars along the structural residue map.
Source: blueprint `proposition-cartier-s-theorem`, third paragraph, and
`def-wf-lie-algebra-derivation`.

Additivity and `k`-linearity are `identity_tangent_transport_operations`, together with
`lieEquiv_symm_add` and `lieEquiv_symm_smul`. No smoothness, finite type, or
finite-dimensional assumption is used. -/
def lieIdentityTangentEquiv {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    letI : Module k (schemeTangentSpace k G.left G.hom x) :=
      Module.compHom (schemeTangentSpace k G.left G.hom x) r
    Lie G ≃ₗ[k] schemeTangentSpace k G.left G.hom x := by
  intro x r
  letI : Module k (schemeTangentSpace k G.left G.hom x) := Module.compHom _ r
  exact { (lieEquiv G).symm.trans (identityTangentTransport G) with
      map_add' := fun v w ↦ by
        have h := (identity_tangent_transport_operations G _
          (identityTangentTransport_val G)).1
        change identityTangentTransport G ((lieEquiv G).symm (v + w)) =
          identityTangentTransport G ((lieEquiv G).symm v) +
            identityTangentTransport G ((lieEquiv G).symm w)
        rw [lieEquiv_symm_add, h]
      map_smul' := fun t v ↦ by
        have h := (identity_tangent_transport_operations G _
          (identityTangentTransport_val G)).2
        change identityTangentTransport G ((lieEquiv G).symm (t • v)) =
          t • identityTangentTransport G ((lieEquiv G).symm v)
        change identityTangentTransport G
          ((lieEquiv G).symm ((Scheme.ΓSpecIso (.of k)).inv.hom t • v)) = _
        rw [lieEquiv_symm_smul, h] }

/-- The defining formula of `lieIdentityTangentEquiv`. -/
theorem lieIdentityTangentEquiv_apply {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] (v : Lie G) :
    lieIdentityTangentEquiv G v = identityTangentTransport G ((lieEquiv G).symm v) :=
  rfl

end AlgebraicGeometry.GrpObj
