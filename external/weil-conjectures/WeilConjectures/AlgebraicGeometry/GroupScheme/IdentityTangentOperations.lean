/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import WeilConjectures.AlgebraicGeometry.GroupScheme.IdentityTangentAddition

/-!
# Compatibility of identity tangent transport with the vector-space operations

Source: blueprint `def-wf-lie-algebra-derivation` and
`lemma-connected-components-images-homomorphisms--3`, Multiplication paragraph.
-/

@[expose] public section

universe u
open CategoryTheory
open scoped MonObj
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem scale_toSpec {k : Type u} [Field k] (t : k) :
    (Spec (.of k)).dualNumbersScale ((Scheme.ΓSpecIso (.of k)).inv.hom t) ≫
      Scheme.dualNumbersToSpec (.of k) =
    Scheme.dualNumbersToSpec (.of k) ≫ Spec.map (CommRingCat.ofHom
      (DualNumber.scale t).toRingHom) := by
  rw [Scheme.dualNumbersToSpec, Scheme.toSpecΓ_naturality_assoc]
  rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  symm
  change DualNumber.mapRingHom (Scheme.ΓSpecIso (.of k)).inv.hom (DualNumber.scale t z) =
    ((Spec (.of k)).dualNumbersScale ((Scheme.ΓSpecIso (.of k)).inv.hom t)).appTop
      (DualNumber.mapRingHom (Scheme.ΓSpecIso (.of k)).inv.hom z)
  change DualNumber.mapRingHom (Scheme.ΓSpecIso (.of k)).inv.hom (DualNumber.scale t z) =
    DualNumber.scale ((Scheme.ΓSpecIso (.of k)).inv.hom t)
      (DualNumber.mapRingHom (Scheme.ΓSpecIso (.of k)).inv.hom z)
  ext <;> simp [DualNumber.fst_mapRingHom, DualNumber.snd_mapRingHom, DualNumber.scale]

namespace GrpObj

set_option backward.isDefEq.respectTransparency false in
/-- Any map with the prescribed underlying morphism carries infinitesimal multiplication
and scaling to the specified tangent addition and scalar multiplication.
Source: blueprint `def-wf-lie-algebra-derivation`;
`lemma-connected-components-images-homomorphisms--3`, Multiplication paragraph; Stacks Project, Tag
0B2B, the construction of the vector-space operations.

Proof: The addition formula in `exists_tangentVectors_vectorSpace` uses the pushout
of two dual-number spectra over their closed points. For two infinitesimal points,
extend each point over the two-direction spectrum using the corresponding coordinate
projection, and multiply the two extended points. Its restriction to the first axis
is the first point times the identity; its restriction to the second is the identity
times the second point. The unit laws therefore make this the unique gluing of the
two tangent vectors. Pulling back by the sum map gives the product of the original
points, since both coordinate projections composed with the sum map are identities.
Transport by the identity residue isomorphism commutes with these coordinate maps.
Thus the prescribed map takes multiplication to tangent addition.
For scaling, `infPointsScale` is precomposition by `dualNumbersScaleOver`.
Under `dualNumbersToSpecOver`, that morphism sends epsilon to `t * epsilon`, where
`t` is the scalar read through `Scheme.ΓSpecIso`. Mapping both coefficients by `r`
turns it into the scaling map of the tangent vector-space specification. Its scalar
is `r t`, which is precisely the action of `t` under `Module.compHom`.
The two precomposition formulas agree, including when the scalar is zero.
Subtype extensionality turns these equalities of morphisms into the asserted identities.
No bijectivity or equivalence is assumed or concluded here. -/
theorem identity_tangent_transport_operations
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    letI : Module k (schemeTangentSpace k G.left G.hom x) :=
      Module.compHom (schemeTangentSpace k G.left G.hom x) r
    ∀ F : infPoints G → schemeTangentSpace k G.left G.hom x,
      (∀ v : infPoints G, (F v).val =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom r)) ≫
          (infPointsEquivTangentGroup G v).val.left) →
      (∀ v w, F (v * w) = F v + F w) ∧
      (∀ (t : k) v,
        F (infPointsScale G ((Scheme.ΓSpecIso (.of k)).inv.hom t) v) = t • F v) := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let K := G.left.residueField x
  let r : k →+* K :=
    (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
  let : Module k (schemeTangentSpace k G.left G.hom x) :=
    Module.compHom (schemeTangentSpace k G.left G.hom x) r
  dsimp only
  intro F hF
  refine ⟨identity_tangent_transport_addition G F hF, ?_⟩
  intro t v
  let U := Scheme.dualNumbersToSpec (.of k)
  let mk := Spec.map (CommRingCat.ofHom (DualNumber.scale t).toRingHom)
  let mK := Spec.map (CommRingCat.ofHom (DualNumber.scale (r t)).toRingHom)
  let d := Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom r))
  have hm : inv U ≫
      (Spec (.of k)).dualNumbersScale ((Scheme.ΓSpecIso (.of k)).inv.hom t) =
      mk ≫ inv U := by
    apply (cancel_mono U).1
    rw [Category.assoc, scale_toSpec]
    change (inv U ≫ U) ≫ mk = (mk ≫ inv U) ≫ U
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hd : d ≫ mk = mK ≫ d := by
    dsimp only [d, mk, mK]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change DualNumber.mapRingHom r (DualNumber.scale t z) =
      DualNumber.scale (r t) (DualNumber.mapRingHom r z)
    ext <;> simp [DualNumber.fst_mapRingHom, DualNumber.snd_mapRingHom, DualNumber.scale]
  have hi : (inv (dualNumbersToSpecOver (R := k))).left = inv U := by
    exact (Over.forget _).map_inv _
  apply Subtype.ext
  rw [hF]
  have hs := (Classical.choose_spec
    (Classical.choose_spec (exists_tangentVectors_vectorSpace k G.left G.hom x).2.2.2)).2.2
  change d ≫ (infPointsEquivTangentGroup G
    (infPointsScale G ((Scheme.ΓSpecIso (.of k)).inv.hom t) v)).val.left =
      ((r t) • F v).val
  rw [hs, hF]
  simp only [coe_infPointsEquivTangentGroup_apply, Over.comp_left,
    infPointsScale, Scheme.dualNumbersScaleOver_left, hi]
  change d ≫ inv U ≫
      (Spec (.of k)).dualNumbersScale ((Scheme.ΓSpecIso (.of k)).inv.hom t) ≫ v.val.left =
    Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map ((r t) • (LinearMap.id : K →ₗ[K] K))).toRingHom) ≫
        d ≫ inv U ≫ v.val.left
  rw [← Category.assoc (inv U), hm]
  simp only [Category.assoc]
  rw [← Category.assoc d mk, hd, Category.assoc]
  congr 1

end GrpObj
end AlgebraicGeometry
