/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import WeilConjectures.AlgebraicGeometry.GroupScheme.LieCotangentDualResidue

/-!
# Transport of infinitesimal points to tangent vectors at the identity

Source: blueprint `def-wf-lie-algebra-derivation` and the identity tangent-space argument of
`lemma-connected-components-images-homomorphisms--3`.

## Main definitions

* `AlgebraicGeometry.GrpObj.identityTangentTransport`: the bijection between infinitesimal
  points of `G` and tangent vectors of the scheme `G.left` at the identity, obtained by
  transporting the dual-number coefficients along the structural residue map.
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory
open scoped MonObj
namespace AlgebraicGeometry.GrpObj

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing an element of `tangentGroup G` with the dual-number map of the structural
residue map gives a tangent vector at the identity, and this assignment is bijective.

Proof: Let `a` be the structural residue map. `identity_residue_rational` proves that
it is bijective and that `Spec.map a` followed by the unit section is the canonical
residue point. The functor `CommRingCat.dualNumber` sends its ring isomorphism to an
isomorphism of dual-number rings. Naturality of `dualNumberFst` gives the closed-point
condition. Naturality of `dualNumberInl`, the over-morphism equation, and
`unitSection_comp_hom` give the base condition. Conversely precompose a tangent vector by
the inverse dual-number isomorphism. The same naturality equations give an over-morphism
reducing to the unit section, hence an element of `tangentGroup G`. Both composites are
identities by the two isomorphism cancellation equations. -/
theorem identityTangentTransport_aux
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let K := G.left.residueField x
    let d := Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom))
    ∃ h : ∀ v : tangentGroup G,
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫
            d ≫ v.val.left = G.left.fromSpecResidueField x ∧
          (d ≫ v.val.left) ≫ G.hom =
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K)) ≫
              G.left.fromSpecResidueField x ≫ G.hom,
      Function.Bijective (fun v : tangentGroup G ↦
        (⟨d ≫ v.val.left, h v⟩ : schemeTangentSpace k G.left G.hom x)) := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let K := G.left.residueField x
  let a : CommRingCat.of k ⟶ K :=
    StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x
  obtain ⟨ha, he⟩ := identity_residue_rational G
  change Function.Bijective a.hom at ha
  change Spec.map a ≫ unitSection G = G.left.fromSpecResidueField x at he
  let ae := (RingEquiv.ofBijective a.hom ha).toCommRingCatIso
  have : IsIso a := by
    change IsIso ae.hom
    infer_instance
  let b := Spec.map a
  let d := Spec.map (CommRingCat.dualNumber.map a)
  let ck := Spec.map (CommRingCat.dualNumberFst.app (.of k))
  let cK := Spec.map (CommRingCat.dualNumberFst.app K)
  let qk := Spec.map (CommRingCat.dualNumberInl.app (.of k))
  let qK := Spec.map (CommRingCat.dualNumberInl.app K)
  have : IsIso b := by dsimp [b]; infer_instance
  have : IsIso d := by dsimp [d]; infer_instance
  have hc : cK ≫ d = b ≫ ck := by
    dsimp only [cK, ck, b, d]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.dualNumberFst.naturality a)
  have hq : d ≫ qk = qK ≫ b := by
    dsimp only [qK, qk, b, d]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.dualNumberInl.naturality a).symm
  have hp : G.left.fromSpecResidueField x ≫ G.hom = b := by
    rw [← he, Category.assoc, unitSection_comp_hom, Category.comp_id]
  have h1 : (1 : points G k).left = unitSection G := by
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ unitSection G = _
    change Spec.map (𝟙 (CommRingCat.of k)) ≫ unitSection G = _
    rw [Spec.map_id, Category.id_comp]
  have ht (v : tangentGroup G) : ck ≫ v.val.left = unitSection G := by
    have h := congrArg (fun f ↦ f.left) ((mem_tangentGroup G).1 v.property)
    change ck ≫ v.val.left = (1 : points G k).left at h
    exact h.trans h1
  have hmem (v : tangentGroup G) :
      cK ≫ d ≫ v.val.left = G.left.fromSpecResidueField x ∧
        (d ≫ v.val.left) ≫ G.hom = qK ≫ G.left.fromSpecResidueField x ≫ G.hom := by
    constructor
    · rw [← Category.assoc, hc, Category.assoc, ht v]
      exact he
    · rw [Category.assoc, Over.w, hp]
      exact hq
  refine ⟨hmem, ?_⟩
  constructor
  · intro v w h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact (cancel_epi d).1 (congrArg Subtype.val h)
  · intro θ
    let v : points G (DualNumber k) := Over.homMk (inv d ≫ θ.val) (by
      change (inv d ≫ θ.val) ≫ G.hom = qk
      have hθ : θ.val ≫ G.hom = qK ≫ G.left.fromSpecResidueField x ≫ G.hom :=
        θ.property.2
      rw [Category.assoc, hθ, hp, ← hq]
      simp only [IsIso.inv_hom_id_assoc])
    have hv : v ∈ tangentGroup G := by
      rw [mem_tangentGroup]
      apply Over.OverMorphism.ext
      change ck ≫ inv d ≫ θ.val = (1 : points G k).left
      have hc' : ck ≫ inv d = inv b ≫ cK := by
        apply (cancel_epi b).1
        rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← hc]
        simp
      have hθ : cK ≫ θ.val = G.left.fromSpecResidueField x := θ.property.1
      rw [← Category.assoc, hc', Category.assoc, hθ, ← he]
      rw [h1]
      change inv b ≫ b ≫ unitSection G = unitSection G
      simp only [IsIso.inv_hom_id_assoc]
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    change d ≫ inv d ≫ θ.val = θ.val
    simp only [IsIso.hom_inv_id_assoc]

/-- Infinitesimal points of `G` are tangent vectors of the scheme `G.left` at the identity:
transport both coefficients of the dual numbers by the structural residue map `k → κ(e)`.
This is only an equivalence of types; compatibility with the operations is
`identity_tangent_transport_operations`.
Source: blueprint `def-wf-lie-algebra-derivation`, and
`lemma-connected-components-images-homomorphisms--3`, Dimension paragraph. -/
def identityTangentTransport {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    infPoints G ≃ schemeTangentSpace k G.left G.hom (unitSection G (IsLocalRing.closedPoint k)) :=
  (infPointsEquivTangentGroup G).toEquiv.trans
    (Equiv.ofBijective _ (identityTangentTransport_aux G).snd)

/-- The defining formula of `identityTangentTransport`. -/
theorem identityTangentTransport_val {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] (v : infPoints G) :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    (identityTangentTransport G v).val =
      Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom r)) ≫
        (infPointsEquivTangentGroup G v).val.left :=
  rfl

end AlgebraicGeometry.GrpObj
