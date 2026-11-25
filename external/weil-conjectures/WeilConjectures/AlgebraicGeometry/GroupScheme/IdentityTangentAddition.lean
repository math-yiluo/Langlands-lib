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
# Compatibility of identity tangent transport with the vector-space operations

Source: blueprint `def-wf-lie-algebra-derivation` and
`lemma-connected-components-images-homomorphisms--3`, Multiplication paragraph (blueprint:
lem-ag-identity-tangent-addition).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped MonObj
namespace AlgebraicGeometry.GrpObj

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed identity tangent transport sends infinitesimal multiplication to addition.
Source: blueprint `def-wf-lie-algebra-derivation`;
`lemma-connected-components-images-homomorphisms--3`, Multiplication paragraph; Stacks Project, Tag
0B2B, construction of tangent addition. (blueprint: lem-ag-identity-tangent-addition)

Proof: The addition formula in `exists_tangentVectors_vectorSpace` uses the pushout
of two dual-number spectra over their common closed point. Extend each infinitesimal
point over the two-direction square-zero spectrum using its coordinate projection
and multiply the resulting over-morphisms. On the first axis the second extension
restricts to the identity, and on the second axis the first does. The group unit laws
therefore identify the restrictions of the product with the given tangent vectors.
Uniqueness of the pushout gluing identifies this product with their gluing. Pulling
back by the sum map recovers the product of the original points, because both
coordinate projections composed with that map are identities. Transport by the
identity residue isomorphism commutes with those coordinate projections and the sum
map. The sum formula and subtype extensionality now give the asserted equality.
No bijectivity or scalar compatibility is assumed or concluded. -/
theorem identity_tangent_transport_addition
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
      ∀ v w, F (v * w) = F v + F w := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let K := G.left.residueField x
  let b := G.left.fromSpecResidueField x
  let c := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
  let q := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
  let rE := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K (Fin 2 → K)))
  let D := Over.mk (q ≫ b ≫ G.hom)
  let E := Over.mk (rE ≫ b ≫ G.hom)
  let j : Fin 2 → (D ⟶ E) := fun i ↦ Over.homMk (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)) (by
      change _ ≫ rE ≫ b ≫ G.hom = q ≫ b ≫ G.hom
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact TrivSqZeroExt.map_inl _ z)
  let a : Fin 2 → (E ⟶ D) := fun i ↦ Over.homMk (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (LinearMap.single K (fun _ : Fin 2 ↦ K) i)).toRingHom)) (by
      change _ ≫ q ≫ b ≫ G.hom = rE ≫ b ≫ G.hom
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact TrivSqZeroExt.map_inl _ z)
  let s : D ⟶ E := Over.homMk (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map
      ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1)).toRingHom)) (by
      change _ ≫ rE ≫ b ≫ G.hom = q ≫ b ≫ G.hom
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact TrivSqZeroExt.map_inl _ z)
  have hja (i l : Fin 2) : (j i ≫ a l).left =
      if i = l then 𝟙 _ else q ≫ c := by
    change Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.map (LinearMap.single K (fun _ : Fin 2 ↦ K) l)).toRingHom) = _
    split_ifs with h
    · subst l
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      ext <;> simp [LinearMap.single_apply]
    · dsimp only [q, c]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      ext <;> simp [LinearMap.single_apply, h]
  have hsa (i : Fin 2) : s ≫ a i = 𝟙 D := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.map (LinearMap.single K (fun _ : Fin 2 ↦ K) i)).toRingHom) = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    ext <;> fin_cases i <;> simp [LinearMap.single_apply]
  dsimp only
  intro F hF v w
  let V : infPoints G → (D ⟶ G) := fun z ↦ Over.homMk (F z).val (F z).property.2
  let Θ : E ⟶ G := (a 0 ≫ V v) * (a 1 ≫ V w)
  have hconst (z : infPoints G) :
      (Over.homMk (q ≫ c ≫ (F z).val) (by
        rw [Category.assoc, Category.assoc, (F z).property.2]
        change q ≫ c ≫ q ≫ b ≫ G.hom = q ≫ b ≫ G.hom
        have hcq : c ≫ q = 𝟙 _ := by
          dsimp only [c, q]
          rw [← Spec.map_comp, ← Spec.map_id]
          rfl
        rw [← Category.assoc c, hcq, Category.id_comp]) : D ⟶ G) = 1 := by
    apply Over.OverMorphism.ext
    change q ≫ c ≫ (F z).val = (1 : D ⟶ G).left
    rw [(F z).property.1]
    obtain ⟨_, he⟩ := identity_residue_rational G
    rw [← he]
    change q ≫ Spec.map (CommRingCat.ofHom
      ((StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom)) ≫
        unitSection G = (1 : D ⟶ G).left
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    change q ≫ Spec.map _ ≫ unitSection G = (q ≫ b ≫ G.hom) ≫ unitSection G
    rw [Category.assoc]
    congr 1
    have he' : Spec.map
        (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x) ≫
          unitSection G = b := he
    rw [← he']
    simp only [Category.assoc, unitSection_comp_hom, Category.id_comp]
    rfl
  have hjΘ (i : Fin 2) : j i ≫ Θ = if i = 0 then V v else V w := by
    dsimp only [Θ]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
    fin_cases i
    · change (j 0 ≫ a 0) ≫ V v * (j 0 ≫ a 1) ≫ V w = V v
      have h0 : j 0 ≫ a 0 = 𝟙 D := by
        apply Over.OverMorphism.ext
        change (j 0 ≫ a 0).left = 𝟙 (Spec (.of (DualNumber K)))
        simpa only [↓reduceIte] using hja 0 0
      rw [h0, Category.id_comp]
      have h1 : j 0 ≫ a 1 ≫ V w = 1 := by
        apply Over.OverMorphism.ext
        change (j 0 ≫ a 1).left ≫ (F w).val = (1 : D ⟶ G).left
        rw [hja]
        change (q ≫ c) ≫ (F w).val = (1 : D ⟶ G).left
        have h := congrArg (fun f ↦ f.left) (hconst w)
        change q ≫ c ≫ (F w).val = (1 : D ⟶ G).left at h
        simpa only [Category.assoc] using h
      simp only [Category.assoc, h1, mul_one]
    · change (j 1 ≫ a 0) ≫ V v * (j 1 ≫ a 1) ≫ V w = V w
      have h1 : j 1 ≫ a 1 = 𝟙 D := by
        apply Over.OverMorphism.ext
        change (j 1 ≫ a 1).left = 𝟙 (Spec (.of (DualNumber K)))
        simpa only [↓reduceIte] using hja 1 1
      rw [h1, Category.id_comp]
      have h0 : j 1 ≫ a 0 ≫ V v = 1 := by
        apply Over.OverMorphism.ext
        change (j 1 ≫ a 0).left ≫ (F v).val = (1 : D ⟶ G).left
        rw [hja]
        change (q ≫ c) ≫ (F v).val = (1 : D ⟶ G).left
        have h := congrArg (fun f ↦ f.left) (hconst v)
        change q ≫ c ≫ (F v).val = (1 : D ⟶ G).left at h
        simpa only [Category.assoc] using h
      simp only [Category.assoc, h0, one_mul]
  have hadd := (Classical.choose_spec
    (Classical.choose_spec (exists_tangentVectors_vectorSpace k G.left G.hom x).2.2.2)).2.1
  have hΘ0 : (j 0).left ≫ Θ.left = (F v).val := by
    have h : j 0 ≫ Θ = V v := by simpa using hjΘ 0
    exact congrArg (fun f ↦ f.left) h
  have hΘ1 : (j 1).left ≫ Θ.left = (F w).val := by
    have h : j 1 ≫ Θ = V w := by simpa using hjΘ 1
    exact congrArg (fun f ↦ f.left) h
  have hsum : (F v + F w).val = (V v * V w).left := by
    rw [hadd (F v) (F w) Θ.left hΘ0 hΘ1]
    change (s ≫ Θ).left = _
    dsimp only [Θ]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, hsa, hsa]
    simp only [Category.id_comp]
  apply Subtype.ext
  rw [hsum, hF]
  let aa : CommRingCat.of k ⟶ K :=
    StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x
  have hp : b ≫ G.hom = Spec.map aa := by
    have he := (identity_residue_rational G).2
    change Spec.map aa ≫ unitSection G = b at he
    rw [← he, Category.assoc, unitSection_comp_hom, Category.comp_id]
  let dd : D ⟶ (Spec (.of (DualNumber k))).asOver (Spec (.of k)) :=
    Over.homMk (Spec.map (CommRingCat.dualNumber.map aa)) (by
      change Spec.map (CommRingCat.dualNumber.map aa) ≫
        Spec.map (CommRingCat.dualNumberInl.app (.of k)) = q ≫ b ≫ G.hom
      rw [hp]
      change Spec.map (CommRingCat.dualNumber.map aa) ≫
        Spec.map (CommRingCat.dualNumberInl.app (.of k)) =
          Spec.map (CommRingCat.dualNumberInl.app K) ≫ Spec.map aa
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.dualNumberInl.naturality aa).symm)
  have hV (z : infPoints G) : V z = dd ≫ (infPointsEquivTangentGroup G z).val := by
    apply Over.OverMorphism.ext
    exact hF z
  rw [hV v, hV w, ← MonObj.comp_mul]
  change (dd ≫ (infPointsEquivTangentGroup G (v * w)).val).left =
    (dd ≫ ((infPointsEquivTangentGroup G v).val *
      (infPointsEquivTangentGroup G w).val)).left
  rw [map_mul]
  rfl

end AlgebraicGeometry.GrpObj
