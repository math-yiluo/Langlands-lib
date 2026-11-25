/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover

/-!
# Finite models of pointed étale neighbourhoods over an integral morphism

Source: blueprint `lemma-integral-changes-source-base--2`, integral finite-subalgebra argument.
(blueprint: lem-sbc-integral-pointed-etale-finite-model)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom.Nbhd

set_option backward.isDefEq.respectTransparency.types false in
/-- A pointed étale neighbourhood over an integral morphism has a finite model after
restricting the base to an affine neighbourhood.

Source: blueprint `lemma-integral-changes-source-base--2`, proof, integral finite-subalgebra
argument; see also the finite-subalgebra construction in `exists_hom_disjoint_cover_of_isAffine`.
(blueprint: lem-sbc-integral-pointed-etale-finite-model)

Proof: Choose an affine open of Y containing y, regarded as a pointed étale neighbourhood
c. Its pullback T to X is affine since f is integral. Write A = Γ(c) and B = Γ(T), with
B integral over A. Pull V back to T and choose a standard étale affine neighbourhood of
(v, (u,t)). This standard étale B-algebra descends to a finite A-subalgebra B₀ of B by
adjoining its finitely many presentation coefficients. Let Z = Spec B₀, let g be its
finite map to c, and let ρ be the induced map T → Z. Let W be the descended standard étale
Z-scheme. The tensor-product identification gives a map from W ×_Z T to V over X.
Lift the original geometric point through the standard étale affine chart and transport
it through the tensor-product identification. Its composites to V and T are v and (u,t),
respectively, giving r and the two required equalities. -/
theorem exists_pointed_etale_finite_model
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (t : Scheme.Hom.GeometricFiber f y) (V : X.Etale)
    (v : (Scheme.pointSmallEtale t.1).fiber.obj V) :
    ∃ (c : Scheme.Hom.Nbhd y) (Z : Scheme.{u}) (g : Z ⟶ c.1.left),
      IsFinite g ∧ ∃ (ρ : pullback c.1.hom f ⟶ Z),
      ρ ≫ g = pullback.fst c.1.hom f ∧
      ∃ (W : Z.Etale) (r : Spec (.of Ω) ⟶ pullback W.hom ρ)
        (a : pullback W.hom ρ ⟶ V.left),
        a ≫ V.hom = pullback.snd W.hom ρ ≫ pullback.snd c.1.hom f ∧
        r ≫ a = v.left ∧ r ≫ pullback.snd W.hom ρ = basePt f c t := by
  classical
  obtain ⟨c₀⟩ := IsCofiltered.nonempty (C := Scheme.Hom.Nbhd y)
  obtain ⟨U, hU, hu, -⟩ := exists_isAffineOpen_mem_and_subset (X := c₀.1.left)
    (x := c₀.2.left (default : Spec (.of Ω))) (U := ⊤) trivial
  let c := c₀.restrict U hu
  have : IsAffine c.1.left := hU
  have : IsAffine ((𝟭 Scheme).obj c.1.left) := ‹IsAffine c.1.left›
  let T := pullback c.1.hom f
  have : IsAffine T := isAffine_of_isAffineHom (pullback.fst c.1.hom f)
  let A := Γ(c.1.left, ⊤)
  let B := Γ(T, ⊤)
  let : Algebra A B := (pullback.fst c.1.hom f).appTop.hom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨fun b ↦
    ((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)).mp
      (inferInstance : IsIntegralHom (pullback.fst c.1.hom f))).2 b⟩
  let δ := pullback.snd c.1.hom f
  let z : Spec (.of Ω) ⟶ pullback V.hom δ :=
    pullback.lift v.left (basePt f c t) (by rw [basePt_snd]; exact Over.w v)
  let q := pullback.snd V.hom δ ≫ T.isoSpec.hom
  obtain ⟨P, e, he, k, hk⟩ := Etale.exists_standardEtalePair q (z default)
  have : AlgebraicGeometry.Etale (e ≫ q) := by
    rw [he]
    exact HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale B P.Ring)))
  have : AlgebraicGeometry.Etale e := AlgebraicGeometry.Etale.of_comp e q
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed e z k hk
  obtain ⟨B₀, hB₀, Q, hQ⟩ :=
    StandardEtalePair.exists_subalgebra_finite_algEquiv_tensor_ring
      (A := A) (B := B) (fun _ : Unit ↦ P)
  let E := (hQ ()).some
  let Z := Spec (.of B₀)
  let g : Z ⟶ c.1.left :=
    Spec.map (CommRingCat.ofHom (algebraMap A B₀)) ≫ c.1.left.isoSpec.inv
  have hg : IsFinite g := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B₀))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hB₀)
    infer_instance
  let ρ : T ⟶ Z := T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B₀ B))
  have hρ : ρ ≫ g = pullback.fst c.1.hom f := by
    simp only [ρ, g, Category.assoc]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    change _ ≫ Spec.map (pullback.fst c.1.hom f).appTop ≫ _ = _
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap B₀ (Q ()).Ring))) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale B₀ (Q ()).Ring)))
  let W : Z.Etale := Scheme.Etale.mk
    (Spec.map (CommRingCat.ofHom (algebraMap B₀ (Q ()).Ring)))
  let H := pullbackSpecIso B₀ B (Q ()).Ring
  let L := Spec.map (CommRingCat.ofHom E.symm.toRingEquiv.toRingHom)
  let l' := l ≫ Spec.map (CommRingCat.ofHom E.toRingEquiv.toRingHom) ≫ H.inv
  have hl' : l' ≫ pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))) W.hom =
      basePt f c t ≫ T.isoSpec.hom := by
    have hE : CommRingCat.ofHom (algebraMap B (B ⊗[B₀] (Q ()).Ring)) ≫
        CommRingCat.ofHom E.toRingEquiv.toRingHom =
        CommRingCat.ofHom (algebraMap B P.Ring) := by
      ext b
      exact E.commutes b
    change l ≫ Spec.map (CommRingCat.ofHom E.toRingEquiv.toRingHom) ≫ H.inv ≫
      pullback.fst _ _ = _
    rw [pullbackSpecIso_inv_fst', ← Spec.map_comp, hE, ← he,
      ← Category.assoc, hl]
    simp [z, q]
  let r : Spec (.of Ω) ⟶ pullback W.hom ρ :=
    pullback.lift (l' ≫ pullback.snd _ W.hom) (basePt f c t) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hl']
      rfl)
  let j : pullback W.hom ρ ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap B₀ B))) W.hom :=
    pullback.lift (pullback.snd W.hom ρ ≫ T.isoSpec.hom) (pullback.fst W.hom ρ) (by
      rw [Category.assoc, ← pullback.condition])
  let a : pullback W.hom ρ ⟶ V.left := j ≫ H.hom ≫ L ≫ e ≫ pullback.fst V.hom δ
  have hj : r ≫ j = l' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, j, pullback.lift_fst, r, hl']
      rw [pullback.lift_snd_assoc]
    · simp [j, r]
  have hL : (j ≫ H.hom ≫ L) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B P.Ring)) =
      pullback.snd W.hom ρ ≫ T.isoSpec.hom := by
    have hE : CommRingCat.ofHom (algebraMap B P.Ring) ≫
        CommRingCat.ofHom E.symm.toRingEquiv.toRingHom =
        CommRingCat.ofHom (algebraMap B (B ⊗[B₀] (Q ()).Ring)) := by
      ext b
      exact E.symm.commutes b
    simp only [L, Category.assoc]
    rw [← Spec.map_comp, hE, pullbackSpecIso_hom_fst']
    exact pullback.lift_fst _ _ _
  refine ⟨c, Z, g, hg, ρ, hρ, W, r, a, ?_, ?_, pullback.lift_snd _ _ _⟩
  · have heδ : e ≫ pullback.snd V.hom δ =
        Spec.map (CommRingCat.ofHom (algebraMap B P.Ring)) ≫ T.isoSpec.inv := by
      rw [← he]
      simp [q]
    change (j ≫ H.hom ≫ L ≫ e ≫ pullback.fst V.hom δ) ≫ V.hom = _
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc e, heδ]
    simp only [Category.assoc]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun h ↦ h ≫ T.isoSpec.inv ≫ δ) hL
  · change r ≫ j ≫ H.hom ≫ L ≫ e ≫ pullback.fst V.hom δ = v.left
    rw [← Category.assoc r, hj]
    simp only [l', L, H, Category.assoc, Iso.inv_hom_id_assoc]
    have hEE : CommRingCat.ofHom E.symm.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom E.toRingEquiv.toRingHom = 𝟙 (CommRingCat.of P.Ring) := by
      ext x
      exact E.apply_symm_apply x
    rw [← Spec.map_comp_assoc, hEE, Spec.map_id, Category.id_comp,
      ← Category.assoc, hl]
    exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme.Hom.Nbhd
