/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Quasi-coherent algebras on nested affine opens

Source: Stacks Project, Constructions, Lemmas 01LN and 01LO
(blueprint: lem-weil-pbc-quasi-coherent-algebra-affine-inclusion).

The tensor comparison is expressed as a pushout square of commutative rings.
By `CommRingCat.isPushout_tensorProduct`, this says exactly that the canonical map
`A(V) ⊗[𝒪(V)] 𝒪(U) → A(U)` is an isomorphism; its pure-tensor formula is
`a ⊗ r ↦ res(a) * σ_U(r)`. This avoids choosing extra algebra instances for sections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On nested affine opens, the canonical tensor comparison for a quasi-coherent algebra
is an isomorphism (the ring square is a pushout). Its spectrum square, using the canonical
charts `U.2.isoSpec`, is cartesian. The spectrum restriction is an open immersion whose image
is the inverse image of the smaller open in the larger one, with the structure map to `U`
given by that square. Spectrum restrictions compose and the self-restriction is the identity.
Source: Stacks Project, Constructions, Lemmas 01LN and 01LO
(blueprint: lem-weil-pbc-quasi-coherent-algebra-affine-inclusion).

Proof: (1) Apply lem-weil-pbc-quasi-coherent-affine-section-base-change to `A.toModule`.
The resulting module comparison respects products and units by the algebra-sheaf structure,
so the canonical tensor comparison is a ring isomorphism, or equivalently the ring square
is a pushout. (2) By lem-weil-pbc-fibre-product-affine-spectra the affine fibre product is
Spec of the tensor product; (1) identifies it with Spec A(U). Base change of the inclusion
U → V is an open immersion and identifies its image with the preimage of U, by
lem-weil-pbc-open-preimage-fibre-product. (3) Restriction maps compose and self-restrictions
are identities. Contravariant functoriality of Spec gives the last two equations. -/
theorem quasi_coherent_algebra_affine_inclusion
    (S : Scheme.{u}) (A : S.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent) :
    (∀ (U V : S.affineOpens) (hUV : U.1 ≤ V.1),
      IsPushout (A.hom.hom.app (op V.1)) (S.presheaf.map (homOfLE hUV).op)
        (A.right.obj.map (homOfLE hUV).op) (A.hom.hom.app (op U.1)) ∧
      IsPullback (Spec.map (A.right.obj.map (homOfLE hUV).op))
        (Spec.map (A.hom.hom.app (op U.1)) ≫ U.2.isoSpec.inv)
        (Spec.map (A.hom.hom.app (op V.1)) ≫ V.2.isoSpec.inv) (S.homOfLE hUV) ∧
      IsOpenImmersion (Spec.map (A.right.obj.map (homOfLE hUV).op)) ∧
      Set.range (Spec.map (A.right.obj.map (homOfLE hUV).op)).base =
        (Spec.map (A.hom.hom.app (op V.1)) ≫ V.2.isoSpec.inv).base ⁻¹'
          Set.range (S.homOfLE hUV).base) ∧
    (∀ (U V W : S.affineOpens) (hUV : U.1 ≤ V.1) (hVW : V.1 ≤ W.1),
      Spec.map (A.right.obj.map (homOfLE hUV).op) ≫
        Spec.map (A.right.obj.map (homOfLE hVW).op) =
      Spec.map (A.right.obj.map (homOfLE (hUV.trans hVW)).op)) ∧
    (∀ U : S.affineOpens,
      Spec.map (A.right.obj.map (homOfLE (le_refl U.1)).op) =
        𝟙 (Spec (A.right.obj.obj (op U.1)))) := by
  constructor
  · intro U V hUV
    have hpush : IsPushout (A.hom.hom.app (op V.1))
        (S.presheaf.map (homOfLE hUV).op) (A.right.obj.map (homOfLE hUV).op)
        (A.hom.hom.app (op U.1)) := by
      let R := S.presheaf.obj (op V.1)
      let B := A.right.obj.obj (op V.1)
      let T := S.presheaf.obj (op U.1)
      let C := A.right.obj.obj (op U.1)
      let f := (A.hom.hom.app (op V.1)).hom
      let g := (S.presheaf.map (homOfLE hUV).op).hom
      let i := (A.right.obj.map (homOfLE hUV).op).hom
      let j := (A.hom.hom.app (op U.1)).hom
      let : Algebra R B := f.toAlgebra
      let : Algebra R T := g.toAlgebra
      let : Algebra R C := (i.comp f).toAlgebra
      have hn : i.comp f = j.comp g := by
        exact congrArg CommRingCat.Hom.hom (A.hom.hom.naturality (homOfLE hUV).op).symm
      let fi : B →ₐ[R] C := { i with commutes' := fun r ↦ rfl }
      let gj : T →ₐ[R] C := { j with
        commutes' := fun r ↦ (DFunLike.congr_fun hn r).symm }
      let q := Algebra.TensorProduct.productMap fi gj
      have : A.toModule.IsQuasicoherent := hA
      obtain ⟨c, hc, _, hct⟩ :=
        Scheme.Modules.quasiCoherent_affine_section_baseChange S A.toModule U V hUV
      have he : ∀ t, q t = c t := by
        intro t
        induction t using TensorProduct.inductionOn with
        | tmul b t =>
          rw [Algebra.TensorProduct.productMap_apply_tmul, hct]
          change i b * j t = j t * i b
          exact mul_comm _ _
        | add x y hx hy => simp [hx, hy]
      have hq : Function.Bijective q := by
        change Function.Bijective (fun t ↦ q t)
        rw [show (fun t ↦ q t) = (fun t ↦ c t) from funext he]
        exact hc
      let e := (RingEquiv.ofBijective q.toRingHom hq).toCommRingCatIso
      refine (CommRingCat.isPushout_tensorProduct R B T).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by rfl) (by rfl) ?_ ?_
      · ext b
        change q (TensorProduct.tmul R b 1) = i b
        exact Algebra.TensorProduct.productMap_left_apply fi gj b
      · ext t
        change q (TensorProduct.tmul R 1 t) = j t
        exact Algebra.TensorProduct.productMap_right_apply fi gj t
    have hp := isPullback_SpecMap_of_isPushout _ _ _ _
      hpush
    have hc : Spec.map (S.presheaf.map (homOfLE hUV).op) ≫ V.2.isoSpec.inv =
        U.2.isoSpec.inv ≫ S.homOfLE hUV := by
      rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, S.homOfLE_ι]
      exact V.2.map_fromSpec U.2 (homOfLE hUV).op
    have h : IsPullback (Spec.map (A.right.obj.map (homOfLE hUV).op))
        (Spec.map (A.hom.hom.app (op U.1)) ≫ U.2.isoSpec.inv)
        (Spec.map (A.hom.hom.app (op V.1)) ≫ V.2.isoSpec.inv) (S.homOfLE hUV) :=
      hp.of_iso (Iso.refl _) (Iso.refl _) U.2.isoSpec.symm V.2.isoSpec.symm
        (by simp) (by simp) (by simp) hc
    have hi : IsOpenImmersion (Spec.map (A.right.obj.map (homOfLE hUV).op)) :=
      MorphismProperty.of_isPullback h.flip inferInstance
    refine ⟨hpush, h, hi, ?_⟩
    simpa using Scheme.image_preimage_eq_of_isPullback h.flip Set.univ
  · constructor
    · intro U V W hUV hVW
      rw [← Spec.map_comp, ← A.right.obj.map_comp]
      rfl
    · intro U
      change Spec.map (A.right.obj.map (𝟙 (op U.1))) = _
      rw [A.right.obj.map_id, Spec.map_id]

end AlgebraicGeometry
