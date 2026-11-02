import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationKernelPair
import Langlands.AlgebraicGeometry.EtaleFaithfullyFlatNoetherianDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # A Noetherian ring presentation of an affine quotient

Let `E` be an étale equivalence relation with `E.U` and `E.R` affine and with an affine quotient
`q : E.U ⟶ M`. Then `q` is étale (fpqc descent from `E.t`) and faithfully flat, so
`Γ(M) → Γ(E.U)` is étale and faithfully flat. Noetherian descent of such algebras gives a ring
`A₁` of finite type over `ℤ`, an étale and faithfully flat `A₁`-algebra `B₁` and a map
`φ : B₁ → Γ(E.U)` such that `Γ(E.R)` is the tensor product `B₁ ⊗[A₁] Γ(E.U)`, through
`b ⊗ d ↦ t (φ b) * s d`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

namespace EtaleEquivalenceRelation

/-- Let `E` be an étale equivalence relation with `E.U` and `E.R` affine that has an affine
quotient. Then there are a ring `A₁` of finite type over `ℤ`, an étale and faithfully flat
`A₁`-algebra `B₁` (also of finite type over `ℤ`) and a ring map `φ : B₁ → Γ(E.U)` such that,
for the `A₁`-algebra structure on `Γ(E.U)` through `φ`, the ring map
`B₁ ⊗[A₁] Γ(E.U) → Γ(E.R)`, `b ⊗ d ↦ t (φ b) * s d`, is bijective. -/
theorem exists_fg_pushout_of_hasAffineQuotient (E : EtaleEquivalenceRelation.{u})
    [IsAffine E.U] [IsAffine E.R] (hq : E.HasAffineQuotient) :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ B₁),
      Algebra.FiniteType ℤ A₁ ∧ Algebra.FiniteType ℤ B₁ ∧ Algebra.Etale A₁ B₁ ∧
        Module.FaithfullyFlat A₁ B₁ ∧
      ∃ (φ : B₁ →+* Γ(E.U, ⊤)),
        letI : Algebra A₁ Γ(E.U, ⊤) := (φ.comp (algebraMap A₁ B₁)).toAlgebra
        ∃ F : B₁ ⊗[A₁] Γ(E.U, ⊤) →+* Γ(E.R, ⊤),
          (∀ b d, F (b ⊗ₜ d) = E.t.appTop (φ b) * E.s.appTop d) ∧ Function.Bijective F := by
  obtain ⟨M, q, hM, hpb, hfl, _, hsurj⟩ := hq
  -- The quotient map is étale by descent from `E.t`, and faithfully flat.
  have hqc : QuasiCompact q := inferInstance
  have hqet : Etale q := by
    apply MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
    · exact ⟨⟨hsurj, hfl⟩, hqc⟩
    · exact E.etale_t
  have hRet : q.appTop.hom.Etale := (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hqet
  have hRff : q.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨hfl, hsurj⟩
  let : Algebra Γ(M, ⊤) Γ(E.U, ⊤) := q.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(M, ⊤) Γ(E.U, ⊤) := RingHom.etale_algebraMap.mp hRet
  have : Module.FaithfullyFlat Γ(M, ⊤) Γ(E.U, ⊤) := RingHom.faithfullyFlat_algebraMap_iff.mp hRff
  -- Noetherian descent of the étale faithfully flat algebra `Γ(M) → Γ(E.U)`.
  obtain ⟨A₁, B₁, _, _, hA₁, hét, hff, ⟨e⟩⟩ :=
    exists_subalgebra_fg_etale_faithfullyFlat ℤ (A := Γ(M, ⊤)) (B := Γ(E.U, ⊤))
  have hA₁ft : Algebra.FiniteType ℤ A₁ := (Subalgebra.fg_iff_finiteType A₁).mp hA₁
  have hB₁ft : Algebra.FiniteType ℤ B₁ := Algebra.FiniteType.trans hA₁ft inferInstance
  let φ : B₁ →+* Γ(E.U, ⊤) :=
    ((e.symm : Γ(M, ⊤) ⊗[A₁] B₁ →ₐ[Γ(M, ⊤)] Γ(E.U, ⊤)).restrictScalars A₁).toRingHom.comp
      (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] Γ(M, ⊤) ⊗[A₁] B₁).toRingHom
  -- The pushout square `A₁ → Γ(M) → Γ(E.U)`, `A₁ → B₁ → Γ(E.U)`.
  have hI : IsPushout (CommRingCat.ofHom (algebraMap A₁ B₁))
      (CommRingCat.ofHom (algebraMap A₁ Γ(M, ⊤))) (CommRingCat.ofHom φ) q.appTop := by
    refine (CommRingCat.isPushout_of_bijective (algebraMap Γ(M, ⊤) Γ(E.U, ⊤)) φ
      (e.symm : Γ(M, ⊤) ⊗[A₁] B₁ →+* Γ(E.U, ⊤)) ?_ e.symm.bijective).flip
    intro a b
    rw [show a ⊗ₜ[A₁] b = a • ((1 : Γ(M, ⊤)) ⊗ₜ[A₁] b) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simp only [RingHom.coe_coe, map_smul, Algebra.smul_def]
    rfl
  -- Paste with the pushout square of the affine quotient.
  have hP := hI.paste_vert (isPushout_appTop_of_isPullback hpb)
  let : Algebra A₁ Γ(E.U, ⊤) := (φ.comp (algebraMap A₁ B₁)).toAlgebra
  have hT := CommRingCat.isPushout_tensorProduct A₁ B₁ Γ(E.U, ⊤)
  have hw : CommRingCat.ofHom (algebraMap A₁ Γ(E.U, ⊤)) =
      CommRingCat.ofHom (algebraMap A₁ Γ(M, ⊤)) ≫ q.appTop := by
    rw [← hI.w, ← CommRingCat.ofHom_comp]
  rw [hw] at hT
  let iso := hT.isoIsPushout _ _ hP
  refine ⟨A₁, B₁, inferInstance, inferInstance, inferInstance, hA₁ft, hB₁ft, hét, hff, φ,
    iso.hom.hom, ?_, iso.commRingCatIsoToRingEquiv.bijective⟩
  intro b d
  have hl := congrArg (fun k => k.hom b) (hT.inl_isoIsPushout_hom _ _ hP)
  have hr := congrArg (fun k => k.hom d) (hT.inr_isoIsPushout_hom _ _ hP)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hl hr
  refine Eq.trans ?_ (congrArg₂ (· * ·) hl hr)
  rw [← map_mul]
  congr 1
  simp

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
