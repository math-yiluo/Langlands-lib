import Langlands.GroupScheme.Absolute.TriangularSeriesCharacters
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.Torus.DiagonalizableGeometry

/-! # Actual finite quotient towers for triangular diagonal maps -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {k : Type u} [Field k]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]

omit [LocallyOfFiniteType H.X.hom] in
/-- Comparisons between two actual quotients by the same full subgroup
are isomorphisms. -/
theorem QuotientTerm.comparison_isIso {F : SubgroupFunctor H}
    (A B : QuotientTerm F) :
    IsIso (QuotientTerm.comparison A B le_rfl) := by
  have he : QuotientTerm.comparison A B le_rfl =
      (FppfQuotientComparison.iso B.isFppfQuotient A.isFppfQuotient).hom := by
    apply FppfQuotientComparison.hom_ext B.isFppfQuotient
    rw [QuotientTerm.comparison_fac, FppfQuotientComparison.iso_fac]
  rw [he]
  infer_instance

variable {N : ℕ}

omit [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom] in
/-- Every positive-size series term is contained in its first term. -/
theorem seriesHom_le_first (ρ : MatrixRepresentation H (Fin N))
    (hN : 0 < N) (t : ℕ) :
    SubgroupFunctor.range (seriesHom ρ t) ≤
      SubgroupFunctor.range (seriesHom ρ 0) := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (seriesHom_succ_le ρ hN t).trans ih

section GeneralTarget

variable {D : CommGroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType D.X.hom] [IsAffineHom D.X.hom]

/-- The supplied actual diagonal image itself is the quotient by the first
full coordinate subgroup. -/
def diagonalQuotientTerm
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (q : H ⟶ D.toGrp)
    (hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (kernelι
        (j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _))) q) :
    QuotientTerm (SubgroupFunctor.range (seriesHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _) 0)) :=
  ⟨D.toGrp, q, inferInstance, inferInstance, by
    simpa only [range_seriesHom_first] using hq⟩

/-- A supplied fppf diagonal image and generic affine-image and normal
quotient existence give an actual finite character-linear quotient tower.
The source representation is faithful on every test scheme. -/
theorem hasTower_of_affine_image_and_normal_quotient
    (himage : AffineHomImageStatement.{u})
    (hquot : AffineNormalSubgroupQuotientStatement.{u})
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    [Mono (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))).hom.hom]
    (q : H ⟶ D.toGrp)
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (hfac : q ≫ d = j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _)
    (hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (kernelι
        (j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _))) q) :
    LinearKernelTower.HasTower D (N * N) q := by
  let ρ := j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))
  have hq0 : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (seriesHom ρ 0)) q := by
    simpa only [ρ, range_seriesHom_first] using hq
  by_cases hN0 : N = 0
  · have hbot : SubgroupFunctor.range (seriesHom ρ 0) = ⊥ := by
      have hNN : N * N = 0 := by rw [hN0, Nat.zero_mul]
      exact (congrArg (fun t : ℕ => SubgroupFunctor.range (seriesHom ρ t))
        hNN).symm.trans (range_seriesHom_last ρ)
    have hqb : RelativeRoot.IsFppfQuotient ⊥ q := hbot ▸ hq0
    have : IsIso q.hom.hom := hqb.isIso_of_bot
    have hqi : IsIso q := by
      exact ⟨⟨hqb.isoOfBot.inv, hqb.isoOfBot.hom_inv_id,
        hqb.isoOfBot.inv_hom_id⟩⟩
    simpa only [hN0, Nat.zero_mul] using
      LinearKernelTower.HasTower.zero (D := D) (q := q) inferInstance inferInstance hqi
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    let A0 := diagonalQuotientTerm j q hq
    have htower : ∀ (t : ℕ)
        (B : QuotientTerm (SubgroupFunctor.range (seriesHom ρ t))),
        LinearKernelTower.HasTower D t
          (QuotientTerm.comparison A0 B (seriesHom_le_first ρ hN t)) := by
      intro t
      induction t with
      | zero =>
          intro B
          exact LinearKernelTower.HasTower.zero B.locallyOfFiniteType B.isAffineHom
            (QuotientTerm.comparison_isIso A0 B)
      | succ t ih =>
          intro B
          let A := seriesQuotient hquot j t
          let p := QuotientTerm.comparison A B (seriesHom_succ_le ρ hN t)
          let r := QuotientTerm.comparison A0 A (seriesHom_le_first ρ hN t)
          let qB := QuotientTerm.comparison A0 B (seriesHom_le_first ρ hN (t + 1))
          have hB : B.hom ≫ qB = q :=
            QuotientTerm.comparison_fac A0 B (seriesHom_le_first ρ hN (t + 1))
          have hpr : p ≫ r = qB := by
            apply FppfQuotientComparison.hom_ext B.isFppfQuotient
            rw [← Category.assoc, QuotientTerm.comparison_fac,
              QuotientTerm.comparison_fac, QuotientTerm.comparison_fac]
          obtain ⟨hflat, hsurj⟩ :=
            QuotientTerm.comparison_flat_surjective A0 B
              (seriesHom_le_first ρ hN (t + 1))
          let : Flat qB.hom.hom.left := hflat
          let : Surjective qB.hom.hom.left := hsurj
          have : QuasiCompact qB.hom.hom.left := by
            have : IsAffine B.quotient.X.left :=
              isAffine_of_isAffineHom B.quotient.X.hom
            have : IsAffine A0.quotient.X.left :=
              isAffine_of_isAffineHom A0.quotient.X.hom
            infer_instance
          exact LinearKernelTower.HasTower.succ p r B.locallyOfFiniteType B.isAffineHom
            (QuotientTerm.comparison_isFppfQuotient A B (seriesHom_succ_le ρ hN t))
            hpr
            (seriesComparison_isCharacterLinearKernel himage j q d hfac hN t A B qB hB)
            (ih A)
    have hid : RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range (seriesHom ρ (N * N))) (𝟙 H) := by
      refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
      rw [range_seriesHom_last]
      ext T x
      rw [mem_range_kernelι_iff]
      change x ≫ 𝟙 H.X = 1 ↔ x = 1
      rw [Category.comp_id]
    let B : QuotientTerm (SubgroupFunctor.range (seriesHom ρ (N * N))) :=
      ⟨H, 𝟙 H, inferInstance, inferInstance, hid⟩
    have hlast : QuotientTerm.comparison A0 B
        (seriesHom_le_first ρ hN (N * N)) = q := by
      have hf := QuotientTerm.comparison_fac A0 B
        (seriesHom_le_first ρ hN (N * N))
      change (𝟙 H) ≫ QuotientTerm.comparison A0 B
        (seriesHom_le_first ρ hN (N * N)) = q at hf
      simpa only [Category.id_comp] using hf
    simpa only [hlast] using htower (N * N) B

end GeneralTarget

/-- In particular the supplied actual diagonalizable image of any closed
triangular subgroup admits a tower, with torsion characters allowed and no
restriction on the characteristic or matrix size. -/
theorem admitsTower_diagonalizable_of_affine_image_and_normal_quotient
    (himage : AffineHomImageStatement.{u})
    (hquot : AffineNormalSubgroupQuotientStatement.{u})
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (hj : IsClosedSubgroup j)
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (d : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶
      GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ)))
    (q : H ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hfac : q ≫ d = j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _)
    (hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (kernelι
        (j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _))) q) :
    LinearKernelTower.AdmitsTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) q := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))).hom.hom :=
    (GeneralLinear.isRepresentedBy_blockParabolic (Fin N) (CommRingCat.of k) _).1
  have : Mono (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))).hom.hom := by
    change Mono (j.hom.hom ≫
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _).hom.hom)
    infer_instance
  exact ⟨N * N, hasTower_of_affine_image_and_normal_quotient
    himage hquot j q d hfac hq⟩

end Langlands.GroupScheme.TriangularLayer
