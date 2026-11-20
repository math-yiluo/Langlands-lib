import Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors
import Langlands.GroupScheme.IdentityJetAffineNeighborhood
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange

/-! # Affine coordinates for the pulled-back unit neighborhood -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Algebra.SectionJet

open _root_.TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {ε : A →ₐ[R] R} {δ : B →ₐ[R] R}

private theorem augmentation_symm (e : A ≃ₐ[R] B) (he : δ.comp e.toAlgHom = ε) :
    ε.comp e.symm.toAlgHom = δ := by
  rw [← he]
  ext x
  simp

private theorem conormalMap_bijective_of_algEquiv (e : A ≃ₐ[R] B) (he : δ.comp e.toAlgHom = ε) :
    Function.Bijective (conormalMap he) := by
  refine ⟨?_, conormalMap_surjective he e.surjective⟩
  apply Function.LeftInverse.injective (g := conormalMap (augmentation_symm e he))
  intro x
  obtain ⟨a, rfl⟩ := (RingHom.ker ε).toCotangent_surjective x
  simp only [conormalMap, Ideal.mapCotangent_toCotangent]
  congr 1
  exact Subtype.ext (e.symm_apply_apply a.val)

/-- Fixed-rank smoothness along an affine section is preserved by an
augmentation-preserving algebra equivalence over the same base. -/
theorem SmoothAlongSectionOfRank.of_equiv [FinitePresentation R A] [FinitePresentation R B]
    {r : ℕ} (h : SmoothAlongSectionOfRank ε r) (e : A ≃ₐ[R] B) (he : δ.comp e.toAlgHom = ε) :
    SmoothAlongSectionOfRank δ r := by
  obtain ⟨a, ha, hsm⟩ := exists_smooth_away_of_section ε h.1
  let b := e a
  have hb : δ b = 1 := (AlgHom.congr_fun he a).trans ha
  have : Smooth R (Localization.Away a) := hsm
  have hs : Smooth R (Localization.Away b) := Smooth.of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.Away a) (Localization.Away b) e
      (Submonoid.map_powers e a))
  refine ⟨?_, ?_⟩
  · intro p hp
    let q := PrimeSpectrum.comap δ.toRingHom ⟨p, hp⟩
    have hq : q ∈ PrimeSpectrum.basicOpen b := by
      rw [PrimeSpectrum.mem_basicOpen]
      change δ b ∉ p
      rw [hb]
      exact hp.one_notMem
    exact basicOpen_subset_smoothLocus_iff_smooth.mpr hs hq
  · intro p
    let f := LinearEquiv.ofBijective (conormalMap he) (conormalMap_bijective_of_algEquiv e he)
    let pR := p.asIdeal.ResidueField
    let f' : p.asIdeal.Fiber (RingHom.ker ε).Cotangent ≃ₗ[pR]
        p.asIdeal.Fiber (RingHom.ker δ).Cotangent := AlgebraTensorModule.congr (.refl pR pR) f
    exact f'.finrank_eq.symm.trans (h.2 p)

/-- Changing the affine coordinates of an augmented algebra preserves the
fixed-rank smoothness condition in both directions. -/
theorem smoothAlongSectionOfRank_iff_equiv [FinitePresentation R A] [FinitePresentation R B]
    (e : A ≃ₐ[R] B) (he : δ.comp e.toAlgHom = ε) (r : ℕ) :
    SmoothAlongSectionOfRank ε r ↔ SmoothAlongSectionOfRank δ r :=
  ⟨fun h => h.of_equiv e he, fun h => h.of_equiv e.symm (augmentation_symm e he)⟩

/-- In an iterated scalar extension the scalar cancellation identifies the two
actual section augmentations. -/
theorem baseChangeAugmentation_cancelBaseChange {C : Type*} [CommRing C]
    [Algebra R C] [Algebra B C] [IsScalarTower R B C] (ε : A →ₐ[R] R) :
    (baseChangeAugmentation ε C).comp (Algebra.TensorProduct.cancelBaseChange R B C C A).toAlgHom =
      baseChangeAugmentation (baseChangeAugmentation ε B) C := by
  apply Algebra.TensorProduct.ext'
  intro c y
  induction y using TensorProduct.inductionOn with
  | tmul b a =>
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply R B C, mul_left_comm, mul_comm]
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]

end Algebra.SectionJet

namespace Langlands.GroupScheme.IdentityJet

open Algebra.SectionJet Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors

variable {S W T : Scheme.{u}} (G : GroupScheme S) (v : W ⟶ G.X.left)
    (e : S ⟶ W) (he : e ≫ v = G.identitySection) (b : T ⟶ S)

/-- Pullback of the affine neighborhood inclusion into the group. -/
abbrev neighborhoodBaseChangeInclusion :
    pullback (v ≫ G.X.hom) b ⟶ ((GroupScheme.baseChange b).obj G).X.left :=
  ((Over.pullback b).map (Over.homMk v rfl : Over.mk (v ≫ G.X.hom) ⟶ G.X)).left

/-- The lifted section on the affine pullback neighborhood. -/
abbrev neighborhoodBaseChangeSection : T ⟶ pullback (v ≫ G.X.hom) b :=
  pullback.lift (b ≫ e) (𝟙 T) (by
    rw [Category.assoc, ← Category.assoc e v, he, G.identitySection_comp]
    simp)

theorem neighborhoodBaseChangeSection_comp :
    neighborhoodBaseChangeSection G v e he b ≫ neighborhoodBaseChangeInclusion G v b =
      ((GroupScheme.baseChange b).obj G).identitySection := by
  apply pullback.hom_ext
  · rw [Category.assoc, identitySection_baseChange_fst]
    have hv : neighborhoodBaseChangeInclusion G v b ≫ pullback.fst G.X.hom b =
        pullback.fst (v ≫ G.X.hom) b ≫ v :=
      (RelativeIdentityComponent.overPullback_isPullback b
        (Over.homMk v rfl : Over.mk (v ≫ G.X.hom) ⟶ G.X)).w
    rw [hv, ← Category.assoc, pullback.lift_fst, Category.assoc, he]
  · change neighborhoodBaseChangeSection G v e he b ≫
      (neighborhoodBaseChangeInclusion G v b ≫ pullback.snd _ b) = _
    rw [show neighborhoodBaseChangeInclusion G v b ≫ pullback.snd G.X.hom b =
      pullback.snd (v ≫ G.X.hom) b from Over.w ((Over.pullback b).map
        (Over.homMk v rfl : Over.mk (v ≫ G.X.hom) ⟶ G.X))]
    exact (pullback.lift_snd _ _ _).trans (((GroupScheme.baseChange b).obj G).identitySection_comp.symm)

instance neighborhoodBaseChangeInclusion_isOpenImmersion [IsOpenImmersion v] :
    IsOpenImmersion (neighborhoodBaseChangeInclusion G v b) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (RelativeIdentityComponent.overPullback_isPullback b
      (Over.homMk v rfl : Over.mk (v ≫ G.X.hom) ⟶ G.X)).flip ‹IsOpenImmersion v›

variable [IsAffine S] [IsAffine W] [IsAffine T]

/-- The affine pullback neighborhood has the scalar-extended coordinate algebra. -/
def neighborhoodBaseChangeAlgEquiv :
    letI := neighborhoodAlgebra G v
    letI := b.appTop.hom.toAlgebra
    letI := neighborhoodAlgebra ((GroupScheme.baseChange b).obj G)
      (neighborhoodBaseChangeInclusion G v b)
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(W, ⊤) ≃ₐ[Γ(T, ⊤)] Γ(pullback (v ≫ G.X.hom) b, ⊤) := by
  letI := neighborhoodAlgebra G v
  letI := b.appTop.hom.toAlgebra
  letI := neighborhoodAlgebra ((GroupScheme.baseChange b).obj G)
    (neighborhoodBaseChangeInclusion G v b)
  let q := v ≫ G.X.hom
  let f := (Algebra.TensorProduct.comm Γ(S, ⊤) Γ(T, ⊤) Γ(W, ⊤)).toRingEquiv.trans
    (overlapTensorEquiv q b)
  refine { toRingEquiv := f, commutes' := ?_ }
  intro x
  change overlapTensorEquiv q b (1 ⊗ₜ[Γ(S, ⊤)] x) =
    (neighborhoodBaseChangeInclusion G v b ≫ ((GroupScheme.baseChange b).obj G).X.hom).appTop.hom x
  rw [overlapTensorEquiv_one_tmul]
  exact congrArg (fun h : pullback q b ⟶ T => h.appTop.hom x)
    (Over.w ((Over.pullback b).map (Over.homMk v rfl : Over.mk q ⟶ G.X))).symm

/-- The affine comparison sends the lifted unit to the tensor augmentation. -/
theorem neighborhoodBaseChangeAlgEquiv_aug :
    letI := neighborhoodAlgebra G v
    letI := b.appTop.hom.toAlgebra
    let K := (GroupScheme.baseChange b).obj G
    letI := neighborhoodAlgebra K (neighborhoodBaseChangeInclusion G v b)
    (neighborhoodAugmentation K (neighborhoodBaseChangeInclusion G v b)
      (neighborhoodBaseChangeSection G v e he b) (neighborhoodBaseChangeSection_comp G v e he b)).comp
      (neighborhoodBaseChangeAlgEquiv G v b).toAlgHom =
      baseChangeAugmentation (neighborhoodAugmentation G v e he) Γ(T, ⊤) := by
  let := neighborhoodAlgebra G v
  let := b.appTop.hom.toAlgebra
  let := neighborhoodAlgebra ((GroupScheme.baseChange b).obj G)
    (neighborhoodBaseChangeInclusion G v b)
  let q := v ≫ G.X.hom
  let e' := neighborhoodBaseChangeSection G v e he b
  apply Algebra.TensorProduct.ext'
  intro x y
  change e'.appTop.hom (overlapTensorEquiv q b (y ⊗ₜ[Γ(S, ⊤)] x)) = _
  rw [overlapTensorEquiv_tmul, map_mul, baseChangeAugmentation_tmul]
  have hfst : e' ≫ pullback.fst q b = b ≫ e := pullback.lift_fst _ _ _
  have hsnd : e' ≫ pullback.snd q b = 𝟙 T := pullback.lift_snd _ _ _
  have h₁ := congrArg Scheme.Hom.appTop hfst
  have h₂ := congrArg Scheme.Hom.appTop hsnd
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h₁
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h₂
  rw [show e'.appTop.hom ((pullback.fst q b).appTop.hom y) =
      b.appTop.hom (e.appTop.hom y) from ConcreteCategory.congr_hom h₁ y,
    show e'.appTop.hom ((pullback.snd q b).appTop.hom x) = x from ConcreteCategory.congr_hom h₂ x]
  exact mul_comm _ _

variable [IsOpenImmersion v] [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]

/-- On an affine test, the actual fixed-rank unit condition is the ring
condition for the scalar extension of any affine unit neighborhood. -/
theorem smoothAlongUnitOfRank_baseChange_iff_affine (r : ℕ) :
    letI := neighborhoodAlgebra G v
    letI := b.appTop.hom.toAlgebra
    SmoothAlongUnitOfRank ((GroupScheme.baseChange b).obj G) r ↔
      SmoothAlongSectionOfRank (baseChangeAugmentation (neighborhoodAugmentation G v e he) Γ(T, ⊤)) r := by
  let := neighborhoodAlgebra G v
  let := b.appTop.hom.toAlgebra
  let K := (GroupScheme.baseChange b).obj G
  let q := v ≫ G.X.hom
  let v' := neighborhoodBaseChangeInclusion G v b
  let e' := neighborhoodBaseChangeSection G v e he b
  have he' := neighborhoodBaseChangeSection_comp G v e he b
  let := neighborhoodAlgebra K v'
  have : IsSeparated K.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom b))
  have : LocallyOfFinitePresentation K.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom b))
  have : LocallyOfFinitePresentation q := inferInstance
  have : LocallyOfFinitePresentation (v' ≫ K.X.hom) := inferInstance
  have : Algebra.FinitePresentation Γ(S, ⊤) Γ(W, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) q inferInstance
  have : Algebra.FinitePresentation Γ(T, ⊤) Γ(pullback q b, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) (v' ≫ K.X.hom) inferInstance
  exact (smoothAlongUnitOfRank_iff_neighborhood K v' e' he' r).trans
    (smoothAlongSectionOfRank_iff_equiv (neighborhoodBaseChangeAlgEquiv G v b)
      (neighborhoodBaseChangeAlgEquiv_aug G v e he b) r).symm

end Langlands.GroupScheme.IdentityJet
