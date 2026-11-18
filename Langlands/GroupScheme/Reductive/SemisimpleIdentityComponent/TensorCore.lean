import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.AlgClosedCore
import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.SumRepresentation
import Langlands.GroupScheme.AffineHomImage
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.MatrixRepresentationTensor
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.Reductive.ToPseudoReductive

/-! # Tensor products of semisimple representations over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SemisimpleIdentityComponent

open MatrixRepresentation IdentityComponent

variable {K : Type u} [Field K]

/-- Over an algebraically closed field, a surjective morphism locally of finite type is
surjective on rational points. -/
theorem exists_rationalPoint_lift [IsAlgClosed K] {X Y : Over (Spec (CommRingCat.of K))}
    (f : X ⟶ Y) [Surjective f.left] [LocallyOfFiniteType f.left]
    (y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Y) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, x ≫ f = y := by
  let P := Limits.pullback f.left y.left
  obtain ⟨a, ha⟩ := f.left.surjective (y.left (IsLocalRing.closedPoint (CommRingCat.of K)))
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f.left) (g := y.left) a
    (IsLocalRing.closedPoint (CommRingCat.of K)) ha
  have : Nonempty P := ⟨z⟩
  let Z : Over (Spec (CommRingCat.of K)) := Over.mk (Limits.pullback.snd f.left y.left)
  have : LocallyOfFiniteType Z.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd f.left y.left)
    infer_instance
  have : Nonempty Z.left := ⟨z⟩
  obtain ⟨w⟩ := nonempty_rationalPoints Z
  have hw : w.left ≫ Limits.pullback.snd f.left y.left = 𝟙 _ := Over.w w
  refine ⟨Over.homMk (w.left ≫ Limits.pullback.fst f.left y.left) ?_, ?_⟩
  · change (w.left ≫ Limits.pullback.fst f.left y.left) ≫ X.hom = 𝟙 _
    rw [Category.assoc, ← Over.w f, Limits.pullback.condition_assoc, ← Category.assoc, hw,
      Category.id_comp]
    exact Over.w y
  · apply Over.OverMorphism.ext
    change (w.left ≫ Limits.pullback.fst f.left y.left) ≫ f.left = y.left
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hw, Category.id_comp]

/-- Restriction along a homomorphism that is surjective on rational points does not change the
image of the rational-point representation. -/
theorem range_rationalRepresentation_restrict {J I : GroupScheme (Spec (CommRingCat.of K))}
    (q : J ⟶ I)
    (hq : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ I.X,
      ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ J.X, x ≫ q.hom.hom = y)
    {p : Type} [Fintype p] [DecidableEq p] (θ : MatrixRepresentation I p) :
    Set.range (θ.restrict q).rationalRepresentation = Set.range θ.rationalRepresentation := by
  ext T
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x ≫ q.hom.hom, LinearMap.ext fun v => ?_⟩
    rw [rationalRepresentation_apply, rationalRepresentation_apply, rationalMatrix_restrict]
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hq y
    refine ⟨x, LinearMap.ext fun v => ?_⟩
    rw [rationalRepresentation_apply, rationalRepresentation_apply, rationalMatrix_restrict]

/-- A homomorphism kills the kernel of the projection onto the image of a direct sum as soon
as it kills the kernel of one summand. -/
theorem kernelι_projection_comp_eq_zero
    {J : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom J.X.hom]
    {N : ℕ} (φ : MatrixRepresentation J (Fin N)) {L : GroupScheme (Spec (CommRingCat.of K))}
    (f : J ⟶ L) (hf : ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ J.X),
      x ≫ φ.hom.hom = 1 → x ≫ f.hom.hom = 1) :
    kernelι (AffineHomImage.projection φ) ≫ f = 0 := by
  apply Grp.hom_ext
  change (kernelι (AffineHomImage.projection φ)).hom.hom ≫ f.hom.hom = 1
  apply hf
  have h1 : (kernelι (AffineHomImage.projection φ)).hom.hom ≫
      (AffineHomImage.projection φ).hom.hom = 1 :=
    (mem_range_kernelι_iff _ _).1 (SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩)
  have hφ : φ.hom.hom = (AffineHomImage.projection φ).hom.hom ≫
      (AffineHomImage.inclusion φ).hom.hom := by
    rw [← Grp.comp_hom_hom, AffineHomImage.projection_inclusion]
  rw [hφ, ← Category.assoc, h1]
  exact MonObj.one_comp _

variable [IsAlgClosed K] [CharZero K]
  {J : GroupScheme (Spec (CommRingCat.of K))} [Smooth J.X.hom] [IsAffineHom J.X.hom]

/-- **Milne 22.44 over an algebraically closed field**, given Theorem 22.42: the tensor product
of two matrix representations with semisimple rational-point representations has semisimple
rational-point representation. -/
theorem tensor_rationalRepresentation_isSemisimple
    (h22 : CharZeroReductiveSemisimpleRepresentationStatement.{u}) {n m : ℕ}
    (ρ : MatrixRepresentation J (Fin n)) (σ : MatrixRepresentation J (Fin m))
    (hρ : ρ.rationalRepresentation.IsSemisimpleRepresentation)
    (hσ : σ.rationalRepresentation.IsSemisimpleRepresentation) :
    (ρ.tensor σ).rationalRepresentation.IsSemisimpleRepresentation := by
  let φ := ρ.sum σ
  have : Smooth (GeneralLinear.groupScheme (Fin (n + m)) (CommRingCat.of K)).X.hom :=
    GeneralLinear.smoothStatement (Fin (n + m)) _
  let I := AffineHomImage.image φ
  let q := AffineHomImage.projection φ
  let i := AffineHomImage.inclusion φ
  have : Smooth I.X.hom := AffineHomImage.smooth_image φ
  have : IsReduced I.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ I.X.hom
  have : QuasiCompact q.hom.hom.left :=
    inferInstanceAs (QuasiCompact (AffineHomImage.projectionOver φ).left)
  have : IsDominant q.hom.hom.left := inferInstance
  obtain ⟨hqf, hqs, -⟩ := dominantGroupHomFlat K J I q
  have : LocallyOfFiniteType q.hom.hom.left := by
    have h : LocallyOfFiniteType (q.hom.hom.left ≫ I.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp q.hom.hom.left I.X.hom
  have hlift : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ I.X,
      ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ J.X, x ≫ q.hom.hom = y :=
    fun y => exists_rationalPoint_lift q.hom.hom y
  have hkρ : kernelι q ≫ ρ = 0 := by
    apply kernelι_projection_comp_eq_zero
    intro T x hx
    have h := (sum_pointMatrix_eq_one_iff ρ σ T x).1 (by
      rw [pointMatrix_apply, hx, map_one])
    rw [pointMatrix_apply] at h
    exact (GeneralLinear.pointsEquiv (Fin n) _ T).injective (h.1.trans (map_one _).symm)
  have hkσ : kernelι q ≫ σ = 0 := by
    apply kernelι_projection_comp_eq_zero
    intro T x hx
    have h := (sum_pointMatrix_eq_one_iff ρ σ T x).1 (by
      rw [pointMatrix_apply, hx, map_one])
    rw [pointMatrix_apply, pointMatrix_apply] at h
    exact (GeneralLinear.pointsEquiv (Fin m) _ T).injective (h.2.trans (map_one _).symm)
  have : Flat q.hom.hom.left := hqf
  have : Surjective q.hom.hom.left := hqs
  let π₁ : MatrixRepresentation I (Fin n) := FpqcHomDescent.hom q ρ hkρ
  let π₂ : MatrixRepresentation I (Fin m) := FpqcHomDescent.hom q σ hkσ
  have hπ₁ : π₁.restrict q = ρ := FpqcHomDescent.fac q ρ hkρ
  have hπ₂ : π₂.restrict q = σ := FpqcHomDescent.fac q σ hkσ
  have hi : MatrixRepresentation.restrict (i : MatrixRepresentation I (Fin (n + m))) q = φ :=
    AffineHomImage.projection_inclusion φ
  have hI : IsConnectedReductive (identityComponent I) := by
    apply identityComponent_isConnectedReductive_of_faithful h22 i
      (inferInstanceAs (IsClosedImmersion (AffineHomImage.inclusion φ).hom.hom.left))
    rw [← isSemisimpleRepresentation_iff_of_range_eq _ _
      (range_rationalRepresentation_restrict q hlift i), hi]
    exact sum_rationalRepresentation_isSemisimple ρ σ hρ hσ
  have hT := rationalRepresentation_isSemisimple_of_identityComponent hI.isPseudoReductive
    (π₁.tensor π₂)
  rw [← isSemisimpleRepresentation_iff_of_range_eq _ _
    (range_rationalRepresentation_restrict q hlift _), ← tensor_restrict, hπ₁, hπ₂] at hT
  exact hT

end Langlands.GroupScheme.SemisimpleIdentityComponent
