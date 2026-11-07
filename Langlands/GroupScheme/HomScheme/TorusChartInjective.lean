import Langlands.GroupScheme.HomScheme.TorusChartConstruction

/-! # Injectivity of torus charts on affine tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomScheme.TorusChart

open Langlands.Algebra Langlands.Algebra.TorusChartRing Langlands.Algebra.TorusChartAlgebra
  Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → AffineCoordinates.hopfAlgebra G} {n : ℕ}
  (d : Datum R (AffineCoordinates.hopfAlgebra G) r m gen n)

theorem uS_algebraMap (w : W R (AffineCoordinates.hopfAlgebra G) r m) :
    uS d (algebraMap (W R (AffineCoordinates.hopfAlgebra G) r m) (Localization.Away d.f) w) =
      algebraMap d.B (Bf d) (algebraMap (W R (AffineCoordinates.hopfAlgebra G) r m) d.B w) := by
  have := congrArg (fun F => F w) (uS_comp d)
  simpa [IsScalarTower.algebraMap_apply (W R (AffineCoordinates.hopfAlgebra G) r m) d.B (Bf d)]
    using this

/-- Two points of the window piece over `Spec C` with the same window torus have the same
image in the chart. -/
theorem comp_p_eq_of_evaluate_eq {C : Type u} [CommRing C] [Algebra R C] (a' b' : Bf d →ₐ[R] C)
    (h : TorusSubgroupModuli.evaluate (iS G d) (FiniteSource.specMap a') =
      TorusSubgroupModuli.evaluate (iS G d) (FiniteSource.specMap b')) :
    (FiniteSource.specMap a').left ≫ p d = (FiniteSource.specMap b').left ≫ p d := by
  rw [evaluate_iS_specMap, evaluate_iS_specMap] at h
  have hker := (SplitTorusPoint.range_splitPointEquiv_symm_eq_iff_ker
    ⟨FiniteBialgebraHom.pushPoint R a' (fS G d).1, (fS G d).2.pushPoint R a'⟩
    ⟨FiniteBialgebraHom.pushPoint R b' (fS G d).1, (fS G d).2.pushPoint R b'⟩
    (surjective_pushPoint_fS G d a') (surjective_pushPoint_fS G d b')).mp h
  have hker' : RingHom.ker (HopfPointClosedLocus.scalarExt (d.pushα (a'.comp (uS d)))) =
      RingHom.ker (HopfPointClosedLocus.scalarExt (d.pushα (b'.comp (uS d)))) := by
    ext x
    have := congrArg (fun I => x ∈ I) hker
    simp only [RingHom.mem_ker, eq_iff_iff] at this ⊢
    rw [← liftEquiv_pushPoint_fS_eq_zero_iff G d a', ← liftEquiv_pushPoint_fS_eq_zero_iff G d b']
    exact this
  apply hom_ext_of_localization
  intro P hP
  obtain ⟨γ, hγ⟩ := d.exists_act_of_ker_eq (a'.comp (uS d)) (b'.comp (uS d)) hker' P
  let loc := IsScalarTower.toAlgHom R C (Localization.AtPrime P)
  let φa : d.B →+* Localization.AtPrime P := ((loc.comp a').toRingHom).comp (algebraMap d.B (Bf d))
  let φb : d.B →+* Localization.AtPrime P := ((loc.comp b').toRingHom).comp (algebraMap d.B (Bf d))
  have hB : φb = φa.comp (d.actB γ).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers d.N)
    ext w
    have hw := congrArg (fun F => F w) hγ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', uS_algebraMap] at hw
    simp only [φa, φb, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, RingEquiv.toRingHom_eq_coe, Datum.actB_algebraMap]
    exact hw
  have e : ∀ c' : Bf d →ₐ[R] C,
      Spec.map (CommRingCat.ofHom ((loc.comp c').toRingHom.comp (algebraMap d.B (Bf d)))) =
        Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ (FiniteSource.specMap c').left ≫ ι d := by
    intro c'
    change _ = Spec.map (CommRingCat.ofHom loc.toRingHom) ≫
      Spec.map (CommRingCat.ofHom c'.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap d.B (Bf d)))
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have ha : Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ (FiniteSource.specMap a').left ≫
      ι d ≫ (quot d).map = Spec.map (CommRingCat.ofHom φa) ≫ (quot d).map := by
    rw [e a']
    simp only [Category.assoc]
  have hb : Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ (FiniteSource.specMap b').left ≫
      ι d ≫ (quot d).map = Spec.map (CommRingCat.ofHom φb) ≫ (quot d).map := by
    rw [e b']
    simp only [Category.assoc]
  have hx : Spec.map (CommRingCat.ofHom φb) =
      Spec.map (CommRingCat.ofHom φa) ≫ ((action d).act γ).hom := by
    rw [action_act_hom, ← Spec.map_comp, hB]
    rfl
  change Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ (FiniteSource.specMap a').left ≫
      ι d ≫ (quot d).map =
    Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ (FiniteSource.specMap b').left ≫
      ι d ≫ (quot d).map
  rw [ha, hb, hx, Category.assoc, FiniteFreeSchemeAction.AffineQuotient.invariant]

/-- The same statement for an arbitrary affine test scheme. -/
theorem comp_p_eq_of_evaluate_eq_affine (T : Over (Spec (CommRingCat.of R)))
    (hT : IsAffine T.left) (ya yb : T ⟶ S d)
    (h : TorusSubgroupModuli.evaluate (iS G d) ya = TorusSubgroupModuli.evaluate (iS G d) yb) :
    ya.left ≫ p d = yb.left ≫ p d := by
  let ψ : CommRingCat.of R ⟶ Γ(T.left, ⊤) :=
    Spec.preimage (T.left.isoSpec.inv ≫ T.hom : Spec Γ(T.left, ⊤) ⟶ Spec (CommRingCat.of R))
  let : Algebra R Γ(T.left, ⊤) := ψ.hom.toAlgebra
  let e : T ≅ FiniteSource.specOver R Γ(T.left, ⊤) := Over.isoMk T.left.isoSpec (by
    show T.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.hom) = T.hom
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, Iso.hom_inv_id_assoc])
  have h' := TorusSubgroupModuli.evaluate_eq_comp (iS G d) (iS G d) ya yb h e.inv
  have ha : FiniteSource.specMap (FiniteSource.specOverHomEquiv (e.inv ≫ ya)) = e.inv ≫ ya :=
    FiniteSource.specOverHomEquiv.symm_apply_apply _
  have hb : FiniteSource.specMap (FiniteSource.specOverHomEquiv (e.inv ≫ yb)) = e.inv ≫ yb :=
    FiniteSource.specOverHomEquiv.symm_apply_apply _
  rw [← ha, ← hb] at h'
  have key := comp_p_eq_of_evaluate_eq G d _ _ h'
  rw [ha, hb, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc] at key
  have hinv : e.inv.left = T.left.isoSpec.inv := rfl
  rw [hinv] at key
  exact (cancel_epi T.left.isoSpec.inv).mp key

/-- Injectivity of the chart on affine tests. -/
theorem injective_affine (T : Over (Spec (CommRingCat.of R))) (hT : IsAffine T.left)
    (a b : T ⟶ U d)
    (h : TorusSubgroupModuli.evaluate (j G d) a = TorusSubgroupModuli.evaluate (j G d) b) :
    a = b := by
  let π₁ := pullback.fst a.left (p d)
  let ya₁ := pullback.snd a.left (p d)
  let π₂ := pullback.fst (π₁ ≫ b.left) (p d)
  let yb₂ := pullback.snd (π₁ ≫ b.left) (p d)
  let c := π₂ ≫ π₁
  have := (quot d).finite
  have : IsAffineHom (p d) := by
    unfold p
    infer_instance
  have : IsAffine (pullback a.left (p d)) := isAffine_of_isAffineHom π₁
  have : IsAffine (pullback (π₁ ≫ b.left) (p d)) := isAffine_of_isAffineHom π₂
  have : Epi c := inferInstance
  have hqa : a.left ≫ qR d = T.hom := Over.w a
  have hqb : b.left ≫ qR d = T.hom := Over.w b
  have hca : c ≫ a.left = (π₂ ≫ ya₁) ≫ p d := by
    simp only [c, Category.assoc]
    rw [pullback.condition]
  have hcb : c ≫ b.left = yb₂ ≫ p d := by
    simp only [c, Category.assoc]
    exact pullback.condition
  let T₂ : Over (Spec (CommRingCat.of R)) := Over.mk (c ≫ T.hom)
  let cO : T₂ ⟶ T := Over.homMk c rfl
  let yaO : T₂ ⟶ S d := Over.homMk (π₂ ≫ ya₁) (by
    change (π₂ ≫ ya₁) ≫ (S d).hom = c ≫ T.hom
    rw [← p_qR, ← Category.assoc, ← hca, Category.assoc, hqa])
  let ybO : T₂ ⟶ S d := Over.homMk yb₂ (by
    change yb₂ ≫ (S d).hom = c ≫ T.hom
    rw [← p_qR, ← Category.assoc, ← hcb, Category.assoc, hqb])
  have ha : cO ≫ a = yaO ≫ pOver d := Over.OverMorphism.ext hca
  have hb : cO ≫ b = ybO ≫ pOver d := Over.OverMorphism.ext hcb
  have h2 := TorusSubgroupModuli.evaluate_eq_comp (j G d) (j G d) a b h cO
  rw [ha, hb, evaluate_j_comp_pOver, evaluate_j_comp_pOver] at h2
  have key := comp_p_eq_of_evaluate_eq_affine G d T₂ (inferInstanceAs
    (IsAffine (pullback (π₁ ≫ b.left) (p d)))) yaO ybO h2
  apply Over.OverMorphism.ext
  apply (cancel_epi c).mp
  rw [hca, hcb]
  exact key

end Langlands.GroupScheme.HomScheme.TorusChart
