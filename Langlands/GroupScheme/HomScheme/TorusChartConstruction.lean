import Langlands.Algebra.TorusChartRing
import Langlands.AlgebraicGeometry.SpecRingActionFree
import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionQuotient
import Langlands.AlgebraicGeometry.ConnectedCoproductFactorization
import Langlands.GroupScheme.HomScheme.SplitTorusHopfPoint
import Langlands.GroupScheme.HomScheme.TorusChartDescent
import Langlands.GroupScheme.HomScheme.RelativeGraphRecovery
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # The quotient chart of a ring-level torus chart datum -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


namespace Langlands.GroupScheme.HomScheme.TorusChart

open Langlands.Algebra Langlands.Algebra.TorusChartRing Langlands.Algebra.TorusChartAlgebra
  Langlands.AlgebraicGeometry

/-- The spectrum of a local ring is connected. -/
theorem connectedSpace_spec_of_isLocalRing (C : Type u) [CommRing C] [IsLocalRing C] :
    ConnectedSpace (Spec (CommRingCat.of C)) := by
  change ConnectedSpace (PrimeSpectrum C)
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨IsLocalRing.closedPoint C⟩, fun s hs => ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    have h1 : e = 1 := h.mul_left_cancel (he.eq.trans (mul_one e).symm)
    rw [h1, PrimeSpectrum.basicOpen_one]
    rfl
  · left
    have h0 : e = 0 := by
      have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
      exact (h.mul_left_eq_zero).mp this
    rw [h0, PrimeSpectrum.basicOpen_zero]
    rfl

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → A} {n : ℕ}

variable (d : Datum R A r m gen n)

/-- The invariant affine open `Spec B` of the parameter scheme. -/
abbrev X : Scheme.{u} := Spec (CommRingCat.of d.B)

/-- The free twisting action on `Spec B`. -/
def action : FiniteFreeSchemeAction (Γ r m) (X d) :=
  SpecRingAction.finiteFreeSchemeAction d.actB d.actB_free

theorem action_act_hom (γ : Γ r m) :
    ((action d).act γ).hom = Spec.map (CommRingCat.ofHom (d.actB γ).toRingHom) := rfl

/-- The affine quotient of `Spec B` by the twisting action: the parameter scheme of the
chart. -/
def quot : (action d).AffineQuotient := (action d).quotient

instance : IsAffine (quot d).scheme := (quot d).isAffine

/-- The structure map of `Spec B` to the base. -/
abbrev toBase : X d ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R d.B))

theorem act_comp_toBase (γ : Γ r m) : ((action d).act γ).hom ≫ toBase d = toBase d := by
  rw [action_act_hom, ← Spec.map_comp]
  congr 1
  ext x
  exact d.actB_algebraMap_R γ x

/-- The structure map of the quotient to the base. -/
def qR : (quot d).scheme ⟶ Spec (CommRingCat.of R) :=
  (quot d).desc (toBase d) (act_comp_toBase d)

@[reassoc (attr := simp)] theorem map_qR : (quot d).map ≫ qR d = toBase d :=
  (quot d).map_desc _ _

/-- The parameter scheme of the chart, as a scheme over the base. -/
abbrev U : Over (Spec (CommRingCat.of R)) := Over.mk (qR d)

/-- The coordinate ring of `D(f) ⊆ Spec B`. -/
abbrev Bf : Type u := Localization.Away (algebraMap (W R A r m) d.B d.f)

/-- The map `W_f → B_f`. -/
def uS : Localization.Away d.f →ₐ[R] Bf d :=
  IsLocalization.liftAlgHom (M := Submonoid.powers d.f)
    (f := IsScalarTower.toAlgHom R (W R A r m) (Bf d)) (by
      rintro ⟨y, k, rfl⟩
      have h : IsUnit (algebraMap d.B (Bf d) (algebraMap (W R A r m) d.B d.f)) :=
        IsLocalization.Away.algebraMap_isUnit _
      simpa [IsScalarTower.algebraMap_apply (W R A r m) d.B (Bf d)] using h.pow k)

theorem uS_comp : (uS d).comp (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f)) =
    IsScalarTower.toAlgHom R (W R A r m) (Bf d) := by
  apply AlgHom.ext
  intro w
  simp [uS, IsLocalization.lift_eq]

/-- The window piece `D(f) ⊆ Spec B`. -/
abbrev S : Over (Spec (CommRingCat.of R)) := FiniteSource.specOver R (Bf d)

/-- The inclusion of the window piece. -/
abbrev ι : (S d).left ⟶ X d := Spec.map (CommRingCat.ofHom (algebraMap d.B (Bf d)))

/-- The cover of the quotient by the window piece. -/
def p : (S d).left ⟶ (quot d).scheme := ι d ≫ (quot d).map

theorem p_qR : p d ≫ qR d = (S d).hom := by
  rw [p, Category.assoc, map_qR, ← Spec.map_comp]
  congr 1

instance : IsAffine (S d).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Bf d))))

/-- The window piece as a test object over the chart. -/
def pOver : S d ⟶ U d := Over.homMk (p d) (p_qR d)

instance : Flat (p d) := by
  unfold p
  infer_instance

instance : LocallyOfFinitePresentation (p d) := by
  unfold p
  infer_instance

/-- Every point of `Spec B` is a translate of a point of `D(f)`. -/
theorem exists_act_mem_range (y : X d) :
    ∃ γ : Γ r m, ((action d).act γ).hom.base y ∈ Set.range (ι d).base := by
  let P := Ideal.comap (algebraMap (W R A r m) d.B) y.asIdeal
  have hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hN : d.N ∉ P := by
    intro h
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.Away.algebraMap_isUnit d.N))
  obtain ⟨γ, hγ⟩ := d.cover P hP hN
  refine ⟨γ, ?_⟩
  have key : ((action d).act γ).hom.base y ∈
      PrimeSpectrum.basicOpen (algebraMap (W R A r m) d.B d.f) := by
    rw [action_act_hom]
    change algebraMap (W R A r m) d.B d.f ∉
      (PrimeSpectrum.comap (d.actB γ).toRingHom y).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    change d.actB γ (algebraMap (W R A r m) d.B d.f) ∉ y.asIdeal
    rw [Datum.actB_algebraMap]
    exact hγ
  have hr := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of d.B)
    (algebraMap (W R A r m) d.B d.f)
  have : ((action d).act γ).hom.base y ∈ (ι d).opensRange := by
    rw [hr]
    exact key
  exact this

instance : Etale (p d) := by
  have := (quot d).etale
  unfold p
  infer_instance

instance : Surjective (p d) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := (quot d).surjective.surj x
  obtain ⟨γ, z, hz⟩ := exists_act_mem_range d y
  refine ⟨z, ?_⟩
  have e1 : (ι d ≫ (quot d).map) z = (quot d).map ((ι d) z) := rfl
  have e2 : (((action d).act γ).hom ≫ (quot d).map) y =
      (quot d).map (((action d).act γ).hom y) := rfl
  change (ι d ≫ (quot d).map) z = (quot d).map y
  rw [e1, hz, ← e2, FiniteFreeSchemeAction.AffineQuotient.invariant]

/-- Two points of `Spec B` over a local ring with the same image in the quotient differ by
the action of a single element of `Γ`. -/
theorem exists_act_of_comp_eq {C : Type u} [CommRing C] [IsLocalRing C]
    (x₁ x₂ : Spec (CommRingCat.of C) ⟶ X d) (h : x₁ ≫ (quot d).map = x₂ ≫ (quot d).map) :
    ∃ γ : Γ r m, x₁ = x₂ ≫ ((action d).act γ).hom := by
  have := connectedSpace_spec_of_isLocalRing C
  let w := (quot d).isPullback.lift x₁ x₂ h
  have h1 : w ≫ (action d).target = x₁ := (quot d).isPullback.lift_fst _ _ _
  have h2 : w ≫ (action d).source = x₂ := (quot d).isPullback.lift_snd _ _ _
  obtain ⟨γ, y, hy⟩ := connectedHom_factor_coproduct (fun _ : Γ r m => X d) w
  refine ⟨γ, ?_⟩
  have hy' : y ≫ Sigma.ι (fun _ : Γ r m => X d) γ = w := hy
  have e1 : w ≫ (action d).target = y ≫ ((action d).act γ).hom := by
    rw [← hy']
    exact (Category.assoc _ _ _).trans
      (congrArg (y ≫ ·) (FiniteFreeSchemeAction.ι_target (action d) γ))
  have e2 : w ≫ (action d).source = y := by
    rw [← hy']
    exact ((Category.assoc _ _ _).trans
      (congrArg (y ≫ ·) (FiniteFreeSchemeAction.ι_source (action d) γ))).trans
      (Category.comp_id y)
  rw [← h1, ← h2, e1, e2]

/-- The ring-level form of `exists_act_of_comp_eq`. -/
theorem actB_eq_of_spec_eq {C : Type u} [CommRing C] (φ₁ φ₂ : d.B →+* C) (γ : Γ r m)
    (h : Spec.map (CommRingCat.ofHom φ₁) =
      Spec.map (CommRingCat.ofHom φ₂) ≫ ((action d).act γ).hom) :
    φ₁ = φ₂.comp (d.actB γ).toRingHom := by
  rw [action_act_hom, ← Spec.map_comp] at h
  have := Spec.map_injective h
  have h' := congrArg CommRingCat.Hom.hom this
  simpa using h'

/-- The ring maps attached to two points through `D(f)` which agree in the quotient differ,
locally at every maximal ideal, by the action of one element of `Γ`. -/
theorem exists_actB_of_specMap {C : Type u} [CommRing C] [Algebra R C]
    (a' b' : Bf d →ₐ[R] C)
    (h : (FiniteSource.specMap a').left ≫ p d = (FiniteSource.specMap b').left ≫ p d)
    (P : Ideal C) (_ : P.IsMaximal) :
    ∃ γ : Γ r m,
      ((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp a').toRingHom.comp
          (algebraMap d.B (Bf d)) =
        (((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp b').toRingHom.comp
          (algebraMap d.B (Bf d))).comp (d.actB γ).toRingHom := by
  let loc := IsScalarTower.toAlgHom R C (Localization.AtPrime P)
  have e : ∀ c' : Bf d →ₐ[R] C,
      Spec.map (CommRingCat.ofHom ((loc.comp c').toRingHom.comp (algebraMap d.B (Bf d)))) =
        Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ (FiniteSource.specMap c').left ≫ ι d := by
    intro c'
    change _ = Spec.map (CommRingCat.ofHom loc.toRingHom) ≫
      Spec.map (CommRingCat.ofHom c'.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap d.B (Bf d)))
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hx : Spec.map (CommRingCat.ofHom ((loc.comp a').toRingHom.comp (algebraMap d.B (Bf d)))) ≫
      (quot d).map =
      Spec.map (CommRingCat.ofHom ((loc.comp b').toRingHom.comp (algebraMap d.B (Bf d)))) ≫
      (quot d).map := by
    rw [e, e]
    simp only [Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ ·) h
  obtain ⟨γ, hγ⟩ := exists_act_of_comp_eq d _ _ hx
  exact ⟨γ, actB_eq_of_spec_eq d _ _ γ hγ⟩

theorem ker_pushα_uS_eq {C : Type u} [CommRing C] [Algebra R C] (a' b' : Bf d →ₐ[R] C)
    (h : ∀ (P : Ideal C) (_ : P.IsMaximal), ∃ γ : Γ r m,
      ((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp a').toRingHom.comp
          (algebraMap d.B (Bf d)) =
        (((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp b').toRingHom.comp
          (algebraMap d.B (Bf d))).comp (d.actB γ).toRingHom) :
    RingHom.ker (HopfPointClosedLocus.scalarExt (d.pushα (a'.comp (uS d)))) =
      RingHom.ker (HopfPointClosedLocus.scalarExt (d.pushα (b'.comp (uS d)))) := by
  apply HopfPointClosedLocus.ker_scalarExt_eq_of_localization
  intro P hP
  rw [d.mapAlgHom_comp_pushα, d.mapAlgHom_comp_pushα]
  obtain ⟨γ, hγ⟩ := h P hP
  apply d.ker_pushα_eq _ _ γ
  apply AlgHom.ext
  intro w
  have hw := congrArg (fun F => F (algebraMap (W R A r m) d.B w)) hγ
  have hu : ∀ w', uS d (algebraMap (W R A r m) (Localization.Away d.f) w') =
      algebraMap d.B (Bf d) (algebraMap (W R A r m) d.B w') := by
    intro w'
    have := congrArg (fun F => F w') (uS_comp d)
    simpa [IsScalarTower.algebraMap_apply (W R A r m) d.B (Bf d)] using this
  change _ = ((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp (b'.comp (uS d)))
    (algebraMap (W R A r m) (Localization.Away d.f) (act R A r m γ w))
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hu]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, Datum.actB_algebraMap] at hw
  exact hw

/-- The chart is smooth over the base when the representing algebra `W` is. -/
theorem smooth_qR (hW : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (W R A r m))))) :
    Smooth (qR d) := by
  have hB : Smooth (toBase d) := by
    have : toBase d = Spec.map (CommRingCat.ofHom (algebraMap (W R A r m) d.B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (W R A r m))) := by
      rw [← Spec.map_comp]
      congr 1
    rw [this]
    infer_instance
  have := (quot d).etale
  have := (quot d).surjective
  refine smoothEtaleSourceDescent _ _ _ (quot d).map (qR d) inferInstance inferInstance ?_
  rw [map_qR]
  exact hB


/-- Morphisms from an affine scheme to an affine scheme agreeing after every localization at
a maximal ideal agree. -/
theorem hom_ext_of_localization {C : Type u} [CommRing C] {Y : Scheme.{u}} [IsAffine Y]
    (f g : Spec (CommRingCat.of C) ⟶ Y)
    (h : ∀ (P : Ideal C) (_ : P.IsMaximal),
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.AtPrime P))) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.AtPrime P))) ≫ g) : f = g := by
  rw [← cancel_mono Y.isoSpec.hom]
  rw [← Spec.map_preimage (f ≫ Y.isoSpec.hom), ← Spec.map_preimage (g ≫ Y.isoSpec.hom)]
  congr 1
  ext x
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro P hP
  have h1 := h P hP
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap C (Localization.AtPrime P))) ≫
      Spec.map (Spec.preimage (f ≫ Y.isoSpec.hom)) =
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.AtPrime P))) ≫
      Spec.map (Spec.preimage (g ≫ Y.isoSpec.hom)) := by
    rw [Spec.map_preimage, Spec.map_preimage, reassoc_of% h1]
  rw [← Spec.map_comp, ← Spec.map_comp] at h2
  have h3 := congrArg (fun F => F.hom x) (Spec.map_injective h2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [map_sub, h3, sub_self]


end Langlands.GroupScheme.HomScheme.TorusChart

namespace Langlands.GroupScheme.HomScheme.TorusChart

open Langlands.Algebra Langlands.Algebra.TorusChartRing Langlands.Algebra.TorusChartAlgebra
  Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → AffineCoordinates.hopfAlgebra G} {n : ℕ}
  (d : Datum R (AffineCoordinates.hopfAlgebra G) r m gen n)

/-- The window Hopf point over `B_f`, in tensor form. -/
def fS : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] Bf d ⊗[R] AddMonoidAlgebra R (r → ℤ) //
    FiniteBialgebraHom.IsHopfPoint R f} :=
  ⟨ofGroupAlgebra (d.pushα (uS d)), isHopfPoint_ofGroupAlgebra (d.isHopfPoint_pushα _)⟩

/-- The split torus homomorphism over the window piece. -/
def iS : RelativeHom (splitTorus (Spec (CommRingCat.of R)) r) G (S d) :=
  (SplitTorusPoint.splitPointEquiv G (Bf d)).symm (fS G d)

theorem toGroupAlgebra_pushPoint_fS {C : Type u} [CommRing C] [Algebra R C]
    (g : Bf d →ₐ[R] C) :
    HopfPointBridge.toGroupAlgebra (FiniteBialgebraHom.pushPoint R g (fS G d).1) =
      d.pushα (g.comp (uS d)) := by
  rw [HopfPointBridge.toGroupAlgebra_pushPoint]
  change (AddMonoidAlgebra.mapAlgHom (r → ℤ) g).comp
    (HopfPointBridge.toGroupAlgebra (ofGroupAlgebra (d.pushα (uS d)))) = _
  rw [toGroupAlgebra_ofGroupAlgebra, d.mapAlgHom_comp_pushα]

theorem surjective_pushPoint_fS {C : Type u} [CommRing C] [Algebra R C] (g : Bf d →ₐ[R] C) :
    Function.Surjective (AlgHom.liftEquiv R C _ _
      (FiniteBialgebraHom.pushPoint R g (fS G d).1)) := by
  rw [surjective_liftEquiv_iff, toGroupAlgebra_pushPoint_fS]
  exact d.surjective_pushα _

theorem liftEquiv_pushPoint_fS_eq_zero_iff {C : Type u} [CommRing C] [Algebra R C]
    (g : Bf d →ₐ[R] C) (x : C ⊗[R] AffineCoordinates.hopfAlgebra G) :
    AlgHom.liftEquiv R C _ _ (FiniteBialgebraHom.pushPoint R g (fS G d).1) x = 0 ↔
      HopfPointClosedLocus.scalarExt (d.pushα (g.comp (uS d))) x = 0 := by
  have h := congrArg (fun I => x ∈ I) (ker_liftEquiv (FiniteBialgebraHom.pushPoint R g (fS G d).1))
  simp only [RingHom.mem_ker, toGroupAlgebra_pushPoint_fS] at h
  exact h.to_iff

theorem surjective_fS : Function.Surjective (AlgHom.liftEquiv R (Bf d) _ _ (fS G d).1) := by
  rw [surjective_liftEquiv_iff, fS, toGroupAlgebra_ofGroupAlgebra]
  exact d.surjective_pushα _

theorem isClosedSubgroup_iS : IsClosedSubgroup (iS G d) :=
  (SplitTorusPoint.isClosedSubgroup_splitPointEquiv_symm_iff _).mpr (surjective_fS G d)

theorem evaluate_iS_specMap {C : Type u} [CommRing C] [Algebra R C] (a' : Bf d →ₐ[R] C) :
    TorusSubgroupModuli.evaluate (iS G d) (FiniteSource.specMap a') =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm
        ⟨FiniteBialgebraHom.pushPoint R a' (fS G d).1, (fS G d).2.pushPoint R a'⟩) :=
  SplitTorusPoint.evaluate_splitPointEquiv_symm_eq_range a' (fS G d)

theorem range_pushPoint_fS_eq {C : Type u} [CommRing C] [Algebra R C] (a' b' : Bf d →ₐ[R] C)
    (h : RingHom.ker (HopfPointClosedLocus.scalarExt (d.pushα (a'.comp (uS d)))) =
      RingHom.ker (HopfPointClosedLocus.scalarExt (d.pushα (b'.comp (uS d))))) :
    SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm
        ⟨FiniteBialgebraHom.pushPoint R a' (fS G d).1, (fS G d).2.pushPoint R a'⟩) =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm
        ⟨FiniteBialgebraHom.pushPoint R b' (fS G d).1, (fS G d).2.pushPoint R b'⟩) := by
  apply (SplitTorusPoint.range_splitPointEquiv_symm_eq_iff_ker
    ⟨FiniteBialgebraHom.pushPoint R a' (fS G d).1, (fS G d).2.pushPoint R a'⟩
    ⟨FiniteBialgebraHom.pushPoint R b' (fS G d).1, (fS G d).2.pushPoint R b'⟩
    (surjective_pushPoint_fS G d a') (surjective_pushPoint_fS G d b')).mpr
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, liftEquiv_pushPoint_fS_eq_zero_iff,
    liftEquiv_pushPoint_fS_eq_zero_iff, ← RingHom.mem_ker, ← RingHom.mem_ker, h]

/-- Evaluations of the window torus at two points with the same image in the quotient
agree. -/
theorem evaluate_iS_eq {C : Type u} [CommRing C] [Algebra R C]
    (a b : FiniteSource.specOver R C ⟶ S d) (h : a.left ≫ p d = b.left ≫ p d) :
    TorusSubgroupModuli.evaluate (iS G d) a = TorusSubgroupModuli.evaluate (iS G d) b := by
  have ha : FiniteSource.specMap (FiniteSource.specOverHomEquiv a) = a :=
    FiniteSource.specOverHomEquiv.symm_apply_apply a
  have hb : FiniteSource.specMap (FiniteSource.specOverHomEquiv b) = b :=
    FiniteSource.specOverHomEquiv.symm_apply_apply b
  rw [← ha, ← hb] at h ⊢
  rw [evaluate_iS_specMap, evaluate_iS_specMap]
  exact range_pushPoint_fS_eq G d _ _
    (ker_pushα_uS_eq d _ _ (exists_actB_of_specMap d _ _ h))


instance : IsAffine ((GroupScheme.baseChange (qR d)).obj G).X.left := by
  change IsAffine (pullback G.X.hom (qR d))
  exact isAffine_of_isAffineHom (pullback.snd G.X.hom (qR d))

theorem isClosedSubgroup_i : IsClosedSubgroup (iS G d ≫
    (Descent.pullbackComparison (qR d) (p d) (S d).hom (p_qR d) G).inv) :=
  (isClosedSubgroup_iS G d).comp_iso
    (Descent.pullbackComparison (qR d) (p d) (S d).hom (p_qR d) G).symm

theorem overlap_eq :
    SubgroupFunctor.range ((GroupScheme.baseChange (Descent.fst (p d))).map
        (iS G d ≫ (Descent.pullbackComparison (qR d) (p d) (S d).hom (p_qR d) G).inv) ≫
        (Descent.canonicalOverlap (p d) ((GroupScheme.baseChange (qR d)).obj G)).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (Descent.snd (p d))).map
        (iS G d ≫ (Descent.pullbackComparison (qR d) (p d) (S d).hom (p_qR d) G).inv)) :=
  TorusChartDescent.overlap_range_eq_of_evaluate_eq (p d) (qR d) (p_qR d) (iS G d)
    (fun T a b h => TorusChartDescent.evaluate_eq_of_specOver (iS G d) (isClosedSubgroup_iS G d)
      (fun a b => a.left ≫ p d = b.left ≫ p d)
      (fun c a b h => by simp only [Over.comp_left, Category.assoc, h])
      (fun C _ _ a b h => evaluate_iS_eq G d a b h) T a b h)

theorem exists_descent : ∃ (H₀ : GroupScheme (quot d).scheme)
    (j : H₀ ⟶ (GroupScheme.baseChange (qR d)).obj G)
    (e : (GroupScheme.baseChange (p d)).obj H₀ ≅
      (GroupScheme.baseChange (S d).hom).obj (splitTorus (Spec (CommRingCat.of R)) r)),
    IsAffine H₀.X.left ∧ IsClosedSubgroup j ∧
      (GroupScheme.baseChange (p d)).map j =
        e.hom ≫ (iS G d ≫ (Descent.pullbackComparison (qR d) (p d) (S d).hom (p_qR d) G).inv) :=
  IsClosedSubgroup.exists_descent_of_overlap_range_eq (p d) (isClosedSubgroup_i G d)
    (overlap_eq G d)

/-- The descended torus over the chart. -/
def K : GroupScheme (U d).left := (exists_descent G d).choose

/-- The inclusion of the descended torus into the ambient group over the chart. -/
def j : K G d ⟶ (GroupScheme.baseChange (U d).hom).obj G :=
  (exists_descent G d).choose_spec.choose

/-- The recovery isomorphism of the descended torus over the window piece. -/
def recovery : (GroupScheme.baseChange (p d)).obj (K G d) ≅
    (GroupScheme.baseChange (S d).hom).obj (splitTorus (Spec (CommRingCat.of R)) r) :=
  (exists_descent G d).choose_spec.choose_spec.choose

theorem isAffine_K : IsAffine (K G d).X.left :=
  (exists_descent G d).choose_spec.choose_spec.choose_spec.1

theorem isClosedSubgroup_j : IsClosedSubgroup (j G d) :=
  (exists_descent G d).choose_spec.choose_spec.choose_spec.2.1

theorem baseChange_j : (GroupScheme.baseChange (p d)).map (j G d) =
    (recovery G d).hom ≫
      (iS G d ≫ (Descent.pullbackComparison (qR d) (p d) (S d).hom (p_qR d) G).inv) :=
  (exists_descent G d).choose_spec.choose_spec.choose_spec.2.2

/-- Evaluation of the chart family at points through the window piece is the window
torus. -/
theorem evaluate_j_comp_pOver {T : Over (Spec (CommRingCat.of R))} (t : T ⟶ S d) :
    TorusSubgroupModuli.evaluate (j G d) (t ≫ pOver d) =
      TorusSubgroupModuli.evaluate (iS G d) t := by
  rw [← TorusSubgroupModuli.evaluate_comp]
  have hf : TorusSubgroupModuli.familyHom (j G d) (pOver d) = (recovery G d).hom ≫ iS G d := by
    change (GroupScheme.baseChange (p d)).map (j G d) ≫
      (Descent.pullbackComparison (qR d) (p d) (S d).hom (p_qR d) G).hom = _
    rw [baseChange_j]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hf, TorusSubgroupModuli.evaluate_iso_comp]


/-- The descended family is a relative torus: it splits on the étale cover `p`. -/
theorem isTorus_K : RelativeTorus.IsTorus (K G d) := by
  refine ⟨Scheme.Hom.cover.{u} (P := @Etale) (p d) inferInstance, fun i => ?_⟩
  change IsSplitTorus ((GroupScheme.baseChange (p d)).obj (K G d))
  exact IsSplitTorus.of_iso (recovery G d) ((isSplitTorus_splitTorus r).baseChange (S d).hom)

end Langlands.GroupScheme.HomScheme.TorusChart
