import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionFamily
import Langlands.Representation.Plancherel.DiscreteSeriesHaarComparison

/-! # From the full-Levi Fourier tensor to the discrete-series Schwartz action -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

private theorem hasTemperedCoefficients_of_representationEquiv
    {Γ V W : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ Γ V} {τ : Representation ℂ Γ W}
    {Ξ σ : Γ → ℝ} (e : ρ.Equiv τ) (hT : HasTemperedCoefficients Ξ σ ρ) :
    HasTemperedCoefficients Ξ σ τ := by
  intro v ℓ
  have he : (fun g => ℓ.val (τ g v)) =
      fun g => (contragredientMap e.toIntertwiningMap ℓ).val (ρ g (e.symm v)) := by
    funext g
    change ℓ.val (τ g v) = ℓ.val (e.toIntertwiningMap (ρ g (e.symm v)))
    rw [e.toIntertwiningMap.isIntertwining, Representation.Equiv.coe_toIntertwiningMap,
      e.apply_symm_apply]
  rw [he]
  exact hT (e.symm v) (contragredientMap e.toIntertwiningMap ℓ)

open RationalSemistandard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
  (p : SemistandardSpectralIndex i) (d : CompactData p) (hdelta : ModularNormalization p)
  (A : Subgroup (rationalPoints G)) [A.Normal] (hA : A ≤ Subgroup.center (rationalPoints G))
  [MeasurableSpace (rationalPoints G ⧸ A)] [BorelSpace (rationalPoints G ⧸ A)]
  (mu : Measure (rationalPoints G ⧸ A)) [mu.IsHaarMeasure]
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
  (muM : Measure (levi p ⧸ C)) [muM.IsHaarMeasure] [muM.IsInvInvariant]

local instance : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable (hT : ∀ (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup C hC π.obj.representation muM →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj π.obj).representation)

/-- At the full-group parabolic, vanishing of the actual VII.1 tensors forces
all ambient discrete-series Schwartz actions to vanish. The central subgroups
correspond under the full-Levi equivalence and both quotient Haar scales are
arbitrary. -/
def RationalFullLeviFourierActionVanishingStatement : Prop :=
  parabolic p = ⊤ → ∀ hM : levi p = ⊤, radical p = ⊥ →
    C.map (fullLeviGroupEquiv (levi p) hM).symm.toMonoidHom = A →
      ∀ f : RationalSchwartzSpace hKc hPK ρ,
        (∀ (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
          (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation muM),
          rationalSemistandardInducedFourierTransform hG hi hν hKc hPK ρ hsw p d hdelta
            π.obj C hC muM hsq π.property.1 (hT π hsq) f = 0) →
        ∀ ω : DiscreteSeriesClass.{u, uV} A hA mu,
          ∃ ht : HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
            ω.val.out.obj.representation,
            schwartzAction (rationalL2Weights K.isOpen hKc hPK ρ hsw) ω.val.out.property.2 ht
              (Space.check (rationalXi_inv hG hi hν K.isOpen hKc hPK)
                (rationalHeight_inv ρ) f) = 0

/-- Pull back the given discrete series to the literal full Levi, cancel its
positive formal degree and transport the induced action by evaluation at one. -/
theorem rationalFullLeviFourierActionVanishing :
    RationalFullLeviFourierActionVanishingStatement hG hi hν hKc hPK ρ hsw p d hdelta
      A hA mu C hC muM hT := by
  intro hP hM hU hmap f hzero ω
  let e := fullLeviGroupEquiv (levi p) hM
  let π := ω.val.out
  let πM := IrreducibleAdmissibleRep.pullback e.symm π
  let eQ := quotientContinuousMulEquiv e.symm A C hmap
  let mu' := muM.map eQ
  let : mu'.IsHaarMeasure := eQ.isHaarMeasure_map muM
  have hsq : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation mu' := by
    change IsDiscreteSeriesClass A hA mu' (Quotient.mk _ ω.val.out)
    rw [Quotient.out_eq ω.val]
    exact (isDiscreteSeriesClass_haar_iff A hA mu mu' ω.val).mp ω.property
  have hsqM : IsSquareIntegrableModCentralSubgroup C hC πM.obj.representation muM :=
    (isSquareIntegrableModCentralSubgroup_comp_iff e.symm A hA C hC hmap mu' muM rfl
      π.obj.representation).mpr hsq
  have hoperator := rationalSemistandardFourier_operator hG hi hν hKc hPK ρ hsw
    p d hdelta πM.obj C hC muM hsqM πM.property.1 (hT πM hsqM) f
  simp only [hzero πM hsqM, map_zero] at hoperator
  have hdegree := representationFormalDegree_pos C hC muM (compactOpenCofinal p d)
    hsqM πM.property.1
  have haction := (smul_eq_zero.mp hoperator.symm).resolve_left (Complex.ofReal_ne_zero.mpr hdegree.ne')
  let inducedEquiv := fullLeviInductionEquiv (decomposition p) (isClosed_radical p) hP hM hU πM.obj
  have epullback : (fullLeviAmbientSmoothRep (levi p) hM πM.obj).representation.Equiv
      π.obj.representation :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ π.obj) fun g => by
      ext v
      change π.obj.representation (e.symm (e g)) v = π.obj.representation g v
      rw [e.symm_apply_apply]
  let ei := inducedEquiv.trans epullback
  let ht := hasTemperedCoefficients_of_representationEquiv ei (hT πM hsqM)
  refine ⟨ht, LinearMap.ext fun v => ?_⟩
  obtain ⟨w, rfl⟩ := ei.toLinearEquiv.surjective v
  have ha := schwartzAction_intertwining (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (rationalSemistandardFourierAdmissible p d πM.obj C hC muM hsqM) π.property.2
    (hT πM hsqM) ht ei.toIntertwiningMap
    (Space.check (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) f) w
  rw [haction, LinearMap.zero_apply, map_zero] at ha
  exact ha.symm

end Langlands.HarishChandraSchwartz
