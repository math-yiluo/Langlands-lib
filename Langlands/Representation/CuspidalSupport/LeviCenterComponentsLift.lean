import Langlands.CategoryTheory.AdjointCenterLift
import Langlands.Representation.Category.ProjectiveFamilyDetection
import Langlands.Representation.CuspidalSupport.LeviCenterDescent
import Langlands.Representation.CuspidalSupport.InducedProgeneratorCenterInclusionProof
import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndFreeReduction
import Langlands.Representation.CuspidalSupport.RestrictionConstituentExistence
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.NormalHeckeTwist
import Langlands.Representation.Exponents.LeviInductionStages
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingProof
import Langlands.Representation.Families.InducedTwistsDetectionOpposite

/-! # Central components lift through actual parabolic induction (Renard VI.10.5)

For an actual rational parabolic `P = MU` of a connected reductive `G`, every component
`z.app (i_P^G σ)` of an element `z` of the centre of the category of smooth representations of
`G(F)` is `i_P^G(y)` for an endomorphism `y` of `σ`, provided the second adjointness theorem
(Renard VI.9.6) and the joint special-compact basis (Renard V.5.1–V.5.2) hold.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Generators

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U Q L V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviCenterLiftAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- **Lifts on the induced summand progenerators.** Let `P = MU` be an actual rational
parabolic of `G`, `Q = LV` an actual rational parabolic of `M`, `τ` an irreducible
supercuspidal representation of `L(F)`, `ρ₀ ↪ τ|_{⁰L(F)}` irreducible and
`Π_D = ind_{⁰L(F)}^{L(F)} ρ₀`. For every `z` in the centre of the category of smooth
representations of `G(F)`, the component of `z` at `i_P^G(i_Q^M Π_D)` is `i_P^G(f)` for an
endomorphism `f` of `i_Q^M Π_D`; one may take `f = i_Q^M(ζ)` with `ζ` central in `End(Π_D)`. -/
theorem exists_map_eq_center_app_leviInduction_summandInduction
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ M) (n : L ⟶ Q) (s : V ⟶ Q)
    (hq : IsParabolicSubgroup q) (hn : IsRationalLeviSubgroup n)
    (hs : LeviSubgroup.IsGeometricUnipotentRadical s)
    (hmulQ : IsIso (subgroupMultiplication n s)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    haveI := hn.isConnectedReductive.isAffineHom
    haveI : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
    haveI := hn.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology n hn
    haveI : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q n hq hn
    haveI : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q n hq hn
    ∀ τ : SmoothRep.{0, u, v} ℂ (rationalPoints L), τ.IsIrreducible → IsSupercuspidal τ →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel L),
      ρ₀.IsIrreducible →
      ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel L) τ,
        Function.Injective (SmoothRep.hom j) →
        ∀ z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
          let X := (leviInductionFunctor.{u, max u v} q n s hq hs hn hmulQ).obj
            (CuspidalSupport.rationalNormKernelSummandInduction L ρ₀)
          ∃ f : X ⟶ X, (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).map f =
            z.app ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj X) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hn.isConnectedReductive.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hn.isConnectedReductive.smooth
  let := leviPointTopology n hn
  have := leviPoints_locallyCompactSpace q n hq hn
  have := leviPoints_nonarchimedeanGroup q n hq hn
  intro τ hτ hsc ρ₀ hρ₀ j hj z
  let D := LeviParabolicExtensionDatum.ofExtension hG p l r hp hl hr hmul q n s hq hn hs hmulQ
  obtain ⟨θ⟩ := D.leviInduction_iso hG p l r hp hl hr hmul q n s hq hn hs hmulQ
  let piD := CuspidalSupport.rationalNormKernelSummandInduction L ρ₀
  let IR := leviInductionFunctor.{u, max u v} D.pR D.nR D.rR D.hpR D.hrR D.hnR D.hmulR
  have hcent := inducedProgeneratorCenterInclusion.{u, v} k G hG D.R L D.W D.pR D.nR D.rR
    D.hpR D.hnR D.hrR D.hmulR τ hτ hsc ρ₀ hρ₀ j hj
  have hmem : End.of (z.app (IR.obj piD)) ∈ Subring.center (End (IR.obj piD)) := by
    rw [Subring.mem_center_iff]
    intro a
    apply End.ext
    simp only [End.mul_asHom]
    exact (CatCenter.naturality z a.asHom).symm
  have hmem' : End.of (z.app (IR.obj piD)) ∈ (Subring.center (End (IR.obj piD)) :
      Set (End (IR.obj piD))) := hmem
  rw [hcent] at hmem'
  obtain ⟨ζ, -, hζ, -⟩ := hmem'
  refine ⟨(leviInductionFunctor.{u, max u v} q n s hq hs hn hmulQ).map ζ.asHom, ?_⟩
  have hz : z.app (IR.obj piD) = IR.map ζ.asHom := congrArg End.asHom hζ
  have h1 := CatCenter.naturality z (θ.hom.app piD)
  have h2 := θ.hom.naturality ζ.asHom
  rw [hz] at h1
  rw [← cancel_epi (θ.hom.app piD)]
  exact h2.symm.trans h1.symm


/-- **Projective induced summand progenerators detect irreducibles.** Assume the second
adjointness theorem and the joint special-compact basis. For every irreducible smooth
representation `D` of `G(F)` there are an actual rational parabolic `Q = LV` of `G`, an
irreducible supercuspidal `τ` of `L(F)` and an irreducible `ρ₀ ↪ τ|_{⁰L(F)}` such that
`i_Q^G(ind_{⁰L(F)}^{L(F)} ρ₀)` is projective and has a nonzero map to `D`. -/
theorem exists_projective_summandInduction_ne_zero
    (hSA : LeviSecondAdjointnessStatement.{u, v})
    (hJ : JointSpecialCompactBasisExistenceStatement.{u})
    (hG : IsConnectedReductive G)
    (D : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) (hD : D.IsIrreducible) :
    ∃ (Q L V : GroupScheme (Spec (CommRingCat.of k)))
      (q : Q ⟶ G) (n : L ⟶ Q) (s : V ⟶ Q)
      (hq : IsParabolicSubgroup q) (hn : IsRationalLeviSubgroup n)
      (hs : LeviSubgroup.IsGeometricUnipotentRadical s)
      (hmulQ : IsIso (subgroupMultiplication n s)),
      haveI := hn.isConnectedReductive.isAffineHom
      haveI : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
      haveI := hn.isConnectedReductive.smooth
      letI : TopologicalSpace (rationalPoints L) := leviPointTopology n hn
      haveI : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q n hq hn
      haveI : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q n hq hn
      ∃ (τ : SmoothRep.{0, u, max u v} ℂ (rationalPoints L)) (_ : τ.IsIrreducible)
        (_ : IsSupercuspidal τ)
        (ρ₀ : SmoothRep.{0, u, max u v} ℂ (Plancherel.rationalCommonNormKernel L))
        (_ : ρ₀.IsIrreducible)
        (j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel L) τ)
        (_ : Function.Injective (SmoothRep.hom j)),
        Projective ((leviInductionFunctor.{u, max u v} q n s hq hs hn hmulQ).obj
          (CuspidalSupport.rationalNormKernelSummandInduction L ρ₀)) ∧
        ∃ a : (leviInductionFunctor.{u, max u v} q n s hq hs hn hmulQ).obj
            (CuspidalSupport.rationalNormKernelSummandInduction L ρ₀) ⟶ D, a ≠ 0 := by
  obtain ⟨Q, L, V, q, n, s, hq, hn, hs, hmulQ, -, -, ρ, hρ, hρsc, ⟨qJ, hqJ⟩, -⟩ :=
    leviCuspidalEmbedding.{u, max u v} k G hG D hD
  obtain ⟨Qb, Vb, qb, nb, vb, -, hqb, hnb, hvb, hmulb, hcomp, hinf, -, -, -⟩ :=
    Langlands.Renard.AlgebraicFamily.InducedTwistsDetection.exists_opposite_parabolic hG hq hn
  have := hn.isConnectedReductive.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hn.isConnectedReductive.smooth
  let := leviPointTopology n hn
  have := leviPoints_locallyCompactSpace q n hq hn
  have := leviPoints_nonarchimedeanGroup q n hq hn
  have hinf' : pointImage qb ⊓ pointImage q = pointImage (nb ≫ qb) := by
    rw [inf_comm, hinf, hcomp]
  obtain ⟨adjQ⟩ := hSA k G hG Qb Q L Vb V qb nb vb hqb hnb hvb hmulb q n s hq hn hs hmulQ
    hcomp.symm hinf'
  have hleft : (leviJacquetFunctor.{u, max u v} q n s hq hs hn hmulQ).IsLeftAdjoint :=
    (leviFirstAdjunction.{u, v} q n s hq hs hn hmulQ).isLeftAdjoint
  -- an irreducible constituent of the restriction to the norm kernel
  obtain ⟨W, hW⟩ := CuspidalSupport.rationalNormKernelConstituent_of_finiteRestriction
    CuspidalSupport.rationalNormKernelFiniteRestriction.{u, max u v} k L hn.isConnectedReductive
    ρ hρ
  let H0 := Plancherel.rationalCommonNormKernel L
  let ρ₀ := SmoothRep.subrepresentation (SmoothRep.restrictSubgroup H0 ρ) W
  have hρ₀ : ρ₀.IsIrreducible := hW
  let j := SmoothRep.subtype (SmoothRep.restrictSubgroup H0 ρ) W
  have hj : Function.Injective (SmoothRep.hom j) :=
    SmoothRep.subtype_injective (SmoothRep.restrictSubgroup H0 ρ) W
  have hproj : Projective (CuspidalSupport.rationalNormKernelSummandInduction L ρ₀) :=
    projective_rationalNormKernelSummandInduction_of_jointSpecialCompact.{u, max u v} hJ
      q n hq hn ρ hρsc ρ₀ j hj
  -- the nonzero map `Π_D → ρ` given by Frobenius reciprocity
  have hH0 : IsOpen (H0 : Set (rationalPoints L)) := Plancherel.isOpen_rationalCommonNormKernel L
  let φ₁ : CuspidalSupport.rationalNormKernelSummandInduction L ρ₀ ⟶ ρ :=
    (CuspidalSupport.NormalHecke.inducedHomEquiv H0 ρ₀ hH0 ρ).symm (SmoothRep.hom j)
  have hφ₁ : φ₁ ≠ 0 := by
    intro h0
    let : ρ₀.representation.IsIrreducible := hρ₀
    let : Nontrivial ρ₀ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H0)
      ρ₀.representation.asModule
    obtain ⟨w, hw⟩ := exists_ne (0 : ρ₀)
    apply hw
    apply hj
    have h1 := (CuspidalSupport.NormalHecke.inducedHomEquiv H0 ρ₀ hH0 ρ).apply_symm_apply
      (SmoothRep.hom j)
    change CuspidalSupport.NormalHecke.inducedHomEquiv H0 ρ₀ hH0 ρ φ₁ = _ at h1
    rw [h0, map_zero] at h1
    rw [map_zero, ← h1]
    rfl
  -- lift it through the surjection `r_Q(D) → ρ`
  let J := (leviJacquetFunctor.{u, max u v} q n s hq hs hn hmulQ).obj D
  let qJ' : J ⟶ ρ := SmoothRep.ofHom qJ
  have : Epi qJ' := (SmoothRep.epi_iff_surjective qJ').mpr hqJ
  let ψ : CuspidalSupport.rationalNormKernelSummandInduction L ρ₀ ⟶ J :=
    Projective.factorThru φ₁ qJ'
  have hψ : ψ ≠ 0 := by
    intro h
    apply hφ₁
    rw [← Projective.factorThru_comp φ₁ qJ']
    change ψ ≫ qJ' = 0
    rw [h, zero_comp]
  refine ⟨Qb, L, Vb, qb, nb, vb, hqb, hnb, hvb, hmulb, ρ, hρ, hρsc, ρ₀, hρ₀, j, hj,
    adjQ.map_projective _ hproj, (adjQ.homEquiv _ _).symm ψ, ?_⟩
  intro h
  apply hψ
  have h1 : adjQ.homEquiv _ _ ((adjQ.homEquiv _ _).symm ψ) = ψ := Equiv.apply_symm_apply _ _
  rw [← h1, h, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

end Generators

/-- Renard VI.10.5, existence of `z_M`, in derived form: for an actual rational parabolic
`P = MN` of a connected reductive `G`, every element `z` of the centre of the category of
smooth representations of `G(F)` and every smooth representation `σ` of `M(F)` (carriers in
the common universe `max u v`), the component of `z` at `i_P^G(σ)` is `i_P^G(y)` for an
endomorphism `y` of `σ`. -/
def LeviCenterComponentsLiftStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      let I := leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
      ∀ (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
        (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)),
        ∃ y : σ ⟶ σ, I.map y = z.app (I.obj σ)

/-- The statement that `LeviCenterComponentsLiftStatement` follows from the second
adjointness theorem (`LeviSecondAdjointnessStatement`, Renard VI.9.6) and the joint
special-compact basis (`JointSpecialCompactBasisExistenceStatement`, Renard V.5.1–V.5.2). -/
def LeviCenterComponentsLiftReductionStatement : Prop :=
  LeviSecondAdjointnessStatement.{u, v} →
    JointSpecialCompactBasisExistenceStatement.{u} →
      LeviCenterComponentsLiftStatement.{u, v}

/-- **Central components lift through `i_P^G`**, given second adjointness and the joint
special-compact basis. -/
theorem leviCenterComponentsLiftReductionStatement_holds :
    LeviCenterComponentsLiftReductionStatement.{u, v} := by
  intro hSA hJ k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro I z σ
  obtain ⟨Pbar, Nbar, pbar, mbar, nbar, -, hpbar, hmbar, hnbar, hmulbar, hcomp, hinf, -, -, -⟩ :=
    Langlands.Renard.AlgebraicFamily.InducedTwistsDetection.exists_opposite_parabolic hG hp hl
  obtain ⟨adj⟩ := hSA k G hG P Pbar M N Nbar p l r hp hl hr hmul pbar mbar nbar hpbar hmbar
    hnbar hmulbar hcomp hinf
  have := leviInductionFunctor_faithful.{u, max u v} p l r hp hr hl hmul
  refine Renard.exists_map_eq_center_app_of_detecting adj z σ ?_
  intro Y φ hφ
  let Qp : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) := fun X =>
    Projective X ∧ ∃ f : X ⟶ X, I.map f = z.app (I.obj X)
  have hdet : ∀ D : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), D.IsIrreducible →
      ∃ X, Qp X ∧ ∃ a : X ⟶ D, a ≠ 0 := by
    intro D hD
    obtain ⟨Q, L, V, q, n, s, hq, hn, hs, hmulQ, τ, hτ, hsc, ρ₀, hρ₀, j, hj, hproj, a, ha⟩ :=
      exists_projective_summandInduction_ne_zero.{u, v} hSA hJ hl.isConnectedReductive D hD
    obtain ⟨f, hf⟩ := exists_map_eq_center_app_leviInduction_summandInduction.{u, max u v}
      hG p l r hp hl hr hmul q n s hq hn hs hmulQ τ hτ hsc ρ₀ hρ₀ j hj z
    exact ⟨_, ⟨hproj, f, hf⟩, a, ha⟩
  obtain ⟨X, ⟨-, hX⟩, t, ht⟩ :=
    SmoothRep.exists_comp_ne_zero_of_projective_family Qp (fun X h => h.1) hdet φ hφ
  exact ⟨X, t, ht, hX⟩

end Langlands.Aubert.General.RepresentedParabolic
