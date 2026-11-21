import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Automorphic.GroupSchemeUniformGrowthJointEvaluation
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicEisensteinJointRootHyperplaneStatement
import Langlands.Global.AdelicPositiveChamberStatement

/-! # Reduction of the joint root-hyperplane form of Eisenstein series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set Metric Filter Topology
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Scalar meromorphic uniqueness on the entire coordinate space, from agreement on the
intersection of the two domains of holomorphy with one nonempty open set. -/
private theorem eqOn_of_isMeromorphicOn_of_eqOn_open {n : ℕ}
    {f₁ f₂ : (Fin n → ℂ) → ℂ} {D₁ D₂ O : Set (Fin n → ℂ)}
    (h₁ : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f₁ D₁)
    (h₂ : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f₂ D₂)
    (hO : IsOpen O) (hne : O.Nonempty) (heq : EqOn f₁ f₂ (O ∩ (D₁ ∩ D₂))) :
    EqOn f₁ f₂ (D₁ ∩ D₂) := by
  have hloc {f : (Fin n → ℂ) → ℂ} {D : Set (Fin n → ℂ)}
      (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D) : HasLocalDenominators f D univ := by
    intro s _
    obtain ⟨U, hU, hUc, hsU, q, a, hq, hqne, ha, hqa⟩ := hf.2.2.2 s
    exact ⟨U, hU, hUc.isPreconnected, hsU, q, a, mdifferentiableOn_iff_differentiableOn.mp hq,
      hqne, differentiableOn_of_isHolomorphicOn ha, fun t ht => by
        simpa only [smul_eq_mul] using hqa t ht⟩
  obtain ⟨s, hs⟩ := hne
  intro t ht
  exact eq_of_hasLocalDenominators (Ω := univ) isOpen_univ isPreconnected_univ
    h₁.1 h₂.1 (h₁.2.1.closure_eq ▸ subset_rfl) (h₂.2.1.closure_eq ▸ subset_rfl)
    (differentiableOn_of_isHolomorphicOn h₁.2.2.1).continuousOn
    (differentiableOn_of_isHolomorphicOn h₂.2.2.1).continuousOn
    (hloc h₁) (hloc h₂) (mem_univ s)
    (eventually_of_mem (hO.mem_nhds hs) fun t htO ht₁ ht₂ => heq ⟨htO, ht₁, ht₂⟩)
    t (mem_univ t) ht.1 ht.2

section Regularity

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- Scale one positive parameter past any given threshold, using the finitely many root
inequalities. The finite set of ratios can be empty. -/
private theorem exists_regular_of_positive (hG : IsConnectedReductive G)
    {lam₀ : ComplexCharacterParameter F P} (h₀ : r.IsRegularParameter hA hT 0 lam₀) (R : ℝ) :
    ∃ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam := by
  have : Smooth G.X.hom := hG.smooth
  have hfin : r.unipotentRoots.Finite :=
    ((hT.finite_positiveRelativeRoots r.data.i r.data.ν).image fun χ => r.data.f ≫ χ).subset
      fun _ h => h.2
  let L (β : characterLattice A) := (r.realRootFunctional hA hT β).comp (parameterRealPart F P)
  let q (β : characterLattice A) := R / L β lam₀
  obtain ⟨C, hC⟩ := (hfin.image q).bddAbove
  refine ⟨(C + 1) • lam₀, fun β hβ => ?_⟩
  have hpos : 0 < L β lam₀ := h₀ β hβ
  have hle : q β ≤ C := hC ⟨β, hβ, rfl⟩
  have hlt : q β < C + 1 := hle.trans_lt (lt_add_of_pos_right _ zero_lt_one)
  change R < L β ((C + 1) • lam₀)
  rw [map_smul, smul_eq_mul]
  exact (div_lt_iff₀ hpos).mp hlt

end Regularity

section RankZero

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- The rank-zero adelic matrix embedding has only one point. -/
private theorem subsingleton_adelicPoints_of_rank_zero
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    Subsingleton (AdelicGroupPoints F G) :=
  ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
    (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- For a trivial adelic point group the series is a single term, entire in the parameter. -/
private theorem differentiable_series_of_trivial_points [Subsingleton (AdelicGroupPoints F G)]
    (φ : AdelicGroupPoints F G → ℂ) {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) : Differentiable ℂ (fun s => hK.eisensteinSeries φ (e s) g) := by
  let c₀ : ParabolicRationalCosets F p := Quotient.mk _ 1
  have hsub (c c' : ParabolicRationalCosets F p) : c = c' :=
    Quotient.inductionOn₂ c c' fun x y => congrArg _ (Subtype.ext (Subsingleton.elim _ _))
  have hsum : (fun s => hK.eisensteinSeries φ (e s) g) =
      fun s => hK.eisensteinTerm φ (e s) g c₀ := by
    funext s
    exact tsum_eq_single c₀ fun c hc => absurd (hsub c c₀) hc
  let x := (((Quotient.out c₀ : rationalSubgroup F G) : AdelicGroupPoints F G) * g)
  let L : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => complexParameterPairing F P (e s) (hK.height x)
      map_add' := fun s t => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun z s => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] }
  rw [hsum]
  change Differentiable ℂ (fun s => φ x * Complex.exp (L.toContinuousLinearMap s))
  exact (differentiable_const _).mul L.toContinuousLinearMap.differentiable.cexp

end RankZero

section Local

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho) (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))
  {n : ℕ}

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "Gad" => AdelicGroupPoints F G
local notation "E" => (Fin n → ℂ)
local notation "ev" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L

/-- Turn local meromorphic uniform-growth data into joint continuity of a pole-cleared
scalar family, whenever it agrees on the common dense set with scalar multiples of the
local regular values. Left invariance on that set extends to the smaller neighbourhood. -/
private theorem exists_joint_region_of_local_meromorphy
    {W : TopologicalSpace.Opens E} {f : W → 𝔉} {D : Set W}
    (hf : IsMeromorphicOn 𝓘(ℂ, E) f D) {s₀ : E} (hs₀ : s₀ ∈ W)
    {O D₀ : Set E} (hO : IsOpen O) (hsO : s₀ ∈ O) (hdD₀ : Dense D₀)
    {p : E → ℂ} {h : E → Gad → ℂ} (hp : ContinuousOn p O)
    (hh : ∀ g, DifferentiableOn ℂ (fun s => h s g) O)
    (heq : ∀ t ∈ D, (t : E) ∈ O → (t : E) ∈ D₀ → ∀ g, h t g = p t * ev (f t) g)
    (hinv : ∀ t ∈ D, IsLeftInvariantUnder F G (rationalSubgroup F G) (ev (f t))) :
    ∃ T : Set E, IsOpen T ∧ s₀ ∈ T ∧ T ⊆ O ∧
      ContinuousOn (fun p : E × Gad => h p.1 p.2) (T ×ˢ univ) ∧
      ∀ s ∈ T, ∀ c ∈ rationalSubgroup F G, ∀ g, h s (c * g) = h s g := by
  classical
  obtain ⟨U', hU', hU'c, hsU', q, a, hq, hqne, ha, hqa⟩ := hf.2.2.2 ⟨s₀, hs₀⟩
  let U : Set E := Subtype.val '' U'
  let V : Set E := Subtype.val '' D
  have hU : IsOpen U := W.isOpen.isOpenMap_subtype_val _ hU'
  have hUc : IsPreconnected U := hU'c.isPreconnected.image _ continuous_subtype_val.continuousOn
  have hsU : s₀ ∈ U := ⟨⟨s₀, hs₀⟩, hsU', rfl⟩
  have hV : IsOpen V := W.isOpen.isOpenMap_subtype_val _ hf.1
  have hWV : (W : Set E) ⊆ closure V := fun t ht =>
    image_closure_subset_closure_image continuous_subtype_val ⟨⟨t, ht⟩, hf.2.1 _, rfl⟩
  obtain ⟨r, hr, hrOU⟩ := Metric.isOpen_iff.mp (hO.inter hU) s₀ ⟨hsO, hsU⟩
  let T := ball s₀ r
  have hTo : IsOpen T := isOpen_ball
  have hsT : s₀ ∈ T := mem_ball_self hr
  have hTO : T ⊆ O := fun _ hs => (hrOU hs).1
  have hTU : T ⊆ U := fun _ hs => (hrOU hs).2
  let q₀ : E → ℂ := extendOpens q
  let a₀ : E → 𝔉 := extendOpens a
  have hq₀ : DifferentiableOn ℂ q₀ U := differentiableOn_extendOpens hU' hq
  have hq₀ne : ∃ s ∈ U, q₀ s ≠ 0 := by
    obtain ⟨t, ht, htq⟩ := hqne
    exact ⟨t, ⟨t, ht, rfl⟩, by simpa only [q₀, extendOpens_coe] using htq⟩
  have ha₀ (ell : 𝔉 →L[ℂ] ℂ) : DifferentiableOn ℂ (fun s => ell (a₀ s)) U := by
    refine (differentiableOn_extendOpens hU' (ha ell)).congr ?_
    rintro _ ⟨t, ht, rfl⟩
    simp only [a₀, extendOpens_coe]
  have hevd (g : Gad) : DifferentiableOn ℂ (fun s => ev (a₀ s) g) U := by
    refine (ha₀ (UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho R L g)).congr ?_
    exact fun s _ => (UniformGrowthFrechetSpace.evalCLM_apply F G rho hsmooth hcalc hN hrho R L
      g (a₀ s)).symm
  let X := T ∩ V ∩ D₀
  have hTX : T ⊆ closure X := by
    have hTV : T ⊆ closure (T ∩ V) := by
      intro s hs
      exact hTo.inter_closure ⟨hs, hWV (by obtain ⟨t, _, rfl⟩ := hTU hs; exact t.property)⟩
    exact hTV.trans (closure_minimal (hdD₀.open_subset_closure_inter (hTo.inter hV)) isClosed_closure)
  have hprod (g : Gad) : EqOn (fun s => q₀ s * h s g) (fun s => p s * ev (a₀ s) g) T := by
    refine EqOn.of_subset_closure (s := X) ?_
      ((hq₀.mono hTU).continuousOn.mul ((hh g).mono hTO).continuousOn)
      ((hp.mono hTO).mul ((hevd g).mono hTU).continuousOn) (fun _ hx => hx.1.1) hTX
    rintro _ ⟨⟨htT, t, htD, rfl⟩, htD₀⟩
    obtain ⟨t', ht'U, ht't⟩ := hTU htT
    have htU : t ∈ U' := Subtype.val_injective ht't ▸ ht'U
    have hscale := congrArg (UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho R L g)
      (hqa t ⟨htD, htU⟩)
    simp only [map_smul, smul_eq_mul, UniformGrowthFrechetSpace.evalCLM_apply] at hscale
    simp only [q₀, a₀, extendOpens_coe, heq t htD (hTO htT) htD₀]
    rw [← hscale, mul_left_comm]
  refine ⟨T, hTo, hsT, hTO,
    UniformGrowthFrechetSpace.continuousOn_of_mul_eq_eval F G rho hsmooth hcalc hN hrho R L
      hTo (convex_ball s₀ r).isPreconnected (hq₀.mono hTU)
      (exists_ne_zero_of_differentiableOn hU hUc hq₀ hq₀ne hTo hTU ⟨s₀, hsT⟩) (hp.mono hTO)
      (fun ell => (ha₀ ell).mono hTU) (fun g => (hh g).mono hTO) (fun s hs g => hprod g hs), ?_⟩
  intro s hs c hc g
  refine EqOn.of_subset_closure (s := X) (f := fun t => h t (c * g)) (g := fun t => h t g) ?_
    ((hh (c * g)).mono hTO).continuousOn ((hh g).mono hTO).continuousOn (fun _ hx => hx.1.1) hTX hs
  rintro _ ⟨⟨htT, t, htD, rfl⟩, htD₀⟩
  change h (t : E) (c * g) = h (t : E) g
  rw [heq t htD (hTO htT) htD₀, heq t htD (hTO htT) htD₀, hinv t htD c hc g]

end Local

/-- The joint root-hyperplane form follows from a nonempty positive chamber, the
uniform-growth-valued meromorphic continuation, and the scalar root-hyperplane form. -/
def EisensteinJointRootHyperplaneReductionStatement : Prop :=
  PositiveChamberNonemptyStatement.{u} → EisensteinMeromorphicContinuationStatement.{u} →
    EisensteinRootHyperplaneStatement.{u} → EisensteinJointRootHyperplaneStatement.{u}

/-- Match the two continuations on common domains by scalar meromorphic uniqueness,
then pass joint continuity of a cleared uniform-growth numerator to the holomorphic
root-cleared family. -/
theorem eisensteinJointRootHyperplaneReduction : EisensteinJointRootHyperplaneReductionStatement.{u} := by
  classical
  intro hCh hMero hRoot F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hiU K hK N d rho
    hsmooth hcalc φ hKmax hrho hφ EP DP hEP hRP n e s₀
  let Gad := AdelicGroupPoints F G
  obtain ⟨lam₀, h₀⟩ := hCh F G P M A p l a r hA hT hG
  obtain ⟨RP, hRP⟩ := hRP
  have hmatch (E' : ComplexCharacterParameter F P → Gad → ℂ) (D' : Set (Fin n → ℂ))
      (hE' : ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => E' (e s) g) D')
      (hreg : ∃ R₀ : ℝ, ∀ lam, r.IsRegularParameter hA hT R₀ lam →
        E' lam = hK.eisensteinSeries φ lam) :
      ∀ s ∈ D' ∩ e ⁻¹' DP, E' (e s) = EP (e s) := by
    obtain ⟨R₀, hR₀⟩ := hreg
    let O : Set (Fin n → ℂ) := {s | r.IsRegularParameter hA hT (max RP R₀) (e s)}
    have hO : IsOpen O := isOpen_setOf_isRegularParameter r hA hT hG _ e
    have hOne : O.Nonempty := by
      obtain ⟨lam, hlam⟩ := exists_regular_of_positive r hA hT hG h₀ (max RP R₀)
      refine ⟨e.symm lam, ?_⟩
      show r.IsRegularParameter hA hT _ (e (e.symm lam))
      rwa [LinearEquiv.apply_symm_apply]
    intro s hs
    funext g
    refine eqOn_of_isMeromorphicOn_of_eqOn_open (hE' g) ((hEP g).2 n e) hO hOne ?_ hs
    rintro t ⟨htO, -⟩
    change E' (e t) g = EP (e t) g
    rw [hR₀ _ (fun β hβ => (le_max_right RP R₀).trans_lt (htO β hβ)),
      hRP _ (fun β hβ => (le_max_left RP R₀).trans_lt (htO β hβ))]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := subsingleton_adelicPoints_of_rank_zero rho hrho
    have : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hEP 1).1
    have hm (g : Gad) :
        IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => hK.eisensteinSeries φ (e s) g) univ := by
      have hmer : IsMeromorphicInCoordinatesOn (fun lam => hK.eisensteinSeries φ lam g) univ :=
        isMeromorphicInCoordinatesOn_univ (fun _ e' => differentiable_series_of_trivial_points hK φ e' g)
      have hm' := hmer.2 n e
      rw [preimage_univ] at hm'
      exact hm'
    have hE := hmatch (hK.eisensteinSeries φ) univ hm ⟨RP, fun _ _ => rfl⟩
    have hd := differentiable_series_of_trivial_points hK φ e (1 : Gad)
    refine ⟨∅, 0, univ, (fun s _ => hK.eisensteinSeries φ (e s) 1), by simp, by simp,
      isOpen_univ, mem_univ _, (hd.continuous.comp continuous_fst).continuousOn,
      (fun _ => hd.differentiableOn), (fun _ _ _ _ _ => rfl), ?_⟩
    intro g s _ hsDP
    simpa only [pow_zero, one_mul, Subsingleton.elim g (1 : Gad)] using
      congrFun (hE s ⟨mem_univ _, hsDP⟩) (1 : Gad)
  obtain ⟨E', hR₀, hloc⟩ :=
    hMero F G P M U A p iU l a r hA hT hG hiU K hK rho hN hrho hsmooth hcalc φ hKmax hφ
  have hdata (t₀ : Fin n → ℂ) : HasLocalMeromorphicData (fun (g : Gad) s => E' (e s) g) t₀ := by
    obtain ⟨W, ht₀, R, L, -, f, D, hf, hfD⟩ := hloc n e t₀
    refine hasLocalMeromorphicData_of_isMeromorphicOn hf
      (UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho R L) (fun t ht g => ?_) ht₀
    rw [UniformGrowthFrechetSpace.evalCLM_apply, (hfD t ht).1]
  obtain ⟨D₀, hD₀⟩ := exists_isMeromorphicOn_of_local hdata
  have heqE := hmatch E' D₀ hD₀ hR₀
  have hDPd := ((hEP 1).2 n e).2.1
  have hCommonD := (hD₀ 1).2.1.inter_of_isOpen_left hDPd (hD₀ 1).1
  obtain ⟨S, m, O, hS, hO, hsO, hroot⟩ :=
    hRoot F G P M U A p iU l a r hA hT hG hiU K hK rho hsmooth hcalc φ hKmax hrho hφ EP DP hEP
      ⟨RP, hRP⟩ n e s₀
  choose h hh hEPeq using hroot
  let H : (Fin n → ℂ) → Gad → ℂ := fun s g => h g s
  let Q : (Fin n → ℂ) → ℂ := fun s => (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m
  have hQ : Differentiable ℂ Q := by
    have hfac (β : characterLattice A) :
        Differentiable ℂ (fun s : Fin n → ℂ => r.rootFunctional hA hT β (e s - e s₀)) := by
      let Lβ := (r.rootFunctional hA hT β).comp e.toLinearMap
      simp only [map_sub]
      exact (show Differentiable ℂ (fun s : Fin n → ℂ => Lβ s - Lβ s₀) from
        Lβ.toContinuousLinearMap.differentiable.sub (differentiable_const (Lβ s₀)))
    have hprod (B : Finset (characterLattice A)) :
        Differentiable ℂ (fun s : Fin n → ℂ => ∏ β ∈ B, r.rootFunctional hA hT β (e s - e s₀)) := by
      induction B using Finset.induction_on with
      | empty => simp only [Finset.prod_empty]; exact differentiable_const _
      | @insert β B hβ hB =>
        simp only [Finset.prod_insert hβ]
        exact (hfac β).mul hB
    exact (hprod S).pow m
  obtain ⟨W, hsW, R, L, -, f, D, hf, hfD⟩ := hloc n e s₀
  have hreg_eq (t : W) (ht : t ∈ D) (htO : (t : Fin n → ℂ) ∈ O)
      (htCom : (t : Fin n → ℂ) ∈ D₀ ∩ e ⁻¹' DP) (g : Gad) :
      H t g = Q t * UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) g := by
    change h g t = _
    rw [hEPeq g t htO htCom.2, (hfD t ht).1, heqE t htCom]
  have hreg_inv (t : W) (ht : t ∈ D) : IsLeftInvariantUnder F G (rationalSubgroup F G)
      (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t)) := by
    rw [(hfD t ht).1]
    exact (hfD t ht).2.1
  obtain ⟨T, hTopen, hsT, hTO, hH, hHinv⟩ :=
    exists_joint_region_of_local_meromorphy rho hsmooth hcalc hN hrho R L hf hsW hO hsO hCommonD
      (h := H) hQ.continuous.continuousOn hh hreg_eq hreg_inv
  refine ⟨S, m, T, H, hS, ?_, hTopen, hsT, hH, (fun g => (hh g).mono hTO), hHinv,
    (fun g s hs hd => hEPeq g s (hTO hs) hd)⟩
  intro β hβ hz
  have hpos : 0 < r.realRootFunctional hA hT β (parameterRealPart F P lam₀) := h₀ β (hS hβ)
  simp [hz] at hpos

end Langlands.Global
