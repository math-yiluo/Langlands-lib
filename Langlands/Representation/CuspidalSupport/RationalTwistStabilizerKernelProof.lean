import Langlands.Representation.CuspidalSupport.RationalTwistStabilizerKernelStatement
import Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteProof
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The group `T` of an irreducible representation (Renard VI.4.4, proof) -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

namespace TwistStabilizerKernel

section Duality

/-- `ℂ` has enough roots of unity for the exponent of a finite group. -/
theorem complex_hasEnoughRootsOfUnity_exponent (S : Type*) [Group S] [Finite S] :
    HasEnoughRootsOfUnity ℂ (Monoid.exponent S) := by
  have : NeZero ((Monoid.exponent S : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  infer_instance

/-- Double annihilator for a finite commutative group `S` of characters of a group `Γ`: a
character trivial on every element where all of `S` is trivial comes from `S`. -/
theorem exists_eq_of_forall_eq_one {Γ S : Type*} [Group Γ] [CommGroup S] [Finite S]
    (emb : S →* (Γ →* ℂˣ)) (ω : Γ →* ℂˣ)
    (hω : ∀ g : Γ, (∀ s : S, emb s g = 1) → ω g = 1) : ∃ s : S, emb s = ω := by
  have := complex_hasEnoughRootsOfUnity_exponent S
  have : Finite (S →* ℂˣ) :=
    Finite.of_equiv S
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity S ℂ).some.symm.toEquiv
  have := complex_hasEnoughRootsOfUnity_exponent (S →* ℂˣ)
  let ev : Γ →* (S →* ℂˣ) :=
    { toFun := fun g =>
        { toFun := fun s => emb s g
          map_one' := by simp
          map_mul' := fun s t => by simp }
      map_one' := by ext s; simp
      map_mul' := fun g h => by ext s; simp }
  have hker : ev.ker ≤ ω.ker := by
    intro g hg
    apply hω
    intro s
    have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) s
    exact h
  let ψ : ev.range →* ℂˣ :=
    (QuotientGroup.lift ev.ker ω hker).comp
      (QuotientGroup.quotientKerEquivRange ev).symm.toMonoidHom
  have hψ : ∀ g : Γ, ψ ⟨ev g, g, rfl⟩ = ω g := by
    intro g
    have h : (QuotientGroup.quotientKerEquivRange ev).symm ⟨ev g, g, rfl⟩ =
        (g : Γ ⧸ ev.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]
  obtain ⟨ψ', hψ'⟩ := MonoidHom.domRestrict_surjective (M := ℂ) ev.range ψ
  refine ⟨CommGroup.monoidHomMonoidHomEquiv S ℂ ψ', MonoidHom.ext fun g => ?_⟩
  have h1 : ev g (CommGroup.monoidHomMonoidHomEquiv S ℂ ψ') = ψ' (ev g) :=
    CommGroup.apply_monoidHomMonoidHomEquiv (G := S) (M := ℂ) (ev g) ψ'
  have h2 : ψ' (ev g) = ψ ⟨ev g, g, rfl⟩ := by
    rw [← hψ']
    rfl
  calc emb (CommGroup.monoidHomMonoidHomEquiv S ℂ ψ') g
      = ev g (CommGroup.monoidHomMonoidHomEquiv S ℂ ψ') := rfl
    _ = ω g := by rw [h1, h2, hψ]

end Duality

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] {I : Type*} (ν : I → (G →* ℝ≥0ˣ))

/-- Evaluation of the unramified characters at the classes of `G ⧸ ⁰G`. -/
def quotientEvaluation : G ⧸ commonNormKernel ν →* (unramifiedCharacters ν → ℂ) where
  toFun q := fun χ => ((unramifiedCharacterDescend ν χ q : ℂˣ) : ℂ)
  map_one' := by funext χ; simp
  map_mul' q r := by funext χ; simp

@[simp]
theorem quotientEvaluation_mk (g : G) :
    quotientEvaluation ν (QuotientGroup.mk g) = unramifiedEvaluation ν g := rfl

/-- The evaluation at a class of `G ⧸ ⁰G`, as a monoid homomorphism on the characters. -/
def quotientEvaluationHom (q : G ⧸ commonNormKernel ν) : unramifiedCharacters ν →* ℂ where
  toFun χ := ((unramifiedCharacterDescend ν χ q : ℂˣ) : ℂ)
  map_one' := by
    induction q using QuotientGroup.induction_on
    rfl
  map_mul' χ ψ2 := by
    induction q using QuotientGroup.induction_on
    rfl

/-- Unramified characters separate the points of `G ⧸ ⁰G` when `⁰G` is open: a norm character
that is not trivial at `g` is itself an unramified character. -/
theorem exists_unramifiedCharacter_apply_ne_one [IsTopologicalGroup G]
    (hN : IsOpen (commonNormKernel ν : Set G)) {g : G} (hg : g ∉ commonNormKernel ν) :
    ∃ χ : unramifiedCharacters ν, χ.val g ≠ 1 := by
  rw [mem_commonNormKernel] at hg
  push Not at hg
  obtain ⟨i, hi⟩ := hg
  let c : ℝ≥0 →* ℂ :=
    (Complex.ofRealHom.toMonoidHom).comp NNReal.toRealHom.toMonoidHom
  let f : G →* ℂˣ := (Units.map c).comp (ν i)
  have hf1 : ∀ x ∈ commonNormKernel ν, f x = 1 := by
    intro x hx
    simp [f, (mem_commonNormKernel ν x).mp hx i]
  have hcont : Continuous f := by
    apply continuous_of_continuousAt_one f
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [hN.mem_nhds (commonNormKernel ν).one_mem] with x hx
    rw [hf1 x hx]
  refine ⟨⟨⟨f, hcont⟩, fun x hx => hf1 x hx⟩, ?_⟩
  intro h
  apply hi
  change f g = 1 at h
  have h' : c ((ν i g : ℝ≥0ˣ) : ℝ≥0) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simpa only [f, MonoidHom.comp_apply, Units.coe_map, Units.val_one] using this
  have h'' : (((ν i g : ℝ≥0ˣ) : ℝ≥0) : ℝ) = (1 : ℝ) := by
    have h3 : ((((ν i g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_one]
      exact h'
    exact Complex.ofReal_injective h3
  exact Units.val_eq_one.mp (NNReal.coe_eq_one.mp h'')

theorem quotientEvaluationHom_injective [IsTopologicalGroup G]
    (hN : IsOpen (commonNormKernel ν : Set G)) :
    Function.Injective (quotientEvaluationHom ν) := by
  intro q r hqr
  induction q using QuotientGroup.induction_on with | H g => ?_
  induction r using QuotientGroup.induction_on with | H h => ?_
  by_contra hne
  have hgh : g⁻¹ * h ∉ commonNormKernel ν := by
    intro hmem
    exact hne (QuotientGroup.eq.mpr hmem)
  obtain ⟨χ, hχ⟩ := exists_unramifiedCharacter_apply_ne_one ν hN hgh
  apply hχ
  have h1 : (χ.val g : ℂ) = (χ.val h : ℂ) := by
    have h0 := DFunLike.congr_fun hqr χ
    exact h0
  have h2 : χ.val g = χ.val h := Units.ext h1
  rw [map_mul, map_inv, h2, inv_mul_cancel]

theorem linearIndependent_quotientEvaluation [IsTopologicalGroup G]
    (hN : IsOpen (commonNormKernel ν : Set G)) :
    LinearIndependent ℂ (quotientEvaluation ν) := by
  have h := (linearIndependent_monoidHom (unramifiedCharacters ν) ℂ).comp
    (quotientEvaluationHom ν) (quotientEvaluationHom_injective ν hN)
  have heq : (fun q => ((quotientEvaluationHom ν q : unramifiedCharacters ν →* ℂ) :
      unramifiedCharacters ν → ℂ)) = (quotientEvaluation ν : _ → _) := by
    funext q χ
    rfl
  rw [← heq]
  exact h

/-- The evaluation algebra map `ℂ[G/⁰G] → (X → ℂ)`. -/
def evaluationAlgHom :
    MonoidAlgebra ℂ (G ⧸ commonNormKernel ν) →ₐ[ℂ] (unramifiedCharacters ν → ℂ) :=
  MonoidAlgebra.lift ℂ (unramifiedCharacters ν → ℂ) (G ⧸ commonNormKernel ν)
    (quotientEvaluation ν)

theorem evaluationAlgHom_apply (x : MonoidAlgebra ℂ (G ⧸ commonNormKernel ν)) :
    evaluationAlgHom ν x = Finsupp.linearCombination ℂ (quotientEvaluation ν) x.coeff := by
  rw [evaluationAlgHom, MonoidAlgebra.lift_apply, Finsupp.linearCombination_apply]

theorem evaluationAlgHom_apply_apply (x : MonoidAlgebra ℂ (G ⧸ commonNormKernel ν))
    (χ : unramifiedCharacters ν) :
    evaluationAlgHom ν x χ =
      ∑ q ∈ x.coeff.support, x.coeff q * quotientEvaluation ν q χ := by
  rw [evaluationAlgHom_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply]
  rfl

@[simp]
theorem evaluationAlgHom_of (g : G) :
    evaluationAlgHom ν (MonoidAlgebra.of ℂ _ (QuotientGroup.mk g)) =
      unramifiedEvaluation ν g := by
  rw [evaluationAlgHom, MonoidAlgebra.lift_of, quotientEvaluation_mk]

theorem evaluationAlgHom_injective [IsTopologicalGroup G]
    (hN : IsOpen (commonNormKernel ν : Set G)) :
    Function.Injective (evaluationAlgHom ν) := by
  intro x y hxy
  rw [evaluationAlgHom_apply, evaluationAlgHom_apply] at hxy
  exact MonoidAlgebra.coeff_injective (linearIndependent_quotientEvaluation ν hN hxy)

/-- A translation-invariant image under the evaluation map has invariant coefficients. -/
theorem coeff_invariant [IsTopologicalGroup G]
    (hN : IsOpen (commonNormKernel ν : Set G))
    (x : MonoidAlgebra ℂ (G ⧸ commonNormKernel ν)) (s : unramifiedCharacters ν)
    (hs : ∀ χ, evaluationAlgHom ν x (χ * s) = evaluationAlgHom ν x χ) (g : G) :
    ((s.val g : ℂˣ) : ℂ) * x.coeff (QuotientGroup.mk g) = x.coeff (QuotientGroup.mk g) := by
  classical
  by_cases hg : QuotientGroup.mk g ∈ x.coeff.support
  · have hli := linearIndependent_iff'.mp (linearIndependent_quotientEvaluation ν hN)
    let d : G ⧸ commonNormKernel ν → ℂ := fun q => ((unramifiedCharacterDescend ν s q : ℂˣ) : ℂ)
    have hmul : ∀ (q : G ⧸ commonNormKernel ν) (χ : unramifiedCharacters ν),
        quotientEvaluation ν q (χ * s) = quotientEvaluation ν q χ * d q := by
      intro q χ
      induction q using QuotientGroup.induction_on
      rfl
    have hsum : ∑ q ∈ x.coeff.support,
        (d q * x.coeff q - x.coeff q) • quotientEvaluation ν q = 0 := by
      funext χ
      have h := hs χ
      rw [evaluationAlgHom_apply_apply, evaluationAlgHom_apply_apply] at h
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      simp only [hmul] at h
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h
      rw [← h]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have := hli _ _ hsum _ hg
    have h0 := sub_eq_zero.mp this
    exact h0
  · rw [Finsupp.notMem_support_iff.mp hg, mul_zero]

section Subgroup

variable (T : Subgroup G) (S : Set (unramifiedCharacters ν))

/-- A finitely supported function on `G ⧸ ⁰G` is `S`-invariant exactly when it is supported in
`T ⧸ ⁰G`, where `T` is the common kernel of `S`. -/
theorem invariant_iff_support (hT : ∀ g, g ∈ T ↔ ∀ s ∈ S, s.val g = 1)
    (f : G ⧸ commonNormKernel ν →₀ ℂ) :
    (∀ s ∈ S, ∀ g : G,
        ((s.val g : ℂˣ) : ℂ) * f (QuotientGroup.mk g) = f (QuotientGroup.mk g)) ↔
      ∀ g : G, f (QuotientGroup.mk g) ≠ 0 → g ∈ T := by
  constructor
  · intro h g hg
    rw [hT]
    intro s hs
    have h1 : ((s.val g : ℂˣ) : ℂ) = 1 :=
      mul_right_cancel₀ hg ((h s hs g).trans (one_mul _).symm)
    exact Units.val_eq_one.mp h1
  · intro h s hs g
    by_cases hg : f (QuotientGroup.mk g) = 0
    · rw [hg, mul_zero]
    · rw [(hT g).mp (h g hg) s hs, Units.val_one, one_mul]

/-- The inclusion `T ⧸ ⁰G → G ⧸ ⁰G`. -/
def quotientInclusion :
    T ⧸ (commonNormKernel ν).subgroupOf T →* G ⧸ commonNormKernel ν :=
  QuotientGroup.map _ _ T.subtype (fun _ h => h)

omit [TopologicalSpace G] in
theorem quotientInclusion_mk (t : T) :
    quotientInclusion ν T (QuotientGroup.mk t) = QuotientGroup.mk (t : G) := rfl

omit [TopologicalSpace G] in
theorem quotientInclusion_injective : Function.Injective (quotientInclusion ν T) := by
  intro q r h
  induction q using QuotientGroup.induction_on with | H t => ?_
  induction r using QuotientGroup.induction_on with | H u => ?_
  rw [quotientInclusion_mk, quotientInclusion_mk, QuotientGroup.eq] at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact h

/-- The algebra `ℂ[T ⧸ ⁰G]` maps injectively onto the `S`-invariant polynomial functions. -/
theorem exists_invariantAlgHom [IsTopologicalGroup G]
    (hN : IsOpen (commonNormKernel ν : Set G)) (hT : ∀ g, g ∈ T ↔ ∀ s ∈ S, s.val g = 1) :
    ∃ Θ : MonoidAlgebra ℂ (T ⧸ (commonNormKernel ν).subgroupOf T) →ₐ[ℂ]
        (unramifiedCharacters ν → ℂ),
      Function.Injective Θ ∧
      Set.range Θ =
        {φ | φ ∈ unramifiedRegularFunctions ν ∧ ∀ s ∈ S, ∀ χ, φ (χ * s) = φ χ} ∧
      ∀ t : T, Θ (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)) = unramifiedEvaluation ν (t : G) := by
  classical
  let Θ := (evaluationAlgHom ν).comp
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (quotientInclusion ν T))
  have hΘ : ∀ x, Θ x =
      evaluationAlgHom ν (MonoidAlgebra.mapDomain (quotientInclusion ν T) x) := fun x => rfl
  have hof : ∀ t : T, Θ (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)) =
      unramifiedEvaluation ν (t : G) := by
    intro t
    rw [hΘ, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single, ← MonoidAlgebra.of_apply,
      quotientInclusion_mk, evaluationAlgHom_of]
  refine ⟨Θ, ?_, ?_, hof⟩
  · intro x y hxy
    rw [hΘ, hΘ] at hxy
    exact MonoidAlgebra.mapDomain_injective (quotientInclusion_injective ν T)
      (evaluationAlgHom_injective ν hN hxy)
  · ext φ
    constructor
    · rintro ⟨x, rfl⟩
      induction x using MonoidAlgebra.induction_on with
      | of q =>
        induction q using QuotientGroup.induction_on with | H t => ?_
        rw [hof]
        refine ⟨Algebra.subset_adjoin ⟨(t : G), rfl⟩, fun s hs χ => ?_⟩
        change (((χ * s).val (t : G) : ℂˣ) : ℂ) = ((χ.val (t : G) : ℂˣ) : ℂ)
        rw [Subgroup.coe_mul, ContinuousMonoidHom.mul_apply, (hT t).mp t.property s hs, mul_one]
      | add x y hx hy =>
        rw [map_add]
        refine ⟨add_mem hx.1 hy.1, fun s hs χ => ?_⟩
        simp only [Pi.add_apply, hx.2 s hs χ, hy.2 s hs χ]
      | smul r x hx =>
        rw [map_smul]
        refine ⟨Subalgebra.smul_mem _ hx.1 r, fun s hs χ => ?_⟩
        simp only [Pi.smul_apply, hx.2 s hs χ]
    · rintro ⟨hreg, hinv⟩
      have hle : unramifiedRegularFunctions ν ≤ (evaluationAlgHom ν).range := by
        apply Algebra.adjoin_le
        rintro _ ⟨g, rfl⟩
        exact ⟨MonoidAlgebra.of ℂ _ (QuotientGroup.mk g), evaluationAlgHom_of ν g⟩
      obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).mp (hle hreg)
      have hsupp : (↑x.coeff.support : Set _) ⊆ Set.range (quotientInclusion ν T) := by
        intro q hq
        induction q using QuotientGroup.induction_on with | H g => ?_
        have hgT : g ∈ T :=
          (invariant_iff_support ν T S hT x.coeff).mp
            (fun s hs g' => coeff_invariant ν hN x s (hinv s hs) g') g
            (Finsupp.mem_support_iff.mp hq)
        exact ⟨QuotientGroup.mk ⟨g, hgT⟩, rfl⟩
      refine ⟨MonoidAlgebra.comapDomain (quotientInclusion ν T)
        (quotientInclusion_injective ν T) x, ?_⟩
      rw [hΘ, MonoidAlgebra.mapDomain_comapDomain hsupp]

end Subgroup

end Generic

section Rational

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instTwistStabilizerKernel1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance instTwistStabilizerKernel2 :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- The unramified twist stabilizer `X(G)(π) = {ω | π ⊗ ω ≅ π}`, as a subgroup of the
unramified characters. -/
def twistStabilizer (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Subgroup (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) where
  carrier := {ω | Nonempty (rationalUnramifiedTwist G ω A ≅ A)}
  one_mem' := ⟨rationalUnramifiedTwistOneIso G A⟩
  mul_mem' := by
    rintro χ ψ ⟨e⟩ ⟨f⟩
    exact ⟨(rationalUnramifiedTwistMulIso G χ ψ A).symm ≪≫
      SmoothRep.twistIso χ.val.toMonoidHom (isOpen_rationalUnramifiedCharacter_ker G χ) f ≪≫ e⟩
  inv_mem' := by
    rintro χ ⟨e⟩
    exact ⟨SmoothRep.twistIso (χ⁻¹).val.toMonoidHom
        (isOpen_rationalUnramifiedCharacter_ker G χ⁻¹) e.symm ≪≫
      rationalUnramifiedTwistMulIso G χ⁻¹ χ A ≪≫
      eqToIso (congrArg (fun ω => rationalUnramifiedTwist G ω A) (inv_mul_cancel χ)) ≪≫
      rationalUnramifiedTwistOneIso G A⟩

end Rational

end TwistStabilizerKernel

open TwistStabilizerKernel in
/-- Renard VI.4.4, the paragraph defining `T` and the Remark after it. -/
theorem rationalTwistStabilizerKernel :
    RationalTwistStabilizerKernelStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro A hA X T
  let ν := fun chi => (rationalNormCharacters G chi).toMul
  let stab := twistStabilizer G A
  have hT : ∀ g, g ∈ T ↔ ∀ s ∈ (stab : Set X), s.val g = 1 := by
    intro g
    simp only [T, Subgroup.mem_iInf, MonoidHom.mem_ker]
    exact Iff.rfl
  -- `⁰G ≤ T`
  have h1 : rationalCommonNormKernel G ≤ T := by
    intro g hg
    rw [hT]
    intro s _
    have hs : commonNormKernel ν ≤ s.val.toMonoidHom.ker := s.property
    exact hs hg
  -- the centre lies in `T`, by Schur's lemma
  have h2 : Subgroup.center (GroupScheme.rationalPoints G) ≤ T := by
    intro z hz
    rw [hT]
    intro χ hχ
    have hχ' : Nonempty (rationalUnramifiedTwist G χ A ≅ A) := hχ
    obtain ⟨iso⟩ := hχ'
    let e : A.representation.Equiv (twist χ.val.toMonoidHom A.representation) :=
      SmoothRep.equivOfIso iso.symm
    let Tm : A.representation.IntertwiningMap A.representation :=
      { toLinearMap := A.representation z
        isIntertwining' := fun g => by
          change A.representation z * A.representation g =
            A.representation g * A.representation z
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g] }
    obtain ⟨c, hc, -⟩ := Schur.rationalPoint_scalarEndomorphism F G hG A hA Tm
    have act (x : A) : A.representation z x = c • x :=
      congrArg (fun f : A.representation.IntertwiningMap A.representation => f x) hc
    have := hA
    have : Nontrivial A :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
        A.representation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    have hc0 : c ≠ 0 := by
      intro h
      have hact := act (A.representation z⁻¹ v)
      rw [h, zero_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at hact
      exact hv hact
    have hev : e v ≠ 0 := by
      intro h
      apply hv
      apply e.toLinearEquiv.injective
      change e.toLinearEquiv v = 0 at h
      simpa only [map_zero] using h
    have he := Representation.IntertwiningMap.isIntertwining
      A.representation (twist χ.val.toMonoidHom A.representation)
      e.toIntertwiningMap z v
    change e (A.representation z v) =
      (χ.val z : ℂ) • A.representation z (e v) at he
    rw [act, map_smul, act, smul_smul] at he
    have hscalar : c = (χ.val z : ℂ) * c := smul_left_injective ℂ hev he
    apply Units.ext
    exact mul_right_cancel₀ hc0 (by simpa using hscalar.symm)
  -- `T` has finite index
  have h3 : T.FiniteIndex := by
    have : (rationalCommonNormKernel G ⊔
        Subgroup.center (GroupScheme.rationalPoints G)).FiniteIndex :=
      rationalCommonNormKernel_sup_center_finiteIndex F G hG
    exact Subgroup.finiteIndex_of_le (sup_le h1 h2)
  -- the stabilizer is the annihilator of `T`
  have hfin : Finite stab := by
    have := (rationalTwistStabilizerFinite.{uF, uV} F G hG A hA).to_subtype
    exact this
  have h4 : ∀ ω : X, Nonempty (rationalUnramifiedTwist G ω A ≅ A) ↔
      T ≤ ω.val.toMonoidHom.ker := by
    intro ω
    constructor
    · intro hω
      exact iInf₂_le ω hω
    · intro hle
      let emb : stab →* (GroupScheme.rationalPoints G →* ℂˣ) :=
        { toFun := fun s => s.val.val.toMonoidHom
          map_one' := MonoidHom.ext fun _ => rfl
          map_mul' := fun s t => MonoidHom.ext fun g =>
            ContinuousMonoidHom.mul_apply s.val.val t.val.val g }
      obtain ⟨s, hs⟩ := exists_eq_of_forall_eq_one emb ω.val.toMonoidHom (by
        intro g hg
        rw [← MonoidHom.mem_ker]
        apply hle
        rw [hT]
        intro s hs
        exact hg ⟨s, hs⟩)
      have hs' : s.val.val.toMonoidHom = ω.val.toMonoidHom := hs
      have hsω : s.val = ω := Subtype.ext (ContinuousMonoidHom.toMonoidHom_injective hs')
      rw [← hsω]
      exact s.property
  exact ⟨h1, h2, h3, h4, fun f => invariant_iff_support ν T _ hT f,
    exists_invariantAlgHom ν T _ (isOpen_rationalCommonNormKernel G) hT⟩

end Langlands.CuspidalSupport
