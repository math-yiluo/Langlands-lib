import Langlands.Representation.Exponents.UnitaryTwistJacquetNorms
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof

/-! # Finite exponent norms for the full unitary induced Jacquet family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U Q L V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryInducedNormAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : V ⟶ Q) (hq : IsParabolicSubgroup q)
  (hlQ : IsRationalLeviSubgroup lQ) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ L}

/-- Norms at an actual component point of every exponent of `r_Q i_P(σψ)`,
for every unitary unramified source twist `ψ`. -/
def unitaryInducedJacquetExponentNormSet
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (t : rationalPoints A.toGrp) : Set ℝ≥0 :=
  letI := leviPointTopology l hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  {z | ∃ (ψ : Plancherel.unramifiedCharacters
      (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
    (∀ m, ‖(ψ.val m : ℂ)‖ = 1) ∧ ∃ χ : rationalPoints A.toGrp →* ℂˣ,
      IsGeneralizedEigencharacter
        (((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj
          (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).ρ.comp
            (rationalPoints.map a)) χ ∧ ‖(χ t : ℂ)‖₊ = z}

/-- The full actual normalized induced Jacquet family has only finitely many
exponent norms at each fixed target split-component point, over the entire unitary
unramified parameter space. -/
theorem unitaryInducedJacquetExponentNormSet_finite (hG : IsConnectedReductive G)
    (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : letI := leviPointTopology l hl; σ.IsAdmissible)
    (hfinite : letI := leviPointTopology l hl; σ.HasFiniteLength)
    (t : rationalPoints A.toGrp) :
    (unitaryInducedJacquetExponentNormSet p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
      (a := a) σ t).Finite := by
  classical
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨n, _, z, _, D, hD⟩ := representedGeometricLemma k G hG P M U Q L V
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hpieces (i : Fin n) : ∃ R : Set ℝ≥0, R.Finite ∧
      ∀ (ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
        (∀ m, ‖(ψ.val m : ℂ)‖ = 1) → ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            (((D i).pieceFunctor.obj (σ.twist ψ.val.toMonoidHom
              (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).ρ.comp
                (rationalPoints.map a)) χ → ‖(χ t : ℂ)‖₊ ∈ R := by
    obtain ⟨A', a', f, ha', hf⟩ := (D i).exists_isSplitComponent_factor ha
    exact GeometricLemmaIntersectionDatum.exists_finite_unitaryTwistedPiece_exponentNorms
      p l r hp hl hr hmul (D i) ha ha' (Additive.ofMul f) hf t σ hσ hfinite
  choose R hR hmem using hpieces
  apply (Set.finite_iUnion hR).subset
  rintro s ⟨ψ, hψ, χ, hχ, rfl⟩
  obtain ⟨i, hi⟩ := hD.exists_isGeneralizedEigencharacter
    (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))
      (rationalPoints.map a) χ hχ
  exact Set.mem_iUnion.mpr ⟨i, hmem i ψ hψ χ hi⟩

/-- Uniform separation from one of all strictly contracting exponent norms of
the full actual unitary induced Jacquet family. No generic locus is selected. -/
theorem exists_unitaryInducedJacquet_contracting_norm_bound (hG : IsConnectedReductive G)
    (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : letI := leviPointTopology l hl; σ.IsAdmissible)
    (hfinite : letI := leviPointTopology l hl; σ.HasFiniteLength)
    (t : rationalPoints A.toGrp) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∃ θ : ℝ≥0, θ < 1 ∧
      ∀ (ψ : Plancherel.unramifiedCharacters
        (fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul)),
        (∀ m, ‖(ψ.val m : ℂ)‖ = 1) → ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            (((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj
              (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).ρ.comp
                (rationalPoints.map a)) χ →
            ‖(χ t : ℂ)‖₊ < 1 → ‖(χ t : ℂ)‖₊ ≤ θ := by
  classical
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let R := unitaryInducedJacquetExponentNormSet p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
    (a := a) σ t
  have hR : R.Finite := unitaryInducedJacquetExponentNormSet_finite
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hG ha σ hσ hfinite t
  let S : Finset ℝ≥0 := (hR.subset (Set.inter_subset_left : R ∩ Set.Iio 1 ⊆ R)).toFinset
  refine ⟨S.sup id, (Finset.sup_lt_iff (by norm_num)).mpr ?_, ?_⟩
  · intro s hs
    exact ((Set.Finite.mem_toFinset _).mp hs).2
  · intro ψ hψ χ hχ hχnorm
    apply Finset.le_sup (f := id)
    exact (Set.Finite.mem_toFinset _).mpr ⟨⟨ψ, hψ, χ, hχ, rfl⟩, hχnorm⟩

end Langlands.Aubert.General.RepresentedParabolic
