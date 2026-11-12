import Langlands.Automorphic.CuspidalAdmissible.PolynomialRayleigh
import Langlands.Automorphic.OperatorRealizationCountable
import Langlands.Automorphic.OperatorSubquotientArchimedean
import Langlands.Global.ArchimedeanCasimirCartan

/-!
# A polynomial annihilating the Casimir operator on an irreducible realization

The trace-form Casimir element is fixed by every archimedean adjoint automorphism. On an
irreducible actual operator realization, the kernel of `q(Ω)` is stable under the finite,
compact and differential operators whenever `q(Ω)` kills one nonzero vector; center
finiteness supplies such a nonzero polynomial `q`. Hence one nonzero polynomial in the
Casimir operator vanishes on the whole realization.
-/

noncomputable section

universe uF

open Polynomial

namespace Langlands.Global.ArchimedeanGL

variable (K : Type uF) [Field K] [NumberField K] (n : ℕ)

/-- The real trace form is invariant under the archimedean adjoint action. -/
theorem matrixTraceForm_realLieConjugation (g : InfiniteAdelicGL K n)
    (X Y : RealLieAlgebra K n) :
    matrixTraceForm K n (realLieConjugation K n g X) (realLieConjugation K n g Y) =
      matrixTraceForm K n X Y := by
  simp only [matrixTraceForm_apply, realLieAlgebraToMatrix_realLieConjugation]
  congr 1
  set G := (archimedeanGLCoordinates K n g).val
  set Gi := (archimedeanGLCoordinates K n g⁻¹).val
  set A := realLieAlgebraToMatrix K n X
  set B := realLieAlgebraToMatrix K n Y
  have h1 : Gi * G = 1 := by
    simp only [Gi, G, map_inv]
    exact Units.inv_mul _
  have e : G * A * Gi * (G * B * Gi) = G * (A * B) * Gi := by
    calc G * A * Gi * (G * B * Gi) = G * A * (Gi * G) * B * Gi := by
          simp only [mul_assoc]
      _ = G * (A * B) * Gi := by rw [h1, mul_one]; simp only [mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, h1, one_mul]

omit [NumberField K] in
/-- The real enveloping generator intertwines the adjoint actions. -/
theorem realEnvelopingGenerator_realLieConjugation (g : InfiniteAdelicGL K n)
    (X : RealLieAlgebra K n) :
    realEnvelopingGenerator K n (realLieConjugation K n g X) =
      envelopingConjugation K n g (realEnvelopingGenerator K n X) := by
  rw [realEnvelopingGenerator_apply, realEnvelopingGenerator_apply,
    envelopingConjugation_generator, complexLieConjugation_tmul]

/-- The trace-form Casimir element is fixed by every adjoint automorphism. -/
theorem envelopingConjugation_matrixCasimir (g : InfiniteAdelicGL K n) :
    envelopingConjugation K n g (matrixCasimir K n) = matrixCasimir K n := by
  classical
  have : FiniteDimensional ℝ (RealLieAlgebra K n) :=
    FiniteDimensional.of_injective (realLieAlgebraToMatrix K n).toLinearMap
      (realLieAlgebraToMatrix K n).injective
  let b := Module.finBasis ℝ (RealLieAlgebra K n)
  let b' := b.map (realLieConjugation K n g).toLinearEquiv
  have hdual : (matrixTraceForm K n).dualBasis (matrixTraceForm_nondegenerate K n) b' =
      fun i => realLieConjugation K n g
        ((matrixTraceForm K n).dualBasis (matrixTraceForm_nondegenerate K n) b i) := by
    apply (LinearMap.BilinForm.dualBasis_eq_iff _ b' _).mpr
    intro i j
    change matrixTraceForm K n (realLieConjugation K n g
        ((matrixTraceForm K n).dualBasis (matrixTraceForm_nondegenerate K n) b i))
      (realLieConjugation K n g (b j)) = _
    rw [matrixTraceForm_realLieConjugation, LinearMap.BilinForm.apply_dualBasis_left]
  calc envelopingConjugation K n g (matrixCasimir K n)
      = ∑ i, realEnvelopingGenerator K n (b' i) *
          realEnvelopingGenerator K n (realLieConjugation K n g
            ((matrixTraceForm K n).dualBasis (matrixTraceForm_nondegenerate K n) b i)) := by
        rw [matrixCasimir_eq_sum K n b, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, ← realEnvelopingGenerator_realLieConjugation,
          ← realEnvelopingGenerator_realLieConjugation]
        rfl
    _ = matrixCasimir K n := by
        rw [matrixCasimir_eq_sum K n b', hdual]

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance casimirAnnRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance casimirAnnContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance casimirAnnSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance casimirAnnFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance casimirAnnStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance casimirAnnSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The Casimir operator of a realization. -/
abbrev casimirOperator : Module.End ℂ S.Space :=
  S.envelopingAction (ArchimedeanGL.matrixCasimir F n)

/-- Every realized vector is killed by a nonzero polynomial in the Casimir operator. -/
theorem exists_casimir_annihilator_vector (f : S.Space) :
    ∃ q : ℂ[X], q ≠ 0 ∧ aeval (casimirOperator S) q f = 0 := by
  have : Module.Finite ℂ (FiniteVectors.orbitSpan S.centerRepresentation f) :=
    S.centerRepresentation_isFiniteVector f
  have hW : ∀ w ∈ FiniteVectors.orbitSpan S.centerRepresentation f,
      casimirOperator S w ∈ FiniteVectors.orbitSpan S.centerRepresentation f := fun w hw =>
    (FiniteVectors.orbitSubrepresentation S.centerRepresentation f).apply_mem_toSubmodule
      (ArchimedeanGL.matrixCentralCasimir F n) hw
  exact exists_aeval_apply_eq_zero (casimirOperator S) _ hW
    (FiniteVectors.self_mem_orbitSpan _ f)

/-- The Casimir operator commutes with finite translations. -/
theorem finiteRepresentation_casimirOperator (d : FiniteAdelicGL F n) (f : S.Space) :
    S.finiteRepresentation d (casimirOperator S f) =
      casimirOperator S (S.finiteRepresentation d f) :=
  S.finiteRepresentation_envelopingAction d _ f

/-- The Casimir operator commutes with compact translations. -/
theorem compactRepresentation_casimirOperator (k : standardInfiniteCompact F n)
    (f : S.Space) :
    S.compactRepresentation k (casimirOperator S f) =
      casimirOperator S (S.compactRepresentation k f) :=
  (S.compactRepresentation_envelopingAction k _ f).trans
    (congrArg (fun a => S.envelopingAction a (S.compactRepresentation k f))
      (ArchimedeanGL.envelopingConjugation_matrixCasimir F n k.val))

/-- The Casimir operator commutes with the whole differential action. -/
theorem envelopingAction_casimirOperator (a : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : S.Space) :
    S.envelopingAction a (casimirOperator S f) =
      casimirOperator S (S.envelopingAction a f) := by
  have hc : a * ArchimedeanGL.matrixCasimir F n = ArchimedeanGL.matrixCasimir F n * a :=
    Subalgebra.mem_center_iff.mp (ArchimedeanGL.matrixCasimir_mem_center F n) a
  have h : S.envelopingAction a * casimirOperator S =
      casimirOperator S * S.envelopingAction a :=
    (map_mul S.envelopingAction a _).symm.trans
      ((congrArg S.envelopingAction hc).trans (map_mul S.envelopingAction _ a))
  exact LinearMap.congr_fun h f

set_option maxHeartbeats 2000000 in
/-- An irreducible realization has a nonzero vector. -/
theorem exists_ne_zero (hS : S.IsIrreducible) : ∃ x : S.Space, x ≠ 0 := by
  have hnt : Nontrivial (Subrepresentation S.representation) := hS.toNontrivial
  by_contra! h
  apply (bot_ne_top : (⊥ : Subrepresentation S.representation) ≠ ⊤)
  apply Subrepresentation.ext
  change (⊥ : Submodule ℂ S.Space) = ⊤
  rw [eq_comm, eq_bot_iff]
  intro x _
  exact (Submodule.mem_bot ℂ).mpr (h x)

set_option maxHeartbeats 1000000 in
/-- **Casimir annihilator.** On an irreducible realization, one nonzero polynomial in the
Casimir operator vanishes identically. -/
theorem exists_casimir_annihilator (hS : S.IsIrreducible) :
    ∃ q : ℂ[X], q ≠ 0 ∧ ∀ f : S.Space, aeval (casimirOperator S) q f = 0 := by
  obtain ⟨f₀, hf₀⟩ := exists_ne_zero S hS
  obtain ⟨q, hq, hqf⟩ := exists_casimir_annihilator_vector S f₀
  refine ⟨q, hq, ?_⟩
  let P : Submodule ℂ S.Space := LinearMap.ker (aeval (casimirOperator S) q)
  have hstable := S.representation_mem_of_stable P
    (fun d v hv => by
      change aeval (casimirOperator S) q (S.finiteRepresentation d v) = 0
      rw [← aeval_apply_commute (fun w => finiteRepresentation_casimirOperator S d w),
        show aeval (casimirOperator S) q v = 0 from hv, map_zero])
    (fun k v hv => by
      change aeval (casimirOperator S) q (S.compactRepresentation k v) = 0
      rw [← aeval_apply_commute (fun w => compactRepresentation_casimirOperator S k w),
        show aeval (casimirOperator S) q v = 0 from hv, map_zero])
    (fun a v hv => by
      change aeval (casimirOperator S) q (S.envelopingAction a v) = 0
      rw [← aeval_apply_commute (fun w => envelopingAction_casimirOperator S a w),
        show aeval (casimirOperator S) q v = 0 from hv, map_zero])
  let P' : Subrepresentation S.representation :=
    { toSubmodule := P
      apply_mem_toSubmodule := fun a _ hv => hstable a _ hv }
  have hP' : P' ≠ ⊥ := by
    intro h
    have hmem : f₀ ∈ P'.toSubmodule := hqf
    rw [h] at hmem
    exact hf₀ ((Submodule.mem_bot ℂ).mp hmem)
  have htop : P' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top P').resolve_left hP'
  intro f
  have hmem : f ∈ P'.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  exact hmem

end Langlands.Automorphic.CuspidalAdmissible
