import Langlands.Global.GlobalCompletionWeakApproximation
import Langlands.Global.AdelicGL
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof

/-! # Weak approximation for rational invertible matrices -/

noncomputable section

open NumberField Topology

namespace Langlands.Global

/-- A dense diagonal into finitely many topological fields gives a dense
diagonal of general linear groups. -/
theorem denseRange_generalLinear_of_denseDiagonal {K : Type*} [Field K] {ι : Type*}
    [Finite ι] (A : ι → Type*) [∀ i, Field (A i)] [∀ i, Algebra K (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalDivisionRing (A i)]
    [∀ i, T1Space (A i)]
    (h : DenseRange (fun x : K => fun i => algebraMap K (A i) x)) (n : ℕ) :
    DenseRange (fun g : Langlands.GeneralLinear n K =>
      fun i => Matrix.GeneralLinearGroup.map (algebraMap K (A i)) g) := by
  classical
  by_cases hi : Nonempty ι
  · let swap : Matrix (Fin n) (Fin n) (∀ i, A i) → ∀ i, Matrix (Fin n) (Fin n) (A i) :=
      fun M i j k => M j k i
    have hs : Function.Surjective swap := fun M => ⟨fun j k i => M i j k, rfl⟩
    have hsc : Continuous swap := continuous_pi fun i =>
      continuous_matrix fun j k =>
        (continuous_apply i).comp (continuous_id.matrix_elem j k)
    have hM : DenseRange (fun M : Matrix (Fin n) (Fin n) K =>
        fun i => M.map (algebraMap K (A i))) :=
      hs.denseRange.comp (DenseRange.piMap fun _ : Fin n =>
        DenseRange.piMap fun _ : Fin n => h) hsc
    let V : (∀ i, Langlands.GeneralLinear n (A i)) → ∀ i, Matrix (Fin n) (Fin n) (A i) :=
      fun g i => (g i).val
    have hV : IsOpenEmbedding V :=
      IsOpenEmbedding.piMap (fun i => RankinSelberg.isOpenEmbedding_generalLinear_val
        (K := A i) n)
    intro g
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨M, g', hg'U, hMg⟩ := hM.mem_nhds (hV.isOpenMap.image_mem_nhds hU)
    have hval (i : ι) : (g' i).val = M.map (algebraMap K (A i)) := congrFun hMg i
    have hdet : M.det ≠ 0 := by
      intro hzero
      let i := hi.some
      apply Matrix.GeneralLinearGroup.det_ne_zero (g' i)
      rw [hval i]
      change ((algebraMap K (A i)).mapMatrix M).det = 0
      rw [← RingHom.map_det, hzero, map_zero]
    let q := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
    refine ⟨g', hg'U, q, ?_⟩
    funext i
    exact Units.ext (hval i).symm
  · let : IsEmpty ι := not_nonempty_iff.mp hi
    have hs : Function.Surjective (fun g : Langlands.GeneralLinear n K =>
        fun i => Matrix.GeneralLinearGroup.map (algebraMap K (A i)) g) :=
      fun _ => ⟨1, Subsingleton.elim _ _⟩
    exact hs.denseRange

universe u

/-- Rational \(GL_n\) is dense in the product of its actual completions at
any finite set of finite places of a number field. -/
def RationalGLWeakApproximationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (S : Finset (FinitePlace K)),
    DenseRange (fun g : RationalGL K n => fun v : S =>
      Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K v.val)) g)

theorem rationalGLWeakApproximation : RationalGLWeakApproximationStatement.{u} := by
  intro K _ _ n S
  have hs : Function.Surjective
      (Prod.snd : ((∀ v : InfinitePlace K, InfiniteCompletion K v) ×
        (∀ v : S, FiniteCompletion K v.val)) → ∀ v : S, FiniteCompletion K v.val) :=
    fun x => ⟨(fun _ => 0, x), rfl⟩
  have h : DenseRange (fun x : K => fun v : S => algebraMap K (FiniteCompletion K v.val) x) :=
    hs.denseRange.comp (denseRange_numberFieldFiniteCompletionDiagonal K S) continuous_snd
  exact denseRange_generalLinear_of_denseDiagonal (fun v : S => FiniteCompletion K v.val) h n

end Langlands.Global
