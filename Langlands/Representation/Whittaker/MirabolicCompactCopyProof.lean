import Langlands.Representation.Whittaker.MirabolicCompactCopyStatement
import Langlands.Representation.Whittaker.MirabolicMinimalityProof
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Topology.Nonarchimedean.Subgroup
import Langlands.Group.GL.Nonarchimedean
import Langlands.Group.GL.Padic

/-!
# Proof of nonzero compact standard maps into actual mirabolic subrepresentations

The published compact-minimality theorem `mirabolicCompactMinimality`, proved by an
independent induction on rank, puts the compact functions inside every nonzero
subrepresentation `W` of the smooth mirabolic induction. Corestricting the canonical
compact inclusion to `W` gives an intertwiner. It is nonzero because the inclusion is
injective and a compactly supported covariant local section with value one at the
identity exists. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Whittaker

namespace MirabolicCompactCopy

open GeneralLinear HarmonicAnalysis

universe uF

section Generic

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
variable (ψ : UnitaryAdditiveCharacter K) (n : ℕ)

/-- The canonical compact inclusion, corestricted to a subrepresentation that contains
the compact-support subrepresentation. -/
def compactInclusionInto (W : Subrepresentation (mirabolicSmoothInduced ψ n))
    (hW : mirabolicCompactSubrepresentation ψ n ≤ W) :
    (mirabolicCompactInduced ψ n).IntertwiningMap W.toRepresentation where
  toLinearMap := (mirabolicCompactInclusion ψ n).toLinearMap.codRestrict W.toSubmodule
    fun f => hW f.property
  isIntertwining' _ := by ext f x; rfl

@[simp] theorem compactInclusionInto_apply (W : Subrepresentation (mirabolicSmoothInduced ψ n))
    (hW : mirabolicCompactSubrepresentation ψ n ≤ W) (f : MirabolicCompactFunctions ψ n) :
    ((compactInclusionInto ψ n W hW f : W.toSubmodule) : MirabolicSmoothFunctions ψ n) =
      f.val := rfl

/-- The scalar character representation is smooth: its kernel is open. -/
theorem characterRepresentation_smooth [NonarchimedeanGroup (mirabolic n K)] :
    IsSmooth (mirabolicCharacterRepresentation ψ n) := by
  intro z
  refine ⟨{ toSubgroup := (mirabolicCharacter ψ n).ker
            isOpen' := Langlands.isOpen_ker_of_continuous_complex_character _
              (mirabolicCharacterContinuous ψ n).continuous }, ?_⟩
  intro k
  change (mirabolicCharacter ψ n k : ℂ) * z = z
  rw [show mirabolicCharacter ψ n k = 1 from k.property, Units.val_one, one_mul]

/-- A compactly supported covariant function with value one at the identity. -/
theorem exists_compactEval_one_ne_zero
    [NonarchimedeanGroup (mirabolic n K)] [WeaklyLocallyCompactSpace (mirabolic n K)] :
    ∃ f : MirabolicCompactFunctions ψ n, mirabolicCompactEval ψ n f 1 ≠ 0 := by
  refine ⟨Induction.compactLocalSection _ _ (characterRepresentation_smooth ψ n)
    1 1 Set.univ isOpen_univ (Set.mem_univ _), ?_⟩
  have h := Induction.compactLocalSection_apply _ _ (characterRepresentation_smooth ψ n)
    (1 : mirabolic n K) (1 : ℂ) Set.univ isOpen_univ (Set.mem_univ _)
  change Induction.eval _ _ _ 1 ≠ 0
  rw [h]
  exact one_ne_zero

/-- The corestricted inclusion is nonzero once a nonzero compact function exists. -/
theorem compactInclusionInto_ne_zero
    [NonarchimedeanGroup (mirabolic n K)] [WeaklyLocallyCompactSpace (mirabolic n K)]
    (W : Subrepresentation (mirabolicSmoothInduced ψ n))
    (hW : mirabolicCompactSubrepresentation ψ n ≤ W) :
    compactInclusionInto ψ n W hW ≠ 0 := by
  intro h0
  obtain ⟨f, hf⟩ := exists_compactEval_one_ne_zero ψ n
  apply hf
  have hval := congrArg
    (fun A : (mirabolicCompactInduced ψ n).IntertwiningMap W.toRepresentation =>
      ((A f : W.toSubmodule) : MirabolicSmoothFunctions ψ n)) h0
  change f.val = 0 at hval
  change mirabolicEval ψ n f.val 1 = 0
  rw [hval]
  rfl

end Generic

end MirabolicCompactCopy

open MirabolicCompactCopy in
/-- Every nonzero subrepresentation of the actual smooth mirabolic induction over a
p-adic field with its canonical topology receives a nonzero intertwiner from the compact
induction; the input of Bernstein–Zelevinsky (1976), Proposition 5.15(c). -/
theorem mirabolicNonzeroCompactMap : MirabolicNonzeroCompactMapStatement.{uF} := by
  intro p hp F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  intro n ψ W hW
  let : NonarchimedeanGroup (GeneralLinear (n + 1) F.Carrier) :=
    Langlands.valuativeGeneralLinearNonarchimedean F.Carrier (n + 1)
  let : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  let : LocallyCompactSpace (GeneralLinear.mirabolic n F.Carrier) :=
    GeneralLinear.Mirabolic.locallyCompactSpace
  have hmin := mirabolicCompactMinimality p hp F n ψ W hW
  exact ⟨compactInclusionInto ψ n W hmin, compactInclusionInto_ne_zero ψ n W hmin⟩

end Langlands.Whittaker
