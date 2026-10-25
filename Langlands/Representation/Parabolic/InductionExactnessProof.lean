import Langlands.Representation.Parabolic.ExactnessReciprocityStatement
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Parabolic.NormalizedInductionStatement
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Smooth.Transfer.PullbackProof

noncomputable section

namespace Langlands.Induction

universe uG uU uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Pointwise exactness lifts to image equals kernel in smooth induction when
its first map is injective. The unique pointwise lift retains the right stabilizer. -/
theorem smoothInducedMap_range_eq_ker (P : Subgroup G)
    {ρ : Representation ℂ P U} {σ : Representation ℂ P V}
    {τ : Representation ℂ P W}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hi : Function.Injective i)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap) :
    LinearMap.range (smoothInducedMap P i).toLinearMap =
      LinearMap.ker (smoothInducedMap P q).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hx : i (eval P ρ f x) ∈ LinearMap.ker q.toLinearMap := by
      rw [← hex]
      exact ⟨_, rfl⟩
    exact hx
  · intro f hf
    have hzero : ∀ x, q (eval P σ f x) = 0 := fun x =>
      congrArg (fun f => eval P τ f x) (LinearMap.mem_ker.mp hf)
    have hlift : ∀ x, ∃ u, i u = eval P σ f x := by
      intro x
      apply LinearMap.mem_range.mp
      rw [hex]
      exact hzero x
    choose g hg using hlift
    obtain ⟨K, hK⟩ := f.property
    let f' : SmoothFunctions P ρ := smoothFunctionOf P ρ g (by
      intro p x
      apply hi
      rw [hg, i.isIntertwining, hg]
      exact eval_covariant P σ f p x) K (by
      intro k x
      apply hi
      rw [hg, hg]
      exact congrArg (fun f : EquivariantFunctions P σ => f.1 x) (hK k))
    refine ⟨f', ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hg x

end Langlands.Induction

namespace Langlands.Parabolic

universe uF uU uV uW

/-- Actual unnormalized block-parabolic smooth induction preserves short exact sequences. -/
theorem inductionExactness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    InductionExactnessClause F T B U V W := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  intro ρ σ τ i q _hρ hσ hτ hi hq hex
  dsimp only
  refine ⟨Induction.smoothInducedMap_injective _ _ hi,
    Induction.smoothInducedMap_range_eq_ker _ _ _ hi hex, ?_⟩
  apply Induction.smoothInductionSurjectivity (GeneralLinear n F.Carrier)
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact B.isClosed_parabolic F.Carrier
  · exact isSmooth_comp (B.leviProjection F.Carrier)
      (B.leviProjectionContinuous F.Carrier).continuous hσ
  · exact isSmooth_comp (B.leviProjection F.Carrier)
      (B.leviProjectionContinuous F.Carrier).continuous hτ
  · exact hq

/-- Actual positive-half-modulus normalized induction preserves short exact sequences. -/
theorem normalizedInductionExactness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    NormalizedInductionExactnessClause F T B U V W := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  intro ρ σ τ i q hρ hσ hτ hi hq hex
  let χ := T.leviHalfCharacter B
  exact inductionExactness F T B U V W
    (twist χ.toMonoidHom ρ) (twist χ.toMonoidHom σ) (twist χ.toMonoidHom τ)
    (twistIntertwining χ.toMonoidHom i) (twistIntertwining χ.toMonoidHom q)
    ((isSmooth_twist_iff χ.toMonoidHom ρ χ.isOpen_ker).mpr hρ)
    ((isSmooth_twist_iff χ.toMonoidHom σ χ.isOpen_ker).mpr hσ)
    ((isSmooth_twist_iff χ.toMonoidHom τ χ.isOpen_ker).mpr hτ) hi hq hex

end Langlands.Parabolic
