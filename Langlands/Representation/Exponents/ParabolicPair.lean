import Langlands.Group.GL.BlockIwahoriDefinitions

/-! Concrete conjugates of standard GL block parabolic pairs and actual
restriction of split-component characters. -/

noncomputable section

namespace Langlands.Exponents

universe uR

/-- A concrete presentation of a parabolic pair by a standard block shape
and a conjugating matrix. It contains no representation-theoretic conclusions. -/
structure ConjugateBlockPair (n : ℕ) (R : Type uR) [CommRing R] where
  shape : GeneralLinear.BlockShape n
  conjugator : GeneralLinear n R

namespace ConjugateBlockPair

variable {n : ℕ} {R : Type uR} [CommRing R]

/-- The standard pair is the presentation with conjugating matrix one. -/
def standard (B : GeneralLinear.BlockShape n) : ConjugateBlockPair n R := ⟨B, 1⟩

/-- The actual conjugate upper block parabolic. -/
def parabolic (P : ConjugateBlockPair n R) : Subgroup (GeneralLinear n R) :=
  (P.shape.parabolic R).map (MulAut.conj P.conjugator).toMonoidHom

/-- Coordinates on the actual conjugate split component. -/
def scalarMap (P : ConjugateBlockPair n R) :
    (Fin P.shape.length → Rˣ) →* GeneralLinear n R :=
  (MulAut.conj P.conjugator).toMonoidHom.comp (P.shape.blockScalar R)

@[simp] theorem scalarMap_apply (P : ConjugateBlockPair n R)
    (a : Fin P.shape.length → Rˣ) :
    P.scalarMap a = P.conjugator * P.shape.blockScalar R a * P.conjugator⁻¹ := rfl

/-- The split component as an actual subgroup, not a chosen abstract torus. -/
def splitComponent (P : ConjugateBlockPair n R) : Subgroup (GeneralLinear n R) :=
  P.scalarMap.range

/-- Positive block sizes make the scalar coordinates faithful. -/
theorem scalarMap_injective (P : ConjugateBlockPair n R) :
    Function.Injective P.scalarMap := by
  intro a b hab
  have h : P.shape.blockScalar R a = P.shape.blockScalar R b :=
    (MulAut.conj P.conjugator).injective hab
  funext i
  apply Units.ext
  let j : Fin (P.shape.size i) := ⟨0, P.shape.positive i⟩
  have hij := congrArg (fun g : GeneralLinear n R =>
    g (P.shape.index i j) (P.shape.index i j)) h
  simpa only [GeneralLinear.BlockShape.blockScalar_apply_same, ite_true] using hij

@[simp] theorem standard_scalarMap (B : GeneralLinear.BlockShape n) :
    (standard (R := R) B).scalarMap = B.blockScalar R := by
  apply MonoidHom.ext
  intro a
  change 1 * B.blockScalar R a * 1⁻¹ = B.blockScalar R a
  simp

@[simp] theorem standard_parabolic (B : GeneralLinear.BlockShape n) :
    (standard (R := R) B).parabolic = B.parabolic R := by
  have hc : (MulAut.conj (1 : GeneralLinear n R)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro g
    simp
  change (B.parabolic R).map (MulAut.conj (1 : GeneralLinear n R)).toMonoidHom = _
  rw [hc, Subgroup.map_id]

/-- The fine pair has smaller parabolic and larger split component. -/
def Refines (fine coarse : ConjugateBlockPair n R) : Prop :=
  fine.parabolic ≤ coarse.parabolic ∧ coarse.splitComponent ≤ fine.splitComponent

/-- Strictness concerns the actual pair of subgroups, not its presentation. -/
def StrictlyRefines (fine coarse : ConjugateBlockPair n R) : Prop :=
  fine.Refines coarse ∧ ¬ coarse.Refines fine

theorem refines_refl (P : ConjugateBlockPair n R) : P.Refines P := ⟨le_rfl, le_rfl⟩

theorem Refines.trans {P Q S : ConjugateBlockPair n R}
    (hPQ : P.Refines Q) (hQS : Q.Refines S) : P.Refines S :=
  ⟨hPQ.1.trans hQS.1, hQS.2.trans hPQ.2⟩

theorem strictlyRefines_irrefl (P : ConjugateBlockPair n R) :
    ¬ P.StrictlyRefines P := fun h => h.2 (refines_refl P)

theorem strictlyRefines_iff (P Q : ConjugateBlockPair n R) :
    P.StrictlyRefines Q ↔ P.Refines Q ∧
      (P.parabolic ≠ Q.parabolic ∨ P.splitComponent ≠ Q.splitComponent) := by
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨h, ?_⟩
    by_contra heq
    push Not at heq
    exact hn ⟨heq.1.ge, heq.2.le⟩
  · rintro ⟨h, hne⟩
    refine ⟨h, fun hr => ?_⟩
    rcases hne with hp | ha
    · exact hp (le_antisymm h.1 hr.1)
    · exact ha (le_antisymm hr.2 h.2)

/-- Each coarse scalar has actual fine coordinates under split-component inclusion. -/
theorem exists_scalar_preimage (fine coarse : ConjugateBlockPair n R)
    (h : coarse.splitComponent ≤ fine.splitComponent)
    (a : Fin coarse.shape.length → Rˣ) :
    ∃ b, fine.scalarMap b = coarse.scalarMap a :=
  h ⟨a, rfl⟩

/-- The actual coordinate map for inclusion of split components. -/
def scalarInclusion (fine coarse : ConjugateBlockPair n R)
    (h : coarse.splitComponent ≤ fine.splitComponent) :
    (Fin coarse.shape.length → Rˣ) →* (Fin fine.shape.length → Rˣ) where
  toFun a := Classical.choose (exists_scalar_preimage fine coarse h a)
  map_one' := by
    apply fine.scalarMap_injective
    rw [Classical.choose_spec (exists_scalar_preimage fine coarse h 1), map_one, map_one]
  map_mul' a b := by
    apply fine.scalarMap_injective
    rw [Classical.choose_spec (exists_scalar_preimage fine coarse h (a * b)),
      map_mul, map_mul,
      Classical.choose_spec (exists_scalar_preimage fine coarse h a),
      Classical.choose_spec (exists_scalar_preimage fine coarse h b)]

@[simp] theorem scalarMap_scalarInclusion (fine coarse : ConjugateBlockPair n R)
    (h : coarse.splitComponent ≤ fine.splitComponent)
    (a : Fin coarse.shape.length → Rˣ) :
    fine.scalarMap (scalarInclusion fine coarse h a) = coarse.scalarMap a :=
  Classical.choose_spec (exists_scalar_preimage fine coarse h a)

theorem scalarInclusion_injective (fine coarse : ConjugateBlockPair n R)
    (h : coarse.splitComponent ≤ fine.splitComponent) :
    Function.Injective (scalarInclusion fine coarse h) := by
  intro a b hab
  apply coarse.scalarMap_injective
  simpa only [scalarMap_scalarInclusion] using congrArg fine.scalarMap hab

/-- Exact character extension along the constructed inclusion of actual tori. -/
def CharacterExtends (fine coarse : ConjugateBlockPair n R)
    (h : coarse.splitComponent ≤ fine.splitComponent)
    (ψ : (Fin fine.shape.length → Rˣ) →* ℂˣ)
    (χ : (Fin coarse.shape.length → Rˣ) →* ℂˣ) : Prop :=
  ψ.comp (scalarInclusion fine coarse h) = χ

/-- Equivalent source-coordinate formulation: equal actual scalar matrices
receive equal character values. -/
theorem characterExtends_iff (fine coarse : ConjugateBlockPair n R)
    (h : coarse.splitComponent ≤ fine.splitComponent)
    (ψ : (Fin fine.shape.length → Rˣ) →* ℂˣ)
    (χ : (Fin coarse.shape.length → Rˣ) →* ℂˣ) :
    CharacterExtends fine coarse h ψ χ ↔
      ∀ a b, fine.scalarMap b = coarse.scalarMap a → ψ b = χ a := by
  constructor
  · intro he a b hab
    have hb : b = scalarInclusion fine coarse h a :=
      fine.scalarMap_injective (hab.trans (scalarMap_scalarInclusion fine coarse h a).symm)
    rw [hb]
    exact DFunLike.congr_fun he a
  · intro he
    apply MonoidHom.ext
    intro a
    exact he a _ (scalarMap_scalarInclusion fine coarse h a)

end ConjugateBlockPair
end Langlands.Exponents
