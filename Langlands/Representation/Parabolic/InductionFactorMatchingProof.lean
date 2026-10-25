import Langlands.Representation.Parabolic.InductionFactorMatchingStatement
import Langlands.Representation.Filtration.GradedRefinementProof
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.Data.ENat.BigOperators
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Normalized parabolic induction preserves matching of actual Jordan–Hölder
factors when both induced outputs have finite length. -/

noncomputable section

namespace Langlands.Induction

universe uK uG uV uW uX

open LengthCriterionProof (quotientRep lower)

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]

omit [IsTopologicalGroup G] in
/-- Two smooth induced functions with the same values are equal. -/
theorem smoothFunctions_ext (P : Subgroup G) (σ : Representation k P W)
    {f g : SmoothFunctions P σ} (h : ∀ x, eval P σ f x = eval P σ g x) : f = g :=
  Subtype.ext (Subtype.ext (funext h))

omit [IsTopologicalGroup G] in
theorem smoothFunctions_eq_zero_iff (P : Subgroup G) (σ : Representation k P W)
    (f : SmoothFunctions P σ) : f = 0 ↔ ∀ x, eval P σ f x = 0 :=
  ⟨fun h x => by rw [h]; rfl, fun h => smoothFunctions_ext P σ h⟩

/-- The smooth induced functions all of whose values lie in a fixed subspace.
Right translation preserves this condition for every linear subspace. -/
def valueSubrep (P : Subgroup G) (ρ : Representation k P V) (N : Submodule k V) :
    Subrepresentation (smoothInduced P ρ) where
  toSubmodule :=
    { carrier := {f | ∀ x, eval P ρ f x ∈ N}
      add_mem' := fun hf hg x => N.add_mem (hf x) (hg x)
      zero_mem' := fun _ => N.zero_mem
      smul_mem' := fun a _ hf x => N.smul_mem a (hf x) }
  apply_mem_toSubmodule g _ hf x := hf (x * g)

theorem mem_valueSubrep (P : Subgroup G) (ρ : Representation k P V) (N : Submodule k V)
    (f : SmoothFunctions P ρ) : f ∈ valueSubrep P ρ N ↔ ∀ x, eval P ρ f x ∈ N :=
  Iff.rfl

theorem valueSubrep_mono (P : Subgroup G) (ρ : Representation k P V)
    {N N' : Submodule k V} (h : N ≤ N') : valueSubrep P ρ N ≤ valueSubrep P ρ N' :=
  fun _ hf x => h (hf x)

theorem valueSubrep_bot (P : Subgroup G) (ρ : Representation k P V) :
    valueSubrep P ρ ⊥ = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm _ bot_le
  intro f hf
  change f ∈ (⊥ : Submodule k (SmoothFunctions P ρ))
  rw [Submodule.mem_bot, smoothFunctions_eq_zero_iff]
  exact fun x => (Submodule.mem_bot k).1 (hf x)

theorem valueSubrep_top (P : Subgroup G) (ρ : Representation k P V) :
    valueSubrep P ρ ⊤ = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm le_top
  intro f _ x
  exact Submodule.mem_top

/-- Restricting the codomain of functions with values in `N` to `N`, for a
representation `ρ'` on `N` agreeing with `ρ`. -/
def valueRestriction (P : Subgroup G) (ρ : Representation k P V) {N : Submodule k V}
    (ρ' : Representation k P N) (hρ' : ∀ (p : P) (w : N), ((ρ' p w : N) : V) = ρ p w) :
    (valueSubrep P ρ N).toRepresentation.IntertwiningMap (smoothInduced P ρ') where
  toFun F :=
    ⟨⟨fun x => ⟨eval P ρ F.1 x, F.2 x⟩, fun p x =>
        Subtype.ext ((F.1.1.2 p x).trans (hρ' p ⟨eval P ρ F.1 x, F.2 x⟩).symm)⟩, by
      obtain ⟨K, hK⟩ := F.1.2
      refine ⟨K, fun c => ?_⟩
      apply Subtype.ext
      funext x
      apply Subtype.ext
      exact congrArg (fun f : EquivariantFunctions P ρ => f.1 x) (hK c)⟩
  map_add' _ _ := smoothFunctions_ext P ρ' fun _ => rfl
  map_smul' _ _ := smoothFunctions_ext P ρ' fun _ => rfl
  isIntertwining' _ := LinearMap.ext fun _ => smoothFunctions_ext P ρ' fun _ => rfl

theorem eval_valueRestriction (P : Subgroup G) (ρ : Representation k P V)
    {N : Submodule k V} (ρ' : Representation k P N)
    (hρ' : ∀ (p : P) (w : N), ((ρ' p w : N) : V) = ρ p w)
    (F : (valueSubrep P ρ N).toSubmodule) (x : G) :
    ((eval P ρ' (valueRestriction P ρ ρ' hρ' F) x : N) : V) = eval P ρ F.1 x :=
  rfl

end Langlands.Induction

namespace Langlands.FactorMatchingProof

universe uK uG uV uW

open LengthCriterionProof (quotientRep lower)

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A surjective intertwining map from the upper step whose kernel is exactly the
lower step identifies their successive quotient with the target. -/
theorem nonempty_quotientRep_equiv {ρ : Representation k G V} {σ : Representation k G W}
    {S T : Subrepresentation ρ} (f : T.toRepresentation.IntertwiningMap σ)
    (hf : Function.Surjective f) (hker : ∀ v : T.toSubmodule, f v = 0 ↔ (v : V) ∈ S) :
    Nonempty ((quotientRep S T).Equiv σ) := by
  let Φ := (lower S T).liftQ f.toLinearMap
    (fun v hv => LinearMap.mem_ker.2 ((hker v).2 hv))
  have hΦ (v : T.toSubmodule) : Φ (Submodule.Quotient.mk v) = f v := rfl
  let Ψ : (quotientRep S T).IntertwiningMap σ :=
    { toLinearMap := Φ
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        change Φ (Submodule.Quotient.mk (T.toRepresentation g v)) =
          σ g (Φ (Submodule.Quotient.mk v))
        rw [hΦ, hΦ]
        exact Representation.IntertwiningMap.isIntertwining _ _ f g v }
  refine ⟨Ψ.ofBijective ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Φ (Submodule.Quotient.mk v) = Φ (Submodule.Quotient.mk w) at hxy
    rw [hΦ, hΦ] at hxy
    rw [Submodule.Quotient.eq]
    change ((v - w : T.toSubmodule) : V) ∈ S
    rw [← hker, map_sub, hxy, sub_self]
  · intro y
    obtain ⟨v, rfl⟩ := hf y
    exact ⟨Submodule.Quotient.mk v, hΦ v⟩

/-- The inclusion of an invariant subspace, as an intertwining map. -/
def subrepInclusion {ρ : Representation k G V} (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- In a finite filtration of a representation of finite length, every graded
piece has an actual composition series: lengths add up along the filtration. -/
theorem exists_hasCompositionSeriesLength_graded {A : Rep.{uV} k G} {m : ℕ}
    (s : ObjectRepFiltration A m) (hA : IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule)
    (i : Fin m) : ∃ l, HasCompositionSeriesLength (s.gradedRepresentation i) l := by
  have hA' : repLength A.ρ ≠ ⊤ := Module.length_ne_top_iff.2 hA
  rw [repLength_eq_sum_of_filtration s] at hA'
  have hi : repLength (s.gradedRepresentation i).ρ ≠ ⊤ :=
    ENat.sum_ne_top.1 hA' i (Finset.mem_univ i)
  obtain ⟨c, h₀, h₁⟩ :=
    isFiniteLength_iff_exists_compositionSeries.1 (Module.length_ne_top_iff.1 hi)
  exact ⟨c.length, LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries c h₀ h₁⟩

/-- Equivalent representations have the same factors when one of them has an
actual composition series. -/
theorem haveSameJordanHolderFactors_of_equiv {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    (φ : A.ρ.Equiv B.ρ) (h : ∃ l, HasCompositionSeriesLength A l) :
    HaveSameJordanHolderFactors A B := by
  obtain ⟨l, c, hc⟩ := h
  exact LengthTwo.haveSameJordanHolderFactors_of_equiv φ c hc

end Langlands.FactorMatchingProof

namespace Langlands.Induction

universe uK uG uV uX

open LengthCriterionProof (quotientRep lower)

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {V : Type uV} {X : Type uX}
  [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]

/-- Let `S ≤ N` be subspaces of the inducing space, `ρ'` a representation on `N`
agreeing with `ρ`, and `Q` a surjective intertwining map out of the induction of
`ρ'` whose kernel consists of the functions with all values in `S`. Then the
successive quotient of the functions with values in `S` and in `N` is
equivalent to the target of `Q`. -/
theorem nonempty_valueQuotient_equiv (P : Subgroup G) (ρ : Representation k P V)
    {S N : Submodule k V} (ρ' : Representation k P N)
    (hρ' : ∀ (p : P) (w : N), ((ρ' p w : N) : V) = ρ p w)
    {π : Representation k G X} (Q : (smoothInduced P ρ').IntertwiningMap π)
    (hQ : Function.Surjective Q)
    (hker : ∀ F, Q F = 0 ↔ ∀ x, ((eval P ρ' F x : N) : V) ∈ S) :
    Nonempty ((quotientRep (valueSubrep P ρ S) (valueSubrep P ρ N)).Equiv π) := by
  let ι : ρ'.IntertwiningMap ρ :=
    { toLinearMap := N.subtype
      isIntertwining' := fun p => LinearMap.ext fun w => hρ' p w }
  apply FactorMatchingProof.nonempty_quotientRep_equiv
    (Q.comp (valueRestriction P ρ ρ' hρ'))
  · intro y
    obtain ⟨F', rfl⟩ := hQ y
    refine ⟨⟨smoothInducedMap P ι F', fun x => (eval P ρ' F' x).2⟩, ?_⟩
    change Q (valueRestriction P ρ ρ' hρ' _) = Q F'
    congr 1
  · intro F
    exact hker (valueRestriction P ρ ρ' hρ' F)

/-- The filtration of a smooth induced representation by the functions with
values in the successive steps of a chain of subspaces of the inducing space. -/
def valueFiltration (P : Subgroup G) (ρ : Representation k P V) {m : ℕ}
    (N : Fin (m + 1) → Submodule k V) (hmono : Monotone N) (h₀ : N 0 = ⊥)
    (h₁ : N (Fin.last m) = ⊤) : ObjectRepFiltration (Rep.of (smoothInduced P ρ)) m :=
  ObjectRepFiltration.ofSubrepresentations (fun i => valueSubrep P ρ (N i))
    (fun _ _ h => valueSubrep_mono P ρ (hmono h))
    ((congrArg (valueSubrep P ρ) h₀).trans (valueSubrep_bot P ρ))
    ((congrArg (valueSubrep P ρ) h₁).trans (valueSubrep_top P ρ))

end Langlands.Induction

namespace Langlands.Parabolic

open GeneralLinear
open LengthCriterionProof (quotientRep lower)

universe uF uV uW uX

section Surjectivity

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Right exactness of normalized parabolic induction for given carrier
universes: the induced map of a surjective intertwiner of smooth Levi
representations is surjective. -/
def NormalizedInducedSurjectivity.{uA, uB} : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (Y : Type uA) [AddCommGroup Y] [Module ℂ Y] (Z : Type uB) [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (B.Levi F.Carrier) Y) (σ : Representation ℂ (B.Levi F.Carrier) Z)
    (f : ρ.IntertwiningMap σ), IsSmooth ρ → IsSmooth σ → Function.Surjective f →
      Function.Surjective (T.normalizedParabolicInducedMap B f)

/-- Generic surjectivity of smooth induction from a closed subgroup gives right
exactness of normalized parabolic induction: compact open subgroups of the
actual general linear group are cofinal, the standard block parabolic is
closed, and inflation and twisting by the half modulus preserve smoothness. -/
theorem normalizedInducedSurjectivity_of_smoothInductionSurjectivity.{uA, uB}
    (h : Induction.SmoothInductionSurjectivityStatement.{uF, uA, uB}) :
    NormalizedInducedSurjectivity.{uF, uA, uB} T B := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  intro Y _ _ Z _ _ ρ σ f hρ hσ hf
  refine h (GeneralLinear n F.Carrier) ?_ (B.parabolic F.Carrier)
    (B.isClosed_parabolic F.Carrier) Y Z _ _ ?_ ?_ _ hf
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).2
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous hρ)
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).2
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous hσ)

end Surjectivity

section Matching

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- For a filtration `s` of a smooth Levi representation `σ`, the successive
quotient of the functions with values in two consecutive steps is the
normalized induction of any smooth representation equivalent to the graded
piece, provided normalized induction preserves surjectivity. -/
theorem nonempty_valueQuotient_equiv_induced (σ : Representation ℂ (B.Levi F.Carrier) V)
    {m : ℕ} (s : ObjectRepFiltration (Rep.of σ) m) (i : Fin m)
    (π : Representation ℂ (B.Levi F.Carrier) X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    NormalizedInducedSurjectivity.{uF, uV, uX} T B → IsSmooth σ → IsSmooth π →
      (s.gradedRepresentation i).ρ.Equiv π →
      Nonempty ((quotientRep
        (Induction.valueSubrep (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
          (s.subrepresentation i.castSucc).toSubmodule)
        (Induction.valueSubrep (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
          (s.subrepresentation i.succ).toSubmodule)).Equiv
        (T.normalizedParabolicInduced B π)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hsurj hσ hπ φ
  have hstep : IsSmooth (s.subrepresentation i.succ).toRepresentation :=
    isSmooth_of_injective (FactorMatchingProof.subrepInclusion _) Subtype.val_injective hσ
  let ψ : (s.subrepresentation i.succ).toRepresentation.IntertwiningMap π :=
    φ.toIntertwiningMap.comp (s.gradedProjection i).hom
  have hψ : Function.Surjective ψ :=
    (EquivLike.surjective φ).comp (s.gradedProjection_surjective i)
  refine Induction.nonempty_valueQuotient_equiv (B.parabolic F.Carrier) _
    (twist (T.parabolicHalfModulus B)
      ((s.subrepresentation i.succ).toRepresentation.comp (B.leviProjection F.Carrier)))
    (fun _ _ => rfl) (T.normalizedParabolicInducedMap B ψ) (hsurj _ _ _ _ ψ hstep hπ hψ) ?_
  intro f
  rw [Induction.smoothFunctions_eq_zero_iff]
  refine forall_congr' fun x => ?_
  change φ ((s.gradedProjection i).hom _) = 0 ↔ _
  rw [EmbeddingLike.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- Normalized parabolic induction preserves matching of actual Jordan–Hölder
factors when the first induced output has finite length, provided normalized
induction preserves surjectivity at the needed carrier universes. -/
theorem normalizedInductionOutputMatching_of_surjectivity
    (hVW : NormalizedInducedSurjectivity.{uF, uV, uW} T B)
    (hWW : NormalizedInducedSurjectivity.{uF, uW, uW} T B) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier)),
      NormalizedInductionSourceMatching T B σ τ →
      NormalizedInductionOutputFiniteLength T B σ →
      NormalizedInductionOutputMatching T B σ τ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro σ τ hsrc hfin
  obtain ⟨m, s, t, -, -, e, he⟩ := hsrc
  have hτ (j : Fin m) : IsSmooth (t.gradedRepresentation j).ρ :=
    isSmooth_of_surjective (t.gradedProjection j).hom (t.gradedProjection_surjective j)
      (isSmooth_of_injective (FactorMatchingProof.subrepInclusion _) Subtype.val_injective
        τ.isSmooth)
  let Sσ : ObjectRepFiltration (normalizedInductionObject T B σ) m :=
    Induction.valueFiltration (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (σ.representation.comp (B.leviProjection F.Carrier)))
      (fun i => (s.subrepresentation i).toSubmodule)
      (fun _ _ h => s.monotone_subrepresentation h)
      (congrArg Subrepresentation.toSubmodule s.subrepresentation_zero)
      (congrArg Subrepresentation.toSubmodule s.subrepresentation_last)
  let Sτ : ObjectRepFiltration (normalizedInductionObject T B τ) m :=
    Induction.valueFiltration (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (τ.representation.comp (B.leviProjection F.Carrier)))
      (fun i => (t.subrepresentation i).toSubmodule)
      (fun _ _ h => t.monotone_subrepresentation h)
      (congrArg Subrepresentation.toSubmodule t.subrepresentation_zero)
      (congrArg Subrepresentation.toSubmodule t.subrepresentation_last)
  refine gradedJordanHolderRefinement ℂ (GeneralLinear n F.Carrier)
    (normalizedInductionObject T B σ) (normalizedInductionObject T B τ) m Sσ Sτ e
    fun i => ?_
  obtain ⟨φ⟩ := he i
  obtain ⟨E₁⟩ := nonempty_valueQuotient_equiv_induced T B σ.representation s i _ hVW
    σ.isSmooth (hτ (e i)) φ
  obtain ⟨E₂⟩ := nonempty_valueQuotient_equiv_induced T B τ.representation t (e i) _ hWW
    τ.isSmooth (hτ (e i)) (Representation.Equiv.refl _)
  exact FactorMatchingProof.haveSameJordanHolderFactors_of_equiv (E₁.trans E₂.symm)
    (FactorMatchingProof.exists_hasCompositionSeriesLength_graded Sσ hfin i)

end Matching

/-- The factor-matching theorem, conditional on generic surjectivity of smooth
induction at the two needed pairs of carrier universes. The finite length of
the second induced output is not needed. -/
theorem normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity
    (hVW : Induction.SmoothInductionSurjectivityStatement.{uF, uV, uW})
    (hWW : Induction.SmoothInductionSurjectivityStatement.{uF, uW, uW}) :
    NormalizedInductionFactorMatchingTheorem.{uF, uV, uW} := by
  intro p _ F T n B σ τ hsrc hfin _
  exact normalizedInductionOutputMatching_of_surjectivity T B
    (normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B hVW)
    (normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B hWW) σ τ hsrc hfin

/-- Normalized parabolic induction preserves matching of actual Jordan–Hölder
factors when both induced outputs have finite length. -/
theorem normalizedInductionFactorMatchingTheorem :
    NormalizedInductionFactorMatchingTheorem.{uF, uV, uW} :=
  normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity
    Induction.smoothInductionSurjectivity Induction.smoothInductionSurjectivity

end Langlands.Parabolic
