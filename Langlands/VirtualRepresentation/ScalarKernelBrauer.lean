import Langlands.VirtualRepresentation.ScalarKernelInduction
import Langlands.VirtualRepresentation.FiniteInflation
import Langlands.VirtualRepresentation.ExactInductionTwist
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Representation.Finite.BrauerTheoryProof

/-!
# Brauer induction for representations that are scalar on a finite-index kernel

Let `π : S →* Q` be a homomorphism of a topological group onto a finite group,
with open kernel. Let `B` be a continuous finite-dimensional complex representation
of `S` on which the kernel of `π` acts by scalars. Then the exact virtual class of
`B` is an integral combination of classes `Ind_{π⁻¹ H}^S θ` for subgroups `H` of
`Q` and continuous characters `θ` of `π⁻¹ H`.

The proof applies the published finite Brauer theorem to the finite group
`normalizedImage ρ` of determinant-one scalar multiples of the image of `ρ = B`,
and transports the resulting identity along the additive map given by scalar
lifts of tautological parts.
-/

noncomputable section

universe uG uQ uV uS uW uY

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

section Generators

variable {K : Type*} [Field K] {G : Type uG} [Group G]

/-- A representation of rank zero has virtual class zero. -/
theorem ofRepresentation_eq_zero_of_rank_eq_zero
    (P : FiniteRepresentation.{_, uG, uV} K G → Prop) (A : {A // P A})
    (h : A.val.rank = 0) : ofRepresentation P A = 0 := by
  have hs : Subsingleton A.val := Module.finrank_zero_iff.mp h
  have hA := ofRepresentation_shortExact P (A := A) (B := A) (C := A)
    (f := ⟨LinearMap.id, fun _ => rfl⟩)
    (g := ⟨0, fun _ => by rw [LinearMap.zero_comp, LinearMap.comp_zero]⟩)
    ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨y, Subsingleton.elim _ _⟩, by
      rw [LinearMap.range_id]
      exact (LinearMap.ker_zero).symm⟩
  simpa using hA

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Induced character classes from equal subgroups agree up to the character. -/
theorem continuousInduce_characterClass_congr {T₁ T₂ : Subgroup G} [T₁.FiniteIndex]
    [T₂.FiniteIndex] (h : T₁ = T₂) (h₁ : IsOpen (T₁ : Set G)) (h₂ : IsOpen (T₂ : Set G))
    (θ : T₁ →ₜ* ℂˣ) :
    ∃ θ' : T₂ →ₜ* ℂˣ, continuousInduce T₁ h₁ (characterClass.{uG, uV} θ) =
      continuousInduce T₂ h₂ (characterClass.{uG, uV} θ') := by
  subst h
  exact ⟨θ, rfl⟩

variable {Q : Type uQ} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isOpen_comap_of_isOpen_ker (π : G →* Q) (hπ : IsOpen (π.ker : Set G))
    (H : Subgroup Q) : IsOpen (H.comap π : Set G) :=
  Subgroup.isOpen_mono (fun g hg => by
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_comap, hg]
    exact H.one_mem) hπ

/-- The classes `Ind_{π⁻¹ H}^G θ` for subgroups `H` of `Q` and continuous
characters `θ` of `π⁻¹ H`, with carriers in universe `max uG uV`. -/
def quotientInducedGenerators (π : G →* Q) (hπ : IsOpen (π.ker : Set G)) :
    Set (ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, max uG uV} ℂ G => A.IsContinuous)) :=
  {x | ∃ (H : Subgroup Q) (θ : H.comap π →ₜ* ℂˣ),
    x = continuousInduce (H.comap π) (isOpen_comap_of_isOpen_ker π hπ H)
      (characterClass.{uG, max uG uV} θ)}

/-- Every subgroup containing the kernel gives generators. -/
theorem mem_quotientInducedGenerators_of_ker_le (π : G →* Q) (hπ : IsOpen (π.ker : Set G))
    {T : Subgroup G} [T.FiniteIndex] (hT : π.ker ≤ T) (hTo : IsOpen (T : Set G))
    (θ : T →ₜ* ℂˣ) :
    continuousInduce T hTo (characterClass.{uG, max uG uV} θ) ∈
      quotientInducedGenerators π hπ := by
  obtain ⟨θ', hθ'⟩ := continuousInduce_characterClass_congr.{uG, max uG uV}
    (Subgroup.comap_map_eq_self hT).symm hTo
    (isOpen_comap_of_isOpen_ker π hπ (T.map π)) θ
  exact ⟨T.map π, θ', hθ'⟩

end Generators

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.VirtualRepresentation.ScalarKernel

open FiniteRepresentation ExactGrothendieckGroup

/-- A representation with carrier lifted to the universe `uW`. -/
def liftRep {G : Type uG} [Group G] {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    [Module.Finite ℂ Y] (σ : Representation ℂ G Y) :
    FiniteRepresentation.{0, uG, max uY uW} ℂ G :=
  FiniteRepresentation.of
    ((ULift.moduleEquiv : ULift.{uW} Y ≃ₗ[ℂ] Y).symm.conjRingEquiv.toMonoidHom.comp σ)

/-- The lift is equivalent to the original representation. -/
def liftRepEquiv {G : Type uG} [Group G] {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    [Module.Finite ℂ Y] (σ : Representation ℂ G Y) :
    Representation.Equiv σ (liftRep σ : FiniteRepresentation.{0, uG, max uY uW} ℂ G).representation :=
  Representation.Equiv.mk ULift.moduleEquiv.symm (by
    intro g
    ext v
    rfl)

/-- The continuous exact virtual group of `S` with carriers in universe `max uS uW`. -/
abbrev ContinuousExact (S : Type uS) [Group S] [TopologicalSpace S] :=
  ExactGrothendieckGroup
    (fun A : FiniteRepresentation.{0, uS, max uS uW} ℂ S => A.IsContinuous)

section Lift

variable {S : Type uS} [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  (ρ : Representation ℂ S V) (hρ : (FiniteRepresentation.of ρ).IsContinuous)
  {N : Subgroup S} (hNo : IsOpen (N : Set S)) (hN : ∀ n ∈ N, ∃ c : ℂ, ρ n = c • 1)

include hρ hNo hN

theorem isContinuous_liftRep_scalarLift (U : FDRep ℂ (normalizedImage ρ)) :
    (liftRep (scalarLift ρ U.ρ) : FiniteRepresentation.{0, uS, max uS uW} ℂ S).IsContinuous :=
  (isContinuous_iff_of_equiv (A := FiniteRepresentation.of (scalarLift ρ U.ρ))
    (B := (liftRep (scalarLift ρ U.ρ) : FiniteRepresentation.{0, uS, max uS uW} ℂ S))
    (liftRepEquiv (scalarLift ρ U.ρ))).mp (isContinuous_scalarLift ρ U.ρ hρ hNo hN)

/-- The scalar lift of the tautological part, on isomorphism classes of finite
representations of the normalized image. -/
def scalarLiftClass :
    FiniteRep.RepClass ℂ (normalizedImage ρ) → ContinuousExact.{uS, uW} S :=
  Quotient.lift
    (fun U => ofRepresentation _ ⟨liftRep (scalarLift ρ U.ρ),
      isContinuous_liftRep_scalarLift ρ hρ hNo hN U⟩)
    (fun _ _ ⟨e⟩ => ofRepresentation_eq_of_equiv _
      ((liftRepEquiv _).symm.trans
        ((scalarLiftEquiv ρ (FiniteRep.equivOfIso e)).trans (liftRepEquiv _))))

theorem scalarLiftClass_classOf (U : FDRep ℂ (normalizedImage ρ)) :
    scalarLiftClass ρ hρ hNo hN (FiniteRep.classOf U) =
      ofRepresentation _ ⟨liftRep (scalarLift ρ U.ρ),
        isContinuous_liftRep_scalarLift ρ hρ hNo hN U⟩ := rfl

theorem scalarLiftClass_add (a b : FiniteRep.RepClass ℂ (normalizedImage ρ)) :
    (scalarLiftClass ρ hρ hNo hN (a + b) : ContinuousExact.{uS, uW} S) =
      scalarLiftClass ρ hρ hNo hN a + scalarLiftClass ρ hρ hNo hN b := by
  induction a using Quotient.inductionOn with | h U =>
  induction b using Quotient.inductionOn with | h U' =>
  change ofRepresentation (fun A : FiniteRepresentation.{0, uS, max uS uW} ℂ S =>
      A.IsContinuous) ⟨liftRep (scalarLift ρ (FiniteRep.sumRep U U').ρ), _⟩ =
    ofRepresentation _ ⟨liftRep (scalarLift ρ U.ρ), _⟩ +
      ofRepresentation _ ⟨liftRep (scalarLift ρ U'.ρ), _⟩
  exact ofRepresentation_eq_add_of_equiv_prod _ _ _ _
    ((liftRepEquiv _).symm.trans ((scalarLiftProdEquiv ρ).trans
      (FiniteRep.prodEquiv (liftRepEquiv _) (liftRepEquiv _))))

/-- The scalar lift on the split Grothendieck group of the normalized image. -/
def scalarLiftVirtual :
    FiniteRep.VirtualRep ℂ (normalizedImage ρ) →ₗ[ℤ] ContinuousExact.{uS, uW} S :=
  (Algebra.GrothendieckAddGroup.lift
    (AddMonoidHom.mk' (scalarLiftClass ρ hρ hNo hN) (scalarLiftClass_add ρ hρ hNo hN))).toIntLinearMap

theorem scalarLiftVirtual_ofClass (a : FiniteRep.RepClass ℂ (normalizedImage ρ)) :
    (scalarLiftVirtual ρ hρ hNo hN (FiniteRep.ofClass a) : ContinuousExact.{uS, uW} S) =
      scalarLiftClass ρ hρ hNo hN a :=
  FiniteRep.completionLift_of _ a

/-- The scalar lift of the tautological representation is the class of `ρ`. -/
theorem scalarLiftVirtual_tautological (B : FiniteRepresentation.{0, uS, max uS uW} ℂ S)
    (hB : B.IsContinuous) (e : Representation.Equiv ρ B.representation) :
    scalarLiftVirtual ρ hρ hNo hN
        (FiniteRep.ofClass (FiniteRep.classOfRepresentation (tautological ρ))) =
      ofRepresentation _ ⟨B, hB⟩ := by
  rw [scalarLiftVirtual_ofClass]
  exact ofRepresentation_eq_of_equiv _
    ((liftRepEquiv _).symm.trans ((scalarLiftEquiv ρ (FiniteRep.modelEquiv _).symm).trans
      ((scalarLiftTautologicalEquiv ρ).trans e)))

end Lift

section Main

variable {S : Type uS} [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
  {Q : Type uQ} [Group Q] [Finite Q] (π : S →* Q) (hπ : IsOpen (π.ker : Set S))
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  (ρ : Representation ℂ S V) (hρ : (FiniteRepresentation.of ρ).IsContinuous)
  (hN : ∀ n ∈ π.ker, ∃ c : ℂ, ρ n = c • 1)

/-- The scalar lift of a class induced from a character of a subgroup of the
normalized image is zero or a generator. -/
theorem scalarLiftVirtual_induce_mem [Finite (normalizedImage ρ)]
    (A : Subgroup (normalizedImage ρ)) (ψ : A →* ℂˣ) :
    (scalarLiftVirtual ρ hρ hπ hN (FiniteRep.ofClass (FiniteRep.induce A
        (FiniteRep.classOf (FiniteRep.oneDimensional ψ)))) : ContinuousExact.{uS, uW} S) ∈
      Submodule.span ℤ (quotientInducedGenerators.{uS, uQ, uW} π hπ) := by
  rw [scalarLiftVirtual_ofClass]
  change ofRepresentation _ ⟨(liftRep (scalarLift ρ
      (FiniteRep.induceRep A (FiniteRep.oneDimensional ψ)).ρ) :
        FiniteRepresentation.{0, uS, max uS uW} ℂ S), _⟩ ∈ _
  let e₁ := (FiniteRep.induceRepEquiv A (FiniteRep.oneDimensional ψ)).symm.trans
    (FiniteRep.indCoindEquiv A (FiniteRep.oneDimensional ψ))
  have hχ : ∀ (a : A) (x : ℂ), (FiniteRep.oneDimensional ψ).ρ a x = (ψ a : ℂ) * x :=
    fun _ _ => rfl
  by_cases hψ : IsTautOn ρ A ψ
  · have hT : π.ker ≤ scalarPreimage ρ A := le_scalarPreimage ρ A hN
    have : (scalarPreimage ρ A).FiniteIndex := Subgroup.finiteIndex_of_le hT
    have hTo : IsOpen (scalarPreimage ρ A : Set S) := Subgroup.isOpen_mono hT hπ
    let θ := continuousScalarCharacter ρ hψ hρ hπ hN
    have heq : ofRepresentation _ ⟨(liftRep (scalarLift ρ
        (FiniteRep.induceRep A (FiniteRep.oneDimensional ψ)).ρ) :
          FiniteRepresentation.{0, uS, max uS uW} ℂ S),
          isContinuous_liftRep_scalarLift ρ hρ hπ hN _⟩ =
        continuousInduce (scalarPreimage ρ A) hTo (characterClass.{uS, max uS uW} θ) := by
      simp only [ExactGrothendieckGroup.continuousInduce, characterClass,
        induce_ofRepresentation]
      exact ofRepresentation_eq_of_equiv _ ((liftRepEquiv _).symm.trans
        ((scalarLiftEquiv ρ e₁).trans
          (coindScalarLiftEquiv ρ (FiniteRep.oneDimensional ψ).ρ hχ hψ)))
    rw [heq]
    exact Submodule.subset_span (mem_quotientInducedGenerators_of_ker_le π hπ hT hTo θ)
  · have hbot := tautPart_coind_eq_bot ρ (FiniteRep.oneDimensional ψ).ρ hχ hψ
    have hsub : Subsingleton
        (tautPart ρ (FiniteRep.induceRep A (FiniteRep.oneDimensional ψ)).ρ) := by
      have : Subsingleton (tautPart ρ
          (Representation.coind A.subtype (FiniteRep.oneDimensional ψ).ρ)) :=
        not_nontrivial_iff_subsingleton.mp fun h => Submodule.nontrivial_iff_ne_bot.mp h hbot
      exact (tautPartLinearEquiv ρ e₁).toEquiv.subsingleton
    rw [ofRepresentation_eq_zero_of_rank_eq_zero]
    · exact Submodule.zero_mem _
    · change Module.finrank ℂ (ULift.{max uS uW}
        (tautPart ρ (FiniteRep.induceRep A (FiniteRep.oneDimensional ψ)).ρ)) = 0
      exact Module.finrank_zero_of_subsingleton

end Main

/-- **Brauer induction for representations scalar on a finite-index kernel.**
If `π : S →* Q` has finite target and open kernel, and the kernel acts on the
continuous representation `B` by scalars, then the class of `B` is an integral
combination of classes `Ind_{π⁻¹ H}^S θ` of continuous characters. -/
theorem ofRepresentation_mem_span_of_scalar {S : Type uS} [Group S] [TopologicalSpace S]
    [IsTopologicalGroup S] {Q : Type uQ} [Group Q] [Finite Q] (π : S →* Q)
    (hπ : IsOpen (π.ker : Set S)) (B : FiniteRepresentation.{0, uS, max uS uW} ℂ S)
    (hB : B.IsContinuous) (hscalar : ∀ n ∈ π.ker, ∃ c : ℂ, B.representation n = c • 1) :
    ofRepresentation _ ⟨B, hB⟩ ∈
      Submodule.span ℤ (quotientInducedGenerators.{uS, uQ, uW} π hπ) := by
  classical
  rcases subsingleton_or_nontrivial B with hsub | hnt
  · rw [ofRepresentation_eq_zero_of_rank_eq_zero _ _ Module.finrank_zero_of_subsingleton]
    exact Submodule.zero_mem _
  let ρ := B.representation
  have hρ : (FiniteRepresentation.of ρ).IsContinuous := hB
  have : Finite (normalizedImage ρ) := finite_normalizedImage ρ π.ker hscalar
  let : Fintype (normalizedImage ρ) := Fintype.ofFinite _
  obtain ⟨c, hc⟩ := (FiniteRep.BrauerTheory.finiteBrauerTheory (normalizedImage ρ)).2.2.2.2.2.1
    (FiniteRep.ofClass (FiniteRep.classOfRepresentation (tautological ρ)))
  rw [← scalarLiftVirtual_tautological ρ hρ hπ hscalar B hB (Representation.Equiv.refl _), ← hc,
    FiniteRep.brauerExpansion, Finsupp.apply_linearCombination]
  have hmem := LinearMap.mem_range_self (Finsupp.linearCombination ℤ
    ((scalarLiftVirtual ρ hρ hπ hscalar) ∘ fun d : FiniteRep.MonomialDatum ℂ (normalizedImage ρ) =>
      FiniteRep.ofClass (FiniteRep.induce d.1
        (FiniteRep.classOf (FiniteRep.oneDimensional d.2))))) c
  rw [Finsupp.range_linearCombination] at hmem
  refine Submodule.span_le.mpr ?_ hmem
  rintro _ ⟨d, rfl⟩
  exact scalarLiftVirtual_induce_mem π hπ ρ hρ hscalar d.1 d.2

end Langlands.VirtualRepresentation.ScalarKernel
