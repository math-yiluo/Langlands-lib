import Langlands.BaseChange.Norm
import Langlands.BaseChange.TwistedCharacter
import Langlands.Group.GL.Blocks
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Category.Basic
import Langlands.Representation.Character.Basic
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Smooth.Definitions

/-!
# Tempered representations, σ-discrete series and (twisted) pseudo-coefficients

Generic part, for a topological group `G`: temperedness for every Haar measure on `G/Z`,
the central character of an unbundled representation, pseudo-coefficients with a fixed
central character (Kazhdan 1986, Theorem K(a)) and twisted pseudo-coefficients for an
automorphism `θ` of `G` (Henniart–Lemaire 2011, II.5.13; Arthur–Clozel 1989, Chapter 1,
Corollary 2.10). `GL_n` part: the entrywise action of `σ` on the standard Levi subgroups
and σ-discrete series representations of `GL_n(E)` (Henniart–Lemaire, II.4.6 and II.1.7;
Arthur–Clozel, Chapter 1, §2.3). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure GeneralLinear

universe uG uV uV' uW uW' uX u v

/-! ## Central characters -/

section CentralCharacter

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']

/-- The centre of `G` acts on `ρ` through the character `χ`: `ρ z v = χ(z) v` for every
central `z` and every `v` (HL's `ω_Π = χ`). This is `SmoothRep.HasCentralCharacter` for a
representation that is not bundled as a `SmoothRep`. -/
def HasCentralCharacterRep (ρ : Representation ℂ G V) (χ : Subgroup.center G →* ℂˣ) : Prop :=
  ∀ (z : Subgroup.center G) (v : V), ρ z v = (χ z : ℂ) • v

/-- The central character is transported along an isomorphism of representations. -/
theorem HasCentralCharacterRep.of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') {χ : Subgroup.center G →* ℂˣ}
    (h : HasCentralCharacterRep ρ χ) : HasCentralCharacterRep ρ' χ := by
  intro z w
  calc ρ' z w = ρ' z (e (e.symm w)) := by rw [Representation.Equiv.apply_symm_apply]
    _ = e (ρ z (e.symm w)) :=
      (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap z (e.symm w)).symm
    _ = (χ z : ℂ) • w := by
      rw [h z (e.symm w), map_smul, Representation.Equiv.apply_symm_apply]

end CentralCharacter

/-! ## Temperedness -/

section Tempered

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']

/-- `ρ` is tempered: with the Borel σ-algebra on `G ⧸ Subgroup.center G`, the Library's
`IsTemperedModCenter ρ μ` holds for every Haar measure `μ` on the central quotient (admissible,
with a unitary central character, and with matrix coefficients in `L^(2+ε)(G/Z)` for every
`ε > 0`). -/
def IsTemperedRep (ρ : Representation ℂ G V) : Prop :=
  letI : MeasurableSpace (G ⧸ Subgroup.center G) := borel _
  haveI : BorelSpace (G ⧸ Subgroup.center G) := ⟨rfl⟩
  ∀ (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure], IsTemperedModCenter ρ μ

/-- Temperedness is invariant under isomorphism. -/
theorem isTemperedRep_iff_of_equiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') :
    IsTemperedRep ρ ↔ IsTemperedRep ρ' := by
  let _ : MeasurableSpace (G ⧸ Subgroup.center G) := borel _
  have _ : BorelSpace (G ⧸ Subgroup.center G) := ⟨rfl⟩
  exact forall_congr' fun μ => forall_congr' fun _ => isTemperedModCenter_iff_of_equiv e μ

/-- A tempered representation of a locally compact group is admissible: the central
quotient then carries a Haar measure. -/
theorem IsTemperedRep.isAdmissible [LocallyCompactSpace G] {ρ : Representation ℂ G V}
    (h : IsTemperedRep ρ) : IsAdmissible ρ := by
  let _ : MeasurableSpace (G ⧸ Subgroup.center G) := borel _
  have _ : BorelSpace (G ⧸ Subgroup.center G) := ⟨rfl⟩
  exact (h (Measure.haarMeasure (Classical.arbitrary _))).1

/-- For `GL_n` over a `p`-adic field with the topology of `T`, `IsTemperedRep` is the
Library's `PadicField.TopologicalData.IsTempered`. -/
theorem isTemperedRep_iff_isTempered {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
    (T : F.TopologicalData) {n : ℕ} (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup n
    IsTemperedRep ρ ↔ T.IsTempered ρ :=
  Iff.rfl

end Tempered

/-! ## Pseudo-coefficients and twisted pseudo-coefficients -/

section PseudoCoefficient

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]

/-- `f` is a pseudo-coefficient of `π` with central character `χ` (Kazhdan 1986,
Theorem K(a), with a fixed central character as in Arthur–Clozel, Chapter 1, Corollary 2.10
and Henniart–Lemaire, II.5.13): `π` has central character `χ`, `Θ_π(f) = 1`, and
`Θ_π'(f) = 0` for every irreducible admissible tempered `π'` (carrier in the universe of
`V`) with central character `χ` that is not isomorphic to `π`. -/
def IsPseudoCoefficient (χ : Subgroup.center G →* ℂˣ) (π : Representation ℂ G V)
    (hπ : IsAdmissible π) (f : SchwartzBruhat G) : Prop :=
  HasCentralCharacterRep π χ ∧ Character.distribution μ π hπ f = 1 ∧
    ∀ (V' : Type uV) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ G V')
      (hπ' : IsAdmissible π'), π'.IsIrreducible → IsTemperedRep π' →
        HasCentralCharacterRep π' χ → IsEmpty (π'.Equiv π) →
          Character.distribution μ π' hπ' f = 0

/-- `φ` is a twisted pseudo-coefficient of the θ-representation `(τ, A)` with central
character `χ` (Henniart–Lemaire, II.5.13, Définition; Arthur–Clozel, Chapter 1,
Corollary 2.10): `τ` has central character `χ`, `Θ^A_τ(φ) = 1`, and `Θ^{A'}_{τ'}(φ) = 0` for
every irreducible admissible tempered `τ'` (carrier in the universe of `W`) with central
character `χ` that is not isomorphic to `τ`, and every isomorphism `A'` of `τ'` onto
`τ' ∘ θ`. -/
def IsTwistedPseudoCoefficient (θ : G ≃* G) (χ : Subgroup.center G →* ℂˣ)
    (τ : Representation ℂ G W) (hτ : IsAdmissible τ)
    (A : τ.Equiv (τ.comp θ.toMonoidHom)) (φ : SchwartzBruhat G) : Prop :=
  HasCentralCharacterRep τ χ ∧ twistedDistribution μ τ hτ A.toLinearMap φ = 1 ∧
    ∀ (W' : Type uW) [AddCommGroup W'] [Module ℂ W'] (τ' : Representation ℂ G W')
      (hτ' : IsAdmissible τ'), τ'.IsIrreducible → IsTemperedRep τ' →
        HasCentralCharacterRep τ' χ → IsEmpty (τ'.Equiv τ) →
          ∀ A' : τ'.Equiv (τ'.comp θ.toMonoidHom),
            twistedDistribution μ τ' hτ' A'.toLinearMap φ = 0

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- For a bundled smooth representation, `SmoothRep.HasCentralCharacter` is
`HasCentralCharacterRep` of its underlying representation. -/
theorem smoothRep_hasCentralCharacter_iff (A : SmoothRep.{0, uG, uV} ℂ G)
    (χ : Subgroup.center G →* ℂˣ) :
    A.HasCentralCharacter χ ↔ HasCentralCharacterRep A.representation χ :=
  Iff.rfl

/-- The twisted character evaluated through any finite-rank operator equal to
`ρ(φ) ∘ A`. -/
private theorem twistedDistribution_eq_trace (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (A : Module.End ℂ V) (φ : SchwartzBruhat G) (T : finiteRankEnd V)
    (hT : T.val = Hecke.integratedAction μ ρ hρ.1 φ ∘ₗ A) :
    twistedDistribution μ ρ hρ A φ = FiniteRankEnd.trace T := by
  rw [twistedDistribution_apply]
  congr 1
  exact Subtype.ext hT.symm

/-- Twisted characters are invariant under a linear equivalence that intertwines the
representations and the operators. -/
theorem twistedDistribution_eq_of_equivariant (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) (ρ' : Representation ℂ G V') (hρ' : IsAdmissible ρ')
    (A : Module.End ℂ V) (A' : Module.End ℂ V') (e : V ≃ₗ[ℂ] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hA : ∀ v, e (A v) = A' (e v)) :
    twistedDistribution μ ρ hρ A = twistedDistribution μ ρ' hρ' A' := by
  ext φ
  let T : finiteRankEnd V := ⟨Hecke.integratedAction μ ρ hρ.1 φ ∘ₗ A,
    (Character.finiteRankIntegratedAction μ ρ hρ φ).property.comp_right A⟩
  rw [twistedDistribution_eq_trace μ ρ hρ A φ T rfl,
    twistedDistribution_eq_trace μ ρ' hρ' A' φ (FiniteRankEnd.conjugate e T) ?_,
    FiniteRankEnd.trace_conjugate]
  ext w
  have h1 : A' w = e (A (e.symm w)) := by rw [hA, LinearEquiv.apply_symm_apply]
  rw [LinearMap.comp_apply, h1, FiniteRankEnd.conjugate_apply]
  exact Hecke.integratedAction_intertwiner μ hρ.1 hρ'.1
    (e.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ' he) φ (A (e.symm w))

/-- A twisted pseudo-coefficient of `(τ, A)` has twisted trace `1` at every `(τ', A')`
isomorphic to `(τ, A)`. -/
theorem IsTwistedPseudoCoefficient.twistedDistribution_eq_one {θ : G ≃* G}
    {χ : Subgroup.center G →* ℂˣ} {τ : Representation ℂ G W} {hτ : IsAdmissible τ}
    {A : τ.Equiv (τ.comp θ.toMonoidHom)} {φ : SchwartzBruhat G}
    (h : IsTwistedPseudoCoefficient μ θ χ τ hτ A φ)
    {W' : Type uW'} [AddCommGroup W'] [Module ℂ W'] (τ' : Representation ℂ G W')
    (hτ' : IsAdmissible τ') (A' : τ'.Equiv (τ'.comp θ.toMonoidHom)) (e : τ'.Equiv τ)
    (he : ∀ w, e (A' w) = A (e w)) :
    twistedDistribution μ τ' hτ' A'.toLinearMap φ = 1 := by
  rw [twistedDistribution_eq_of_equivariant μ τ' hτ' τ hτ A'.toLinearMap A.toLinearMap
    e.toLinearEquiv
    (fun g v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v) he]
  exact h.2.1

/-- For `θ = id` and `A = id`, a twisted pseudo-coefficient is a pseudo-coefficient. -/
theorem isPseudoCoefficient_of_isTwistedPseudoCoefficient_refl
    {χ : Subgroup.center G →* ℂˣ} {π : Representation ℂ G V} {hπ : IsAdmissible π}
    {A : π.Equiv (π.comp (MulEquiv.refl G).toMonoidHom)} (hA : A.toLinearMap = LinearMap.id)
    {f : SchwartzBruhat G} (h : IsTwistedPseudoCoefficient μ (MulEquiv.refl G) χ π hπ A f) :
    IsPseudoCoefficient μ χ π hπ f := by
  obtain ⟨hχ, h1, h0⟩ := h
  refine ⟨hχ, ?_, ?_⟩
  · rw [hA] at h1
    rw [← twistedDistribution_one]
    exact h1
  · intro V' _ _ π' hπ' hirr htemp hχ' hne
    let A' : π'.Equiv (π'.comp (MulEquiv.refl G).toMonoidHom) :=
      Representation.Equiv.mk (LinearEquiv.refl ℂ V') (fun _ => rfl)
    rw [← twistedDistribution_one]
    exact h0 V' π' hπ' hirr htemp hχ' hne A'

end PseudoCoefficient

/-! ## The entrywise action on standard Levi subgroups -/

section LeviAlgebraic

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]

/-- The automorphism of the Levi product `∏ᵢ GL_{nᵢ}(E)` of `B` that applies `σ` to every
entry of every block. -/
def leviAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) : B.Levi E ≃* B.Levi E :=
  MulEquiv.piCongrRight fun i => entrywiseAut σ (B.size i)

@[simp]
theorem leviAut_apply (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) (m : B.Levi E)
    (i : Fin B.length) : leviAut σ B m i = entrywiseAut σ (B.size i) (m i) :=
  rfl

/-- The entrywise action of `σ` commutes with the block diagonal embedding. -/
theorem entrywiseAut_leviEmbedding (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (m : B.Levi E) :
    entrywiseAut σ n (B.leviEmbedding E m) = B.leviEmbedding E (leviAut σ B m) := by
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change σ (B.leviEmbedding E m (B.index i a) (B.index j b)) =
    B.leviEmbedding E (leviAut σ B m) (B.index i a) (B.index j b)
  by_cases hij : i = j
  · subst hij
    rw [BlockShape.leviEmbedding_apply_same, BlockShape.leviEmbedding_apply_same, leviAut_apply,
      entrywiseAut_apply_apply]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij,
      BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij, map_zero]

/-- The standard parabolic subgroup is stable under the entrywise action of `σ`. -/
theorem entrywiseAut_mem_parabolic_iff (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (g : GeneralLinear n E) :
    entrywiseAut σ n g ∈ B.parabolic E ↔ g ∈ B.parabolic E := by
  simp only [BlockShape.mem_parabolic_iff, entrywiseAut_apply_apply,
    EmbeddingLike.map_eq_zero_iff]

/-- The Levi projection intertwines the entrywise actions of `σ` on the parabolic and on the
Levi product. -/
theorem leviProjection_entrywiseAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (p : B.parabolic E) :
    B.leviProjection E ⟨entrywiseAut σ n p, (entrywiseAut_mem_parabolic_iff σ B p).2 p.2⟩ =
      leviAut σ B (B.leviProjection E p) := by
  funext i
  ext a b
  rfl

/-- `Ξ ≅ Ξ^σ` for a representation `Ξ` of the Levi product of `B`, where
`Ξ^σ(m) = Ξ(leviAut σ B m)`. -/
def IsLeviSigmaStable (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) {X : Type uX}
    [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X) : Prop :=
  Nonempty (Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))

end LeviAlgebraic

/-! ## σ-discrete series -/

section SigmaDiscrete

variable {F : Type u} [CommRing F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]

/-- `τ` is a σ-discrete series representation of `GL_n(E)` (Arthur–Clozel, Chapter 1, §2.3;
Henniart–Lemaire, II.4.6 and II.1.7): it is admissible, irreducible, tempered and σ-stable,
and it is not isomorphic to the unnormalized smooth induction, from the standard upper block
parabolic of any block shape with at least two blocks, of a smooth σ-stable representation of
the Levi product (carrier in the universe of `W`). -/
def IsSigmaDiscreteSeries (σ : E ≃ₐ[F] E) (n : ℕ) {W : Type uW} [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (GeneralLinear n E) W) : Prop :=
  IsAdmissible τ ∧ τ.IsIrreducible ∧ IsTemperedRep τ ∧ IsSigmaStable σ n τ ∧
    ∀ B : BlockShape n, 2 ≤ B.length →
      ∀ (X : Type uW) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
        IsSmooth Ξ → IsLeviSigmaStable σ B Ξ →
          IsEmpty (τ.Equiv
            (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))

omit [TopologicalSpace E] [IsTopologicalRing E] in
/-- Every element of `GL_1(E)` is central. -/
private theorem generalLinear_one_mem_center (g : GeneralLinear 1 E) :
    g ∈ Subgroup.center (GeneralLinear 1 E) := by
  rw [Subgroup.mem_center_iff]
  intro h
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

omit [TopologicalSpace E] [IsTopologicalRing E] in
private theorem subsingleton_generalLinear_one_quotient :
    Subsingleton (GeneralLinear 1 E ⧸ Subgroup.center (GeneralLinear 1 E)) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b => exact QuotientGroup.eq.mpr (generalLinear_one_mem_center _)

/-- The trivial representation of `GL_1(E)` on `ℂ` is a σ-discrete series representation:
`GL_1(E)` is commutative, so its central quotient is a point, and no block shape of `1` has
two blocks. -/
theorem isSigmaDiscreteSeries_trivial (σ : E ≃ₐ[F] E) :
    IsSigmaDiscreteSeries σ 1 (Representation.trivial ℂ (GeneralLinear 1 E) ℂ) := by
  have hsmooth : IsSmooth (Representation.trivial ℂ (GeneralLinear 1 E) ℂ) :=
    fun _ => ⟨⊤, fun _ => rfl⟩
  have hadm : IsAdmissible (Representation.trivial ℂ (GeneralLinear 1 E) ℂ) :=
    ⟨hsmooth, fun _ => inferInstance⟩
  refine ⟨hadm, ?_, ?_, ?_, ?_⟩
  · refine
      { exists_pair_ne := ⟨⊥, ⊤, fun h => bot_ne_top
          (congrArg _root_.Subrepresentation.toSubmodule h)⟩
        eq_bot_or_eq_top := fun S => ?_ }
    rcases eq_bot_or_eq_top S.toSubmodule with hS | hS
    · exact Or.inl (_root_.Subrepresentation.toSubmodule_injective hS)
    · exact Or.inr (_root_.Subrepresentation.toSubmodule_injective hS)
  · intro μ _
    have := subsingleton_generalLinear_one_quotient (E := E)
    let c : UnitaryCentralCharacter (Representation.trivial ℂ (GeneralLinear 1 E) ℂ) :=
      { character := 1
        isOpen_ker := by simp
        norm_eq_one := fun _ => by simp
        acts := fun _ _ => by simp }
    refine ⟨hadm, c, fun ℓ v ε _ => ?_⟩
    have hc : c.coefficientNorm ℓ v = fun _ => c.coefficientNorm ℓ v 1 :=
      funext fun x => congrArg _ (Subsingleton.elim x 1)
    rw [hc]
    exact memLp_const _
  · exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ ℂ) (fun _ => rfl)⟩
  · intro B hB
    have := B.length_le
    omega

end SigmaDiscrete

/-! ## Haar measures on the central quotient of `GL_n(E)` -/

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E] (n : ℕ)

include F in
/-- For a finite commutative algebra `E` over a nonarchimedean local field, the central
quotient of `GL_n(E)` carries a Haar measure (for its Borel σ-algebra), so `IsTemperedRep`
is not vacuous for `GL_n(E)`. -/
theorem exists_isHaarMeasure_centralQuotient_of_finite :
    letI : MeasurableSpace (GeneralLinear n E ⧸ Subgroup.center (GeneralLinear n E)) := borel _
    ∃ μ : Measure (GeneralLinear n E ⧸ Subgroup.center (GeneralLinear n E)),
      μ.IsHaarMeasure := by
  have := generalLinear_locallyCompactSpace_of_finite F E n
  let _ : MeasurableSpace (GeneralLinear n E ⧸ Subgroup.center (GeneralLinear n E)) := borel _
  have _ : BorelSpace (GeneralLinear n E ⧸ Subgroup.center (GeneralLinear n E)) := ⟨rfl⟩
  exact ⟨Measure.haarMeasure (Classical.arbitrary _), inferInstance⟩

end LocalField

end Langlands.BaseChange
