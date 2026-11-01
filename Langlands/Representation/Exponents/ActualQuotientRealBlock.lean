import Langlands.Representation.Exponents.QuotientRealBlockRetraction
import Langlands.Representation.Exponents.TemperedCoarseRealBlock
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Twist.SubquotientProof

/-! Actual adjunction and quotient block retractions. -/

noncomputable section

namespace Langlands.ActualQuotientRealBlock

open GeneralLinear RelativeRegularComparison CuspidalJacquetMultiplicity

universe uF uV uW uX

/-- The actual normalized opposite Jacquet map on the bundled product Levi. -/
def oppositeMap
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n)
    {X : Rep.{uW} ℂ (GeneralLinear n F.Carrier)}
    {J : Rep.{uX} ℂ (GeneralLinear n F.Carrier)}
    (q : X.ρ.IntertwiningMap J.ρ) :
    (oppositeJacquet T B X).ρ.IntertwiningMap (oppositeJacquet T B J).ρ := by
  let δ := ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
  let f := Jacquet.normalizedMapOfModulus
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier) δ q
  exact {
    toLinearMap := f.toLinearMap
    isIntertwining' := fun m => f.isIntertwining' (B.leviEquiv F.Carrier m) }

/-- Surjectivity is proved on actual coinvariant representatives. -/
theorem oppositeMap_surjective
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n)
    {X : Rep.{uW} ℂ (GeneralLinear n F.Carrier)}
    {J : Rep.{uX} ℂ (GeneralLinear n F.Carrier)}
    (q : X.ρ.IntertwiningMap J.ρ) (hq : Function.Surjective q) :
    Function.Surjective (oppositeMap T B q) := by
  intro y
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective J.ρ
    (B.oppositeUnipotentSubgroup F.Carrier) y
  obtain ⟨v, rfl⟩ := hq w
  exact ⟨Jacquet.mk X.ρ (B.oppositeUnipotentSubgroup F.Carrier) v, rfl⟩

/-- An actual nonzero outer quotient supplies a nonzero adjunction map.
The finite-central and isolation inputs are not used here. -/
theorem nonzeroAdjunctionMap
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (α : Rep.{uV} ℂ (B.Levi F.Carrier))
    (J : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
    (hJ : Nontrivial J.V)
    (q : (induced T B α).ρ.IntertwiningMap J.ρ) (hq : Function.Surjective q) :
    letI := T.topology
    IsAdmissible α.ρ → IsAdmissible J.ρ →
    ∃ g : α.ρ.IntertwiningMap (oppositeJacquet T B J).ρ, g ≠ 0 := by
  let := T.topology
  let := hJ
  intro hα hJadm
  obtain ⟨E, _⟩ :=
    Parabolic.normalizedSecondAdjointness.{uF,uV,uW}.1 p F T n hn B
  have hqne : q ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := exists_ne (0 : J.V)
    obtain ⟨v, hv⟩ := hq w
    rw [hz] at hv
    exact hw hv.symm
  refine ⟨E α J hα hJadm q, ?_⟩
  intro hz
  apply hqne
  apply (E α J hα hJadm).injective
  exact hz.trans (E α J hα hJadm).map_zero.symm

/-- Actual quotient extraction, conditional only at the finite central
actions and the whole-induction per-character projector. -/
theorem quotientRetraction
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (π : Rep.{uV} ℂ (B.Levi F.Carrier))
    (hπirr : Representation.IsIrreducible π.ρ)
    (hπtemp : IsLeviTempered T B π) (t : Fin B.length → ℝ) :
    letI := T.topology
    let α := Rep.of (T.leviRealPowerTwist B t π.ρ)
    let X := induced T B α
    let E := oppositeJacquet T B X
    ∀ (J : Rep.{uW} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible J.ρ →
      ∀ (q : X.ρ.IntertwiningMap J.ρ), Function.Surjective q →
      let N := oppositeJacquet T B J
      Module.Finite ℂ (Submodule.span ℂ
        (Set.range (fun z : Subgroup.center (B.Levi F.Carrier) => E.ρ (z : B.Levi F.Carrier)))) →
      Module.Finite ℂ (Submodule.span ℂ
        (Set.range (fun z : Subgroup.center (B.Levi F.Carrier) => N.ρ (z : B.Levi F.Carrier)))) →
      ∀ (i : α.ρ.IntertwiningMap E.ρ) (r : E.ρ.IntertwiningMap α.ρ),
        (∀ (χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ),
          IsOpen (χ.ker : Set (Subgroup.center (B.Levi F.Carrier))) →
          T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
            (fun k => (B.size k : ℝ) * t k) →
          ∀ v : E, v ∈ generalizedCentralCharacterSpace E.ρ χ → i (r v) = v) →
        ∃ rQ : N.ρ.IntertwiningMap α.ρ,
          (∀ a : α, rQ (oppositeMap T B q (i a)) = a) ∧
          ∀ v : N, v ∈ T.realCentralBlock B N.ρ
            (fun k => (B.size k : ℝ) * t k) →
              oppositeMap T B q (i (rQ v)) = v := by
  let := T.topology
  dsimp only
  intro J hJirr q hq hE hN i r hfix
  let := hJirr
  have hJnt : Nontrivial J.V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) J.ρ.asModule
  have hadm := (relativeCosocleAdmissibility p F T n B π).2.2
    hπtemp.isAdmissible t
  obtain ⟨g, hg⟩ := nonzeroAdjunctionMap T hn B _ J hJnt q hq
    hadm.1 (hadm.2.2 J q hq)
  have hαirr : Representation.IsIrreducible (T.leviRealPowerTwist B t π.ρ) :=
    (isIrreducible_twist_iff _ π.ρ).mpr hπirr
  let P := fun χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ =>
    IsOpen (χ.ker : Set (Subgroup.center (B.Levi F.Carrier))) ∧
      T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
        (fun k => (B.size k : ℝ) * t k)
  have hgroup := QuotientRealBlockRetraction.projectorFixedOnGrouped
    P i r (fun χ hχ v hv => hfix χ hχ.1 hχ.2 v hv)
  exact QuotientRealBlockRetraction.quotientRetraction
    P hE hN (oppositeMap T B q) (oppositeMap_surjective T B q hq) i r hgroup
    hαirr (TemperedCoarseRealBlock.realBlockEqTop T B π hπtemp t) g hg

/-- Finite generation of the whole outer induction suffices for both
central-action inputs; irreducibility gives finite generation of the quotient. -/
theorem quotientRetractionOfFiniteGeneration
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (π : Rep.{uV} ℂ (B.Levi F.Carrier))
    (hπirr : Representation.IsIrreducible π.ρ)
    (hπtemp : IsLeviTempered T B π) (t : Fin B.length → ℝ) :
    letI := T.topology
    let α := Rep.of (T.leviRealPowerTwist B t π.ρ)
    let X := induced T B α
    let E := oppositeJacquet T B X
    Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) X.ρ.asModule →
    ∀ (J : Rep.{uW} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible J.ρ →
      ∀ (q : X.ρ.IntertwiningMap J.ρ), Function.Surjective q →
      let N := oppositeJacquet T B J
      ∀ (i : α.ρ.IntertwiningMap E.ρ) (r : E.ρ.IntertwiningMap α.ρ),
        (∀ (χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ),
          IsOpen (χ.ker : Set (Subgroup.center (B.Levi F.Carrier))) →
          T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
            (fun k => (B.size k : ℝ) * t k) →
          ∀ v : E, v ∈ generalizedCentralCharacterSpace E.ρ χ → i (r v) = v) →
        ∃ rQ : N.ρ.IntertwiningMap α.ρ,
          (∀ a : α, rQ (oppositeMap T B q (i a)) = a) ∧
          ∀ v : N, v ∈ T.realCentralBlock B N.ρ
            (fun k => (B.size k : ℝ) * t k) →
              oppositeMap T B q (i (rQ v)) = v := by
  let := T.topology
  dsimp only
  intro hfg J hJirr q hq i r hfix
  let := hJirr
  have hJfg : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      J.ρ.asModule := inferInstance
  have hadm := (relativeCosocleAdmissibility p F T n B π).2.2
    hπtemp.isAdmissible t
  exact quotientRetraction T hn B π hπirr hπtemp t J hJirr q hq
    (oppositeJacquetCentralAction
      T B _ hadm.2.1 hfg).1
    (oppositeJacquetCentralAction
      T B J (hadm.2.2 J q hq) hJfg).1 i r hfix

end Langlands.ActualQuotientRealBlock
