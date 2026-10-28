import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Parabolic.NaturalJacquetDualityProof
import Langlands.Representation.Category.Contragredient
import Langlands.Group.GL.ReverseBlocks

/-! # Supercuspidality and admissible irreducibility of the smooth contragredient -/

noncomputable section

namespace Langlands

universe uF uV

namespace GeneralLinear

/-- Vanishing of the opposite Jacquet quotient of an admissible representation
implies vanishing of the upper Jacquet quotient of its smooth contragredient. -/
theorem jacquet_vanishing_smoothContragredient_of_opposite
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsAdmissible ρ →
      Subsingleton (Jacquet.Coinvariants ρ (B.oppositeUnipotentSubgroup F.Carrier)) →
      Subsingleton (Jacquet.Coinvariants (smoothContragredient ρ)
        (B.unipotentSubgroup F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  intro ρ hadm hvan
  let : Subsingleton (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of ρ)) := hvan
  obtain ⟨E, _⟩ := Parabolic.standardNaturalJacquetDuality p F T n B
  let e := E (Rep.of ρ) hadm
  let q := B.jacquetModuleEquiv (smoothContragredient ρ)
  exact ⟨fun x y => q.symm.injective (e.injective (Subsingleton.elim _ _))⟩

/-- The smooth contragredient preserves supercuspidality in every rank. -/
theorem isSupercuspidal_smoothContragredient
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsSupercuspidal ρ → IsSupercuspidal (smoothContragredient ρ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hsc
  obtain ⟨hadm, hvan⟩ := (isSupercuspidal_iff_standard ρ).mp hsc
  apply (isSupercuspidal_iff_standard _).mpr
  refine ⟨isAdmissible_smoothContragredient_of_compact_cofinal
    (compactOpen_cofinal F T n) ρ hadm, fun B hB => ?_⟩
  have hreverse := hvan B.reverse ((B.reverse_parabolic_ne_top_iff F.Carrier).mpr hB)
  have hopposite :=
    (Jacquet.coinvariants_conj_subsingleton_iff ρ
      (B.reverse.unipotentSubgroup F.Carrier) (B.reverseMatrix F.Carrier)).mpr hreverse
  rw [B.reverse_unipotentSubgroup_map_conj F.Carrier] at hopposite
  exact jacquet_vanishing_smoothContragredient_of_opposite F T B V ρ hadm hopposite

/-- The smooth contragredient preserves and reflects supercuspidality, and
preserves and reflects irreducibility of admissible representations. -/
theorem supercuspidalContragredient :
    SupercuspidalContragredientStatement.{uF,uV} := by
  intro p hp F T n
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ
  have hcofinal := compactOpen_cofinal F T n
  have hd : ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W],
      (∀ (σ : Representation ℂ (GeneralLinear n F.Carrier) W) (hσ : IsSmooth σ),
        Function.Injective (smoothBidual hσ)) ∧
      (∀ (σ : Representation ℂ (GeneralLinear n F.Carrier) W) (hσ : IsAdmissible σ),
        IsAdmissible (smoothContragredient σ) ∧
          Function.Bijective (smoothBidual hσ.1)) :=
    fun W _ _ => smoothAdmissibleDuality (G := GeneralLinear n F.Carrier)
      (V := W) hcofinal
  constructor
  · constructor
    · intro hsc
      have hadm : IsAdmissible ρ :=
        isAdmissible_of_smoothContragredient hcofinal ρ hρ hsc.1
      let e := (smoothBidual hρ).ofBijective ((hd V).2 ρ hadm).2
      exact (isSupercuspidal_iff_of_equiv e).mpr
        (isSupercuspidal_smoothContragredient F T n (SmoothDual ρ)
          (smoothContragredient ρ) hsc)
    · exact isSupercuspidal_smoothContragredient F T n V ρ
  · intro hadm
    exact isIrreducible_smoothContragredient_iff_of_bidual
      (fun W _ _ => (hd W).1) ρ hρ ((hd V).2 ρ hadm).2

end GeneralLinear
end Langlands
