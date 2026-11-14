import Langlands.AllFieldBZ.Representation.Category.Contragredient
import Langlands.AllFieldBZ.Representation.Parabolic.NaturalJacquetDualityProof
import Langlands.Representation.Classification.SupercuspidalContragredientProof

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalContragredientProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalContragredientProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ
universe uF uV

namespace GeneralLinear
open Langlands.GeneralLinear
/-- Vanishing of the opposite Jacquet quotient of an admissible representation
implies vanishing of the upper Jacquet quotient of its smooth contragredient. -/
theorem _root_.Langlands.GeneralLinear.jacquet_vanishing_smoothContragredient_of_opposite_allFieldBZ
    (F : Langlands.AllFieldBZ.LocalFieldPackage.{uF})
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
  let : Subsingleton (Langlands.AllFieldBZ.CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of ρ)) := hvan
  obtain ⟨E, _⟩ := Langlands.AllFieldBZ.Parabolic.standardNaturalJacquetDuality F T n B
  let e := E (Rep.of ρ) hadm
  let q := B.jacquetModuleEquiv (smoothContragredient ρ)
  exact ⟨fun x y => q.symm.injective (e.injective (Subsingleton.elim _ _))⟩

/-- The smooth contragredient preserves supercuspidality in every rank. -/
theorem _root_.Langlands.GeneralLinear.isSupercuspidal_smoothContragredient_allFieldBZ
    (F : Langlands.AllFieldBZ.LocalFieldPackage.{uF})
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
    (Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T n) ρ hadm, fun B hB => ?_⟩
  have hreverse := hvan B.reverse ((B.reverse_parabolic_ne_top_iff F.Carrier).mpr hB)
  have hopposite :=
    (Jacquet.coinvariants_conj_subsingleton_iff ρ
      (B.reverse.unipotentSubgroup F.Carrier) (B.reverseMatrix F.Carrier)).mpr hreverse
  rw [B.reverse_unipotentSubgroup_map_conj F.Carrier] at hopposite
  exact Langlands.GeneralLinear.jacquet_vanishing_smoothContragredient_of_opposite_allFieldBZ F T B V ρ hadm hopposite

/-- The smooth contragredient preserves and reflects supercuspidality, and
preserves and reflects irreducibility of admissible representations. -/
theorem _root_.Langlands.GeneralLinear.supercuspidalContragredient_allFieldBZ :
    Langlands.GeneralLinear.SupercuspidalContragredientStatement_allFieldBZ.{uF,uV} := by
  intro F T n
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ
  have hcofinal := Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T n
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
        (Langlands.GeneralLinear.isSupercuspidal_smoothContragredient_allFieldBZ F T n (SmoothDual ρ)
          (smoothContragredient ρ) hsc)
    · exact Langlands.GeneralLinear.isSupercuspidal_smoothContragredient_allFieldBZ F T n V ρ
  · intro hadm
    exact isIrreducible_smoothContragredient_iff_of_bidual
      (fun W _ _ => (hd W).1) ρ hρ ((hd V).2 ρ hadm).2

end GeneralLinear
end Langlands.AllFieldBZ
