import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.Segments

/-!
# All-field port of `Langlands.Representation.Classification.Segments`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.Segments` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uG uV uW uF

namespace Classification
open Langlands.Classification
variable {G : Type uG} [Group G]
variable {V V' W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]

end Classification
namespace GeneralLinear
open Langlands.GeneralLinear
variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

end GeneralLinear
namespace LocalFieldPackage.TopologicalData
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

theorem supercuspidalClassRealPowerTwist_zero (n : ℕ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
    T.supercuspidalClassRealPowerTwist n 0 a = a := by
  let := T.topology
  have h1 : IsOpen ((1 : GeneralLinear n F.Carrier →* ℂˣ).ker :
      Set (GeneralLinear n F.Carrier)) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  unfold supercuspidalClassRealPowerTwist
  rw [GeneralLinear.SupercuspidalClass.twist_congr (realPowerCharacter_zero _) _ h1 _
    GeneralLinear.ker_determinant_le_ker_one]
  exact GeneralLinear.SupercuspidalClass.twist_one h1 a

theorem supercuspidalClassRealPowerTwist_add (n : ℕ) (s t : ℝ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
    T.supercuspidalClassRealPowerTwist n s (T.supercuspidalClassRealPowerTwist n t a) =
      T.supercuspidalClassRealPowerTwist n (s + t) a := by
  let := T.topology
  have hst : IsOpen ((T.determinantPowerCharacter n s * T.determinantPowerCharacter n t).ker :
      Set (GeneralLinear n F.Carrier)) := by
    rw [← realPowerCharacter_add]
    exact T.isOpen_ker_determinantPowerCharacter n (s + t)
  unfold supercuspidalClassRealPowerTwist
  rw [GeneralLinear.SupercuspidalClass.twist_twist _ _ _ _ hst]
  exact GeneralLinear.SupercuspidalClass.twist_congr (realPowerCharacter_add _ s t).symm _ _ _ _ a

/-- An element of Zelevinsky's set `𝒞`: the isomorphism class of an irreducible
supercuspidal representation of `GL_r(F)` for some `r ≥ 1`, with carriers in
`Type uV`. -/
structure CuspidalDatum where
  /-- The size `r` of the general linear group. -/
  rank : ℕ
  rank_pos : 0 < rank
  /-- The supercuspidal isomorphism class. -/
  cls : letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := rank)

namespace CuspidalDatum
variable {T}

/-- Zelevinsky's twist `ρ ↦ ν^s ρ`, with `ν = |det|` for the residue-normalized
absolute value. -/
def twist (s : ℝ) (ρ : CuspidalDatum.{uV, uF} T) : CuspidalDatum.{uV, uF} T where
  rank := ρ.rank
  rank_pos := ρ.rank_pos
  cls := T.supercuspidalClassRealPowerTwist ρ.rank s ρ.cls

@[simp]
theorem twist_rank (s : ℝ) (ρ : CuspidalDatum.{uV, uF} T) : (ρ.twist s).rank = ρ.rank := rfl

@[simp]
theorem twist_zero (ρ : CuspidalDatum.{uV, uF} T) : ρ.twist 0 = ρ := by
  obtain ⟨r, hr, a⟩ := ρ
  simp only [twist, mk.injEq, heq_eq_eq, true_and]
  exact T.supercuspidalClassRealPowerTwist_zero r a

theorem twist_twist (s t : ℝ) (ρ : CuspidalDatum.{uV, uF} T) :
    (ρ.twist t).twist s = ρ.twist (s + t) := by
  obtain ⟨r, hr, a⟩ := ρ
  exact congrArg (CuspidalDatum.mk r hr) (T.supercuspidalClassRealPowerTwist_add r s t a)

end CuspidalDatum
/-- Zelevinsky's segment `[ρ, ν^(m-1) ρ] = {ρ, νρ, …, ν^(m-1) ρ}`, recorded by its
beginning `ρ` and its number `m ≥ 1` of elements. -/
structure Segment where
  /-- The beginning `ρ` of the segment. -/
  base : CuspidalDatum.{uV, uF} T
  /-- The number `m` of elements of the segment. -/
  length : ℕ
  length_pos : 0 < length

namespace Segment
variable {T}

/-- The common rank `r` of the supercuspidal classes in the segment. -/
abbrev rank (Δ : Segment.{uV, uF} T) : ℕ := Δ.base.rank

theorem rank_pos (Δ : Segment.{uV, uF} T) : 0 < Δ.rank := Δ.base.rank_pos

/-- The element `ν^i ρ`. -/
def member (Δ : Segment.{uV, uF} T) (i : ℕ) : CuspidalDatum.{uV, uF} T :=
  Δ.base.twist (i : ℝ)

@[simp]
theorem member_zero (Δ : Segment.{uV, uF} T) : Δ.member 0 = Δ.base := by
  simp [member]

/-- The end `ν^(m-1) ρ` of the segment. -/
def last (Δ : Segment.{uV, uF} T) : CuspidalDatum.{uV, uF} T :=
  Δ.member (Δ.length - 1)

/-- The twisted segment `ν^s Δ = [ν^s ρ, ν^(s+m-1) ρ]`. -/
def twist (s : ℝ) (Δ : Segment.{uV, uF} T) : Segment.{uV, uF} T where
  base := Δ.base.twist s
  length := Δ.length
  length_pos := Δ.length_pos

@[simp]
theorem twist_length (s : ℝ) (Δ : Segment.{uV, uF} T) : (Δ.twist s).length = Δ.length := rfl

@[simp]
theorem twist_rank (s : ℝ) (Δ : Segment.{uV, uF} T) : (Δ.twist s).rank = Δ.rank := rfl

@[simp]
theorem twist_zero (Δ : Segment.{uV, uF} T) : Δ.twist 0 = Δ := by
  simp [twist]

theorem twist_twist (s t : ℝ) (Δ : Segment.{uV, uF} T) :
    (Δ.twist t).twist s = Δ.twist (s + t) := by
  simp [twist, CuspidalDatum.twist_twist]

end Segment
namespace Multisegment
variable {T}

end Multisegment
section Induced
variable {r : ℕ}

end Induced
variable {T} in
/-- The actual supercuspidal representatives of a cuspidal datum. -/
def CuspidalDatum.IsRepresentedBy (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)) : Prop :=
  letI := T.topology
  A.isoClass = ρ.cls

end LocalFieldPackage.TopologicalData
end Langlands.AllFieldBZ
