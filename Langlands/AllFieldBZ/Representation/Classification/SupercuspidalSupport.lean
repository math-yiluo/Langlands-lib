import Langlands.AllFieldBZ.Representation.Classification.Segments
import Langlands.Representation.Classification.SupercuspidalSupport

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalSupport`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalSupport` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uR uG uV uF

namespace SmoothRep
open Langlands.SmoothRep
variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]

end SmoothRep
namespace LocalFieldPackage.TopologicalData
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The ordered block shape `(r_1, …, r_k)` of a finite family of cuspidal data of
ranks `r_i`, for any `n` equal to the sum of the ranks. -/
def cuspidalShape {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n) : GeneralLinear.BlockShape n where
  length := k
  size i := (ρ i).rank
  positive i := (ρ i).rank_pos
  sum_eq := h

@[simp]
theorem cuspidalShape_length {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n) : (T.cuspidalShape ρ h).length = k := rfl

@[simp]
theorem cuspidalShape_size {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n) (i : Fin k) : (T.cuspidalShape ρ h).size i = (ρ i).rank :=
  rfl

/-- `A_1 × ⋯ × A_k`: normalized parabolic induction, from the standard upper block
parabolic of shape `(r_1, …, r_k)`, of supercuspidal representations `A_i` of
`GL_(r_i)(F)`. -/
def cuspidalProductInduced {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).obj fun i => (A i).obj

/-- Representatives of the same cuspidal data induce isomorphic representations. -/
def cuspidalProductInducedIsoOfRepresented {k : ℕ} {ρ : Fin k → CuspidalDatum.{uV, uF} T}
    {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    {A A' : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)}
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) (hA' : ∀ i, (ρ i).IsRepresentedBy (A' i)) :
    T.cuspidalProductInduced ρ h A ≅ T.cuspidalProductInduced ρ h A' :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).mapIso
    (Pi.isoMk fun i =>
      (GeneralLinear.supercuspidalProperty (F := F.Carrier) (n := (ρ i).rank)).ι.mapIso
        (Classical.choice
          ((GeneralLinear.SupercuspidalRep.isoClass_eq_iff (A i) (A' i)).mp
            ((hA i).trans (hA' i).symm))))

variable {T}

/-- `π` is an irreducible subquotient of `ρ_1 × ⋯ × ρ_k` for actual supercuspidal
representatives of the cuspidal data `ρ_i`, whose ranks add up to `n`. This is
Zelevinsky's `ω ∈ JH(ρ_1 × ⋯ × ρ_k)`. -/
def IsCuspidalConstituent {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  ∃ (h : ∑ i, (ρ i).rank = n)
    (A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) ∧ π.IsIrreducible ∧
      SmoothRep.IsSubquotient π (T.cuspidalProductInduced ρ h A)

/-- `π` is an irreducible subrepresentation of `ρ_1 × ⋯ × ρ_k` for actual
supercuspidal representatives of the cuspidal data `ρ_i`, in the given order. -/
def IsCuspidalSubrepresentation {k : ℕ} (ρ : Fin k → CuspidalDatum.{uV, uF} T) {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  ∃ (h : ∑ i, (ρ i).rank = n)
    (A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) ∧
      Classification.IsIrreducibleSubrepresentation
        (T.cuspidalProductInduced ρ h A).representation π.representation

/-- An irreducible subrepresentation of `ρ_1 × ⋯ × ρ_k` is an irreducible
subquotient of it. -/
theorem IsCuspidalSubrepresentation.isCuspidalConstituent {k : ℕ}
    {ρ : Fin k → CuspidalDatum.{uV, uF} T} {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hs : T.IsCuspidalSubrepresentation ρ π) : T.IsCuspidalConstituent ρ π := by
  let := T.topology
  obtain ⟨h, A, hA, hπ, j, hj⟩ := hs
  exact ⟨h, A, hA, hπ,
    SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom j, hj⟩⟩

/-- `s` is a supercuspidal support of `π`: some ordering `ρ_1, …, ρ_k` of the multiset
`s` of cuspidal data has `π` as an irreducible subquotient of `ρ_1 × ⋯ × ρ_k`
(Zelevinsky 1980, 1.10). -/
def IsSupercuspidalSupport {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T)) : Prop :=
  ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T),
    (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) = s ∧ T.IsCuspidalConstituent ρ π

end LocalFieldPackage.TopologicalData
end Langlands.AllFieldBZ
