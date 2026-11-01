import Langlands.Representation.CuspidalSupport.UniformTripleTransferStatement

/-! Actual representative transport for the isolated uniform triple input. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual isomorphisms in each slot give an isomorphism of the actual uniform
triple tensor, with no replacement of the ambient Jacquet module. -/
def uniformTripleTensorIso {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ {A B C A' B' C' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear d F.Carrier)}
      (_eA : A ≅ A') (_eB : B ≅ B') (_eC : C ≅ C'),
      uniformTripleTensor F T hd A B C ≅ uniformTripleTensor F T hd A' B' C' := by
  let := T.topology
  intro A B C A' B' C' eA eB eC
  exact FiniteTensor.externalFunctor.mapIso
    (Pi.isoMk (Fin.cases eA (Fin.cases eB (Fin.cases eC finZeroElim))))

/-- Actual subquotient occurrences are invariant under slotwise smooth
isomorphisms of the three factors. -/
theorem uniformTripleOccurrence_iff_of_isos {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    ∀ {A B C A' B' C' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear d F.Carrier)}
      (_eA : A ≅ A') (_eB : B ≅ B') (_eC : C ≅ C')
      (Q : SmoothRep.{0, uF, uV} ℂ ((threeBlocks d d d hd hd hd).Levi F.Carrier)),
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd A B C) Q ↔
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd A' B' C') Q := by
  let := T.topology
  intro A B C A' B' C' eA eB eC Q
  let e := uniformTripleTensorIso F T hd eA eB eC
  constructor
  · rintro ⟨S, U, ⟨h⟩⟩
    exact ⟨S, U, ⟨e.symm ≪≫ h⟩⟩
  · rintro ⟨S, U, ⟨h⟩⟩
    exact ⟨S, U, ⟨e ≪≫ h⟩⟩

/-- The local input with literally repeated representatives, while retaining
the class relation between the upper and lower supercuspidals. -/
def RepeatedTripleSeedTransfer : Prop :=
  letI := T.topology
  ∀ (d : ℕ) (hd : 0 < d)
    (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (d + (d + d)) F.Carrier))
    (A B : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d)),
    E.IsIrreducible → E.IsAdmissible → E.HasFiniteLength →
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    (SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj B.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd B.obj A.obj B.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E)) ∧
    (SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj A.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj A.obj B.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) ∨
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd B.obj A.obj A.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E))

/-- Literal repetition suffices: class equalities give actual smooth
isomorphisms, which are tensored slotwise before and after the seed move. -/
theorem uniformRepeatedTripleTransfer_of_seed
    (H : RepeatedTripleSeedTransfer.{uF, uV} F T) :
    UniformRepeatedCuspidalTripleJacquetTransfer.{uF, uV} F T := by
  let := T.topology
  intro d hd E A B C hEi hEa hEf hOcc hAB
  have hSeed := H d hd E A B hEi hEa hEf hAB
  constructor
  · intro hCB
    obtain ⟨eCB⟩ := (SupercuspidalRep.isoClass_eq_iff C B).mp hCB
    let e : C.obj ≅ B.obj :=
      (supercuspidalProperty (F := F.Carrier) (n := d)).ι.mapIso eCB
    have hSeedOcc := (uniformTripleOccurrence_iff_of_isos F T hd
      (Iso.refl A.obj) (Iso.refl B.obj) e _).mp hOcc
    exact (uniformTripleOccurrence_iff_of_isos F T hd
      (Iso.refl B.obj) (Iso.refl A.obj) e.symm _).mp (hSeed.1 hSeedOcc)
  · intro hCA
    obtain ⟨eCA⟩ := (SupercuspidalRep.isoClass_eq_iff C A).mp hCA
    let e : C.obj ≅ A.obj :=
      (supercuspidalProperty (F := F.Carrier) (n := d)).ι.mapIso eCA
    have hSeedOcc := (uniformTripleOccurrence_iff_of_isos F T hd
      (Iso.refl A.obj) (Iso.refl B.obj) e _).mp hOcc
    rcases hSeed.2 hSeedOcc with haa | hba
    · exact Or.inl ((uniformTripleOccurrence_iff_of_isos F T hd
        (Iso.refl A.obj) e.symm (Iso.refl B.obj) _).mp haa)
    · exact Or.inr ((uniformTripleOccurrence_iff_of_isos F T hd
        (Iso.refl B.obj) (Iso.refl A.obj) e.symm _).mp hba)

/-- The actual supercuspidal twist `ν B` for the supplied topological data. -/
def nuSupercuspidal {d : ℕ} :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d) →
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d) :=
  letI := T.topology
  SupercuspidalRep.twist (T.determinantPowerCharacter d 1)
    (T.isOpen_ker_determinantPowerCharacter d 1)
    (T.ker_determinant_le_ker_determinantPowerCharacter d 1)

/-- Its isomorphism class is the published normalized determinant twist. -/
theorem nuSupercuspidal_isoClass {d : ℕ} :
    letI := T.topology
    ∀ B : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d),
      (nuSupercuspidal F T B).isoClass =
        T.supercuspidalClassRealPowerTwist d 1 B.isoClass := by
  let := T.topology
  intro B
  rfl

/-- The isolated seed obligation for the literal pairs `(νB,B,B)` and
`(νB,B,νB)`. No relation between different class representatives is a premise. -/
def CanonicalRepeatedTripleSeedTransfer : Prop :=
  letI := T.topology
  ∀ (d : ℕ) (hd : 0 < d)
    (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (d + (d + d)) F.Carrier))
    (B : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d)),
    E.IsIrreducible → E.IsAdmissible → E.HasFiniteLength →
    let A := nuSupercuspidal F T B
    (SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj B.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd B.obj A.obj B.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E)) ∧
    (SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj A.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj A.obj B.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) ∨
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd B.obj A.obj A.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E))

/-- Equality with the twist class provides an actual isomorphism to the
canonical twist, so the canonical seeds imply the literal-repetition seeds. -/
theorem repeatedTripleSeedTransfer_of_canonical
    (H : CanonicalRepeatedTripleSeedTransfer.{uF, uV} F T) :
    RepeatedTripleSeedTransfer.{uF, uV} F T := by
  let := T.topology
  intro d hd E A B hEi hEa hEf hAB
  obtain ⟨eA⟩ := (SupercuspidalRep.isoClass_eq_iff A (nuSupercuspidal F T B)).mp hAB
  let e : A.obj ≅ (nuSupercuspidal F T B).obj :=
    (supercuspidalProperty (F := F.Carrier) (n := d)).ι.mapIso eA
  have hSeed := H d hd E B hEi hEa hEf
  constructor
  · intro hOcc
    have hSeedOcc := (uniformTripleOccurrence_iff_of_isos F T hd
      e (Iso.refl B.obj) (Iso.refl B.obj) _).mp hOcc
    exact (uniformTripleOccurrence_iff_of_isos F T hd
      (Iso.refl B.obj) e.symm (Iso.refl B.obj) _).mp (hSeed.1 hSeedOcc)
  · intro hOcc
    have hSeedOcc := (uniformTripleOccurrence_iff_of_isos F T hd
      e (Iso.refl B.obj) e _).mp hOcc
    rcases hSeed.2 hSeedOcc with haa | hba
    · exact Or.inl ((uniformTripleOccurrence_iff_of_isos F T hd
        e.symm e.symm (Iso.refl B.obj) _).mp haa)
    · exact Or.inr ((uniformTripleOccurrence_iff_of_isos F T hd
        (Iso.refl B.obj) e.symm e.symm _).mp hba)

/-- The canonical seed obligation is exactly equivalent to the uniform
local transfer proposition, including arbitrary supplied representatives. -/
theorem uniformRepeatedTripleTransfer_iff_canonical :
    UniformRepeatedCuspidalTripleJacquetTransfer.{uF, uV} F T ↔
      CanonicalRepeatedTripleSeedTransfer.{uF, uV} F T := by
  let := T.topology
  constructor
  · intro H d hd E B hEi hEa hEf
    constructor
    · intro hOcc
      exact (H d hd E (nuSupercuspidal F T B) B B hEi hEa hEf hOcc rfl).1 rfl
    · intro hOcc
      exact (H d hd E (nuSupercuspidal F T B) B (nuSupercuspidal F T B)
        hEi hEa hEf hOcc rfl).2 rfl
  · intro H
    exact uniformRepeatedTripleTransfer_of_seed F T (repeatedTripleSeedTransfer_of_canonical F T H)

end Langlands.CuspidalSupport
