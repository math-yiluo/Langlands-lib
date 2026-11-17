import Langlands.LocalFactor.ArchimedeanPairFactor

/-! # Restriction of real Weil block data to complex Weil block data

These are operations on the published actual character data and finite block lists.
The equations record the norm pullback and the two inducing characters; no global
base-change compatibility or isomorphism of sum models is asserted.
-/

noncomputable section

namespace Langlands.LocalFactor.Archimedean

/-- The real character pulled back along the complex norm, in the complex polar convention. -/
def RealCharacterData.complexRestriction (c : RealCharacterData) : ComplexCharacterData where
  character := c.character.comp Langlands.Weil.Archimedean.complexNorm
  weight := 0
  exponent := c.exponent
  character_eq z := by
    simpa [ComplexCharacterData.twistReal, ComplexCharacterData.trivial] using
      (ComplexCharacterData.trivial.twistReal c).character_eq z

@[simp]
theorem RealCharacterData.complexRestriction_character (c : RealCharacterData) :
    c.complexRestriction.character =
      c.character.comp Langlands.Weil.Archimedean.complexNorm := rfl

@[simp]
theorem RealCharacterData.complexRestriction_weight (c : RealCharacterData) :
    c.complexRestriction.weight = 0 := rfl

@[simp]
theorem RealCharacterData.complexRestriction_exponent (c : RealCharacterData) :
    c.complexRestriction.exponent = c.exponent := rfl

/-- Restriction of one real block: a norm pullback, or the two conjugate inducing data. -/
def RealBlock.restrictToComplex : RealBlock → List ComplexCharacterData
  | .character c => [c.complexRestriction]
  | .induced d => [d, d.conj]

@[simp]
theorem RealBlock.restrictToComplex_character (c : RealCharacterData) :
    (RealBlock.character c).restrictToComplex = [c.complexRestriction] := rfl

@[simp]
theorem RealBlock.restrictToComplex_induced (d : ComplexCharacterData) :
    (RealBlock.induced d).restrictToComplex = [d, d.conj] := rfl

/-- Restriction preserves the rank of a block as the number of complex characters. -/
@[simp]
theorem RealBlock.length_restrictToComplex (b : RealBlock) :
    b.restrictToComplex.length = b.rank := by
  cases b <;> rfl

/-- Restrict each real block and concatenate, retaining every block with its multiplicity. -/
def realParameterRestrictToComplex (ds : List RealBlock) : List ComplexCharacterData :=
  ds.flatMap RealBlock.restrictToComplex

@[simp]
theorem realParameterRestrictToComplex_nil : realParameterRestrictToComplex [] = [] := rfl

@[simp]
theorem realParameterRestrictToComplex_cons (b : RealBlock) (ds : List RealBlock) :
    realParameterRestrictToComplex (b :: ds) =
      b.restrictToComplex ++ realParameterRestrictToComplex ds := rfl

@[simp]
theorem realParameterRestrictToComplex_append (ds es : List RealBlock) :
    realParameterRestrictToComplex (ds ++ es) =
      realParameterRestrictToComplex ds ++ realParameterRestrictToComplex es :=
  List.flatMap_append

/-- The number of restricted complex blocks is the total rank of the real blocks. -/
@[simp]
theorem length_realParameterRestrictToComplex (ds : List RealBlock) :
    (realParameterRestrictToComplex ds).length = realRank ds := by
  induction ds with
  | nil => rfl
  | cons b ds ih =>
    rw [realParameterRestrictToComplex_cons, List.length_append,
      RealBlock.length_restrictToComplex, ih, realRank_cons]

/-- Reordering the real blocks reorders their restricted complex blocks. -/
theorem realParameterRestrictToComplex_perm {ds es : List RealBlock} (h : ds.Perm es) :
    (realParameterRestrictToComplex ds).Perm (realParameterRestrictToComplex es) :=
  h.flatMap_right RealBlock.restrictToComplex

end Langlands.LocalFactor.Archimedean
