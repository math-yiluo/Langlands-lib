import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.SubrepresentationLattice

/-!
# Compact-coefficient isotypic subrepresentations and annihilators

For a class `c` of irreducible smooth complex representations with compact
smooth-dual coefficients and an actual smooth representation `A`, the
`c`-isotypic subrepresentation is the supremum of the ranges of all intertwiners
from representatives of `c` into `A`. The `c`-annihilator is the infimum of the
kernels of all intertwiners from `A` to representatives of `c`. These intrinsic
lattice objects correspond to Bernstein--Zelevinsky's (1976, §§2.43--2.44)
`E_ω` and `E_ω^⊥`. No complement, projector, splitting or finiteness is asserted.
The representative carrier universe `uV` and the ambient carrier universes are
independent.
-/

noncomputable section

namespace Langlands

namespace CompactCoefficientClass

universe uG uV uW uX

open Representation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The `c`-isotypic subrepresentation of `A`: the supremum of the ranges of all
actual intertwiners from representatives of `c`, with carriers in `Type uV`. -/
def isotypicSubrepresentation (c : CompactCoefficientClass.{uG, uV} G)
    (A : SmoothRep.{0, uG, uW} ℂ G) : Subrepresentation A.representation :=
  ⨆ (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (_ : ofRep D = c)
    (f : D.obj.representation.IntertwiningMap A.representation), f.range

/-- The `c`-annihilator subrepresentation of `A`: the infimum of the kernels of
all actual intertwiners to representatives of `c`, with carriers in `Type uV`. -/
def annihilatorSubrepresentation (c : CompactCoefficientClass.{uG, uV} G)
    (A : SmoothRep.{0, uG, uW} ℂ G) : Subrepresentation A.representation :=
  ⨅ (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (_ : ofRep D = c)
    (f : A.representation.IntertwiningMap D.obj.representation), f.ker

section Laws

variable {c : CompactCoefficientClass.{uG, uV} G} {A : SmoothRep.{0, uG, uW} ℂ G}

/-- Every intertwiner from a representative of `c` has range in the isotypic part. -/
theorem range_le_isotypicSubrepresentation
    (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (hD : ofRep D = c)
    (f : D.obj.representation.IntertwiningMap A.representation) :
    f.range ≤ isotypicSubrepresentation c A :=
  le_iSup₂_of_le D hD (le_iSup (fun f : D.obj.representation.IntertwiningMap
    A.representation => f.range) f)

/-- The isotypic part is the least subrepresentation containing all these ranges. -/
theorem isotypicSubrepresentation_le_iff (S : Subrepresentation A.representation) :
    isotypicSubrepresentation c A ≤ S ↔
      ∀ (D : IrreducibleCompactCoefficientRep.{uG, uV} G), ofRep D = c →
        ∀ f : D.obj.representation.IntertwiningMap A.representation, f.range ≤ S := by
  simp only [isotypicSubrepresentation, iSup_le_iff]

/-- The annihilator lies in the kernel of every intertwiner to a representative. -/
theorem annihilatorSubrepresentation_le_ker
    (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (hD : ofRep D = c)
    (f : A.representation.IntertwiningMap D.obj.representation) :
    annihilatorSubrepresentation c A ≤ f.ker :=
  iInf₂_le_of_le D hD (iInf_le (fun f : A.representation.IntertwiningMap
    D.obj.representation => f.ker) f)

/-- The annihilator is the greatest subrepresentation inside all these kernels. -/
theorem le_annihilatorSubrepresentation_iff (S : Subrepresentation A.representation) :
    S ≤ annihilatorSubrepresentation c A ↔
      ∀ (D : IrreducibleCompactCoefficientRep.{uG, uV} G), ofRep D = c →
        ∀ f : A.representation.IntertwiningMap D.obj.representation, S ≤ f.ker := by
  simp only [annihilatorSubrepresentation, le_iInf_iff]

/-- A vector lies in the annihilator exactly when every intertwiner to a
representative of `c` kills it. -/
theorem mem_annihilatorSubrepresentation_iff (v : A) :
    v ∈ annihilatorSubrepresentation c A ↔
      ∀ (D : IrreducibleCompactCoefficientRep.{uG, uV} G), ofRep D = c →
        ∀ f : A.representation.IntertwiningMap D.obj.representation, f v = 0 := by
  simp only [annihilatorSubrepresentation, Subrepresentation.mem_iInf]
  rfl

/-- The underlying submodule is the submodule supremum of the linear ranges. -/
theorem toSubmodule_isotypicSubrepresentation :
    (isotypicSubrepresentation c A).toSubmodule =
      ⨆ (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (_ : ofRep D = c)
        (f : D.obj.representation.IntertwiningMap A.representation),
          LinearMap.range f.toLinearMap := by
  simp only [isotypicSubrepresentation, Subrepresentation.toSubmodule_iSup]
  rfl

/-- The underlying submodule is the submodule infimum of the linear kernels. -/
theorem toSubmodule_annihilatorSubrepresentation :
    (annihilatorSubrepresentation c A).toSubmodule =
      ⨅ (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (_ : ofRep D = c)
        (f : A.representation.IntertwiningMap D.obj.representation),
          LinearMap.ker f.toLinearMap := by
  simp only [annihilatorSubrepresentation, Subrepresentation.toSubmodule_iInf]
  rfl

/-- Representative formula: one actual representative of `c` suffices. -/
theorem isotypicSubrepresentation_eq_iSup_range
    (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (hD : ofRep D = c) :
    isotypicSubrepresentation c A =
      ⨆ f : D.obj.representation.IntertwiningMap A.representation, f.range := by
  apply le_antisymm
  · refine (isotypicSubrepresentation_le_iff _).2 fun D' hD' f => ?_
    obtain ⟨e⟩ := (ofRep_eq_iff D' D).1 (hD'.trans hD.symm)
    let ε := SmoothRep.equivOfIso ((irreducibleCompactCoefficientProperty G).ι.mapIso e)
    refine le_trans ?_ (le_iSup (fun f : D.obj.representation.IntertwiningMap
      A.representation => f.range) (f.comp ε.symm.toIntertwiningMap))
    rintro _ ⟨v, rfl⟩
    exact ⟨ε v, by simp⟩
  · exact iSup_le fun f => range_le_isotypicSubrepresentation D hD f

/-- Representative formula: one actual representative of `c` suffices. -/
theorem annihilatorSubrepresentation_eq_iInf_ker
    (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (hD : ofRep D = c) :
    annihilatorSubrepresentation c A =
      ⨅ f : A.representation.IntertwiningMap D.obj.representation, f.ker := by
  apply le_antisymm
  · exact le_iInf fun f => annihilatorSubrepresentation_le_ker D hD f
  · refine (le_annihilatorSubrepresentation_iff _).2 fun D' hD' f => ?_
    obtain ⟨e⟩ := (ofRep_eq_iff D' D).1 (hD'.trans hD.symm)
    let ε := SmoothRep.equivOfIso ((irreducibleCompactCoefficientProperty G).ι.mapIso e)
    refine le_trans (iInf_le (fun f : A.representation.IntertwiningMap
      D.obj.representation => f.ker) (ε.toIntertwiningMap.comp f)) ?_
    intro v hv
    have h : ε (f v) = 0 := hv
    change f v = 0
    rw [← ε.symm_apply_apply (f v), h, map_zero]

end Laws

section Naturality

variable (c : CompactCoefficientClass.{uG, uV} G)
  {A : SmoothRep.{0, uG, uW} ℂ G} {B : SmoothRep.{0, uG, uX} ℂ G}

/-- An intertwiner maps the `c`-isotypic subrepresentation into that of its target. -/
theorem mapsTo_isotypicSubrepresentation
    (φ : A.representation.IntertwiningMap B.representation) :
    Set.MapsTo φ (isotypicSubrepresentation c A : Set A)
      (isotypicSubrepresentation c B : Set B) := by
  refine Subrepresentation.mapsTo_iSup φ _ _ fun D => ?_
  refine Subrepresentation.mapsTo_iSup φ _ _ fun hD => ?_
  refine Subrepresentation.mapsTo_iSup φ _ _ fun f => ?_
  rintro _ ⟨v, rfl⟩
  exact range_le_isotypicSubrepresentation D hD (φ.comp f) ⟨v, rfl⟩

/-- An intertwiner maps the `c`-annihilator into that of its target. -/
theorem mapsTo_annihilatorSubrepresentation
    (φ : A.representation.IntertwiningMap B.representation) :
    Set.MapsTo φ (annihilatorSubrepresentation c A : Set A)
      (annihilatorSubrepresentation c B : Set B) := by
  intro v hv
  rw [SetLike.mem_coe, mem_annihilatorSubrepresentation_iff] at hv ⊢
  exact fun D hD f => hv D hD (f.comp φ)

end Naturality

section Total

variable (A : SmoothRep.{0, uG, uW} ℂ G)

/-- The total compact part of `A`: the supremum over all compact-coefficient
classes at the representative carrier universe `uV`. -/
def totalIsotypicSubrepresentation : Subrepresentation A.representation :=
  ⨆ c : CompactCoefficientClass.{uG, uV} G, isotypicSubrepresentation c A

/-- The total annihilator of `A`: the infimum over all compact-coefficient
classes at the representative carrier universe `uV`. -/
def totalAnnihilatorSubrepresentation : Subrepresentation A.representation :=
  ⨅ c : CompactCoefficientClass.{uG, uV} G, annihilatorSubrepresentation c A

/-- Each isotypic part lies in the total compact part. -/
theorem isotypicSubrepresentation_le_totalIsotypicSubrepresentation
    (c : CompactCoefficientClass.{uG, uV} G) :
    isotypicSubrepresentation c A ≤ totalIsotypicSubrepresentation.{uG, uV} A :=
  le_iSup (fun c : CompactCoefficientClass.{uG, uV} G => isotypicSubrepresentation c A) c

/-- The total annihilator lies in each annihilator. -/
theorem totalAnnihilatorSubrepresentation_le_annihilatorSubrepresentation
    (c : CompactCoefficientClass.{uG, uV} G) :
    totalAnnihilatorSubrepresentation.{uG, uV} A ≤ annihilatorSubrepresentation c A :=
  iInf_le (fun c : CompactCoefficientClass.{uG, uV} G => annihilatorSubrepresentation c A) c

/-- The total compact part is the supremum of the ranges of all intertwiners from
all actual representatives with carriers in `Type uV`. -/
theorem totalIsotypicSubrepresentation_eq_iSup_range :
    totalIsotypicSubrepresentation.{uG, uV} A =
      ⨆ (D : IrreducibleCompactCoefficientRep.{uG, uV} G)
        (f : D.obj.representation.IntertwiningMap A.representation), f.range := by
  apply le_antisymm
  · refine iSup_le fun c => (isotypicSubrepresentation_le_iff _).2 fun D _ f => ?_
    exact le_iSup₂_of_le D f le_rfl
  · refine iSup₂_le fun D f => ?_
    exact (range_le_isotypicSubrepresentation D rfl f).trans
      (isotypicSubrepresentation_le_totalIsotypicSubrepresentation A (ofRep D))

/-- The total annihilator is the infimum of the kernels of all intertwiners to all
actual representatives with carriers in `Type uV`. -/
theorem totalAnnihilatorSubrepresentation_eq_iInf_ker :
    totalAnnihilatorSubrepresentation.{uG, uV} A =
      ⨅ (D : IrreducibleCompactCoefficientRep.{uG, uV} G)
        (f : A.representation.IntertwiningMap D.obj.representation), f.ker := by
  apply le_antisymm
  · refine le_iInf₂ fun D f => ?_
    exact (totalAnnihilatorSubrepresentation_le_annihilatorSubrepresentation A
      (ofRep D)).trans (annihilatorSubrepresentation_le_ker D rfl f)
  · refine le_iInf fun c => (le_annihilatorSubrepresentation_iff _).2 fun D _ f => ?_
    exact iInf₂_le_of_le D f le_rfl

/-- A vector lies in the total annihilator exactly when every intertwiner to every
representative with carrier in `Type uV` kills it. -/
theorem mem_totalAnnihilatorSubrepresentation_iff (v : A) :
    v ∈ totalAnnihilatorSubrepresentation.{uG, uV} A ↔
      ∀ (D : IrreducibleCompactCoefficientRep.{uG, uV} G)
        (f : A.representation.IntertwiningMap D.obj.representation), f v = 0 := by
  simp only [totalAnnihilatorSubrepresentation_eq_iInf_ker, Subrepresentation.mem_iInf]
  rfl

end Total

section TotalNaturality

variable {A : SmoothRep.{0, uG, uW} ℂ G} {B : SmoothRep.{0, uG, uX} ℂ G}

/-- An intertwiner maps the total compact part into that of its target. -/
theorem mapsTo_totalIsotypicSubrepresentation
    (φ : A.representation.IntertwiningMap B.representation) :
    Set.MapsTo φ (totalIsotypicSubrepresentation.{uG, uV} A : Set A)
      (totalIsotypicSubrepresentation.{uG, uV} B : Set B) :=
  Subrepresentation.mapsTo_iSup φ _ _ fun c =>
    (mapsTo_isotypicSubrepresentation c φ).mono_right
      (isotypicSubrepresentation_le_totalIsotypicSubrepresentation B c)

/-- An intertwiner maps the total annihilator into that of its target. -/
theorem mapsTo_totalAnnihilatorSubrepresentation
    (φ : A.representation.IntertwiningMap B.representation) :
    Set.MapsTo φ (totalAnnihilatorSubrepresentation.{uG, uV} A : Set A)
      (totalAnnihilatorSubrepresentation.{uG, uV} B : Set B) := by
  intro v hv
  rw [SetLike.mem_coe, mem_totalAnnihilatorSubrepresentation_iff] at hv ⊢
  exact fun D f => hv D (f.comp φ)

end TotalNaturality

end CompactCoefficientClass

end Langlands
