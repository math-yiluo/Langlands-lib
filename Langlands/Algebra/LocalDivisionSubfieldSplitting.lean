import Langlands.Algebra.LocalDivisionUnramifiedSubfield
import Mathlib.FieldTheory.Finite.GaloisField

/-! Splitting in the original full-residue subfield by lifting all simple residue roots. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance : Algebra 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D

section Embedded

variable {L : Type uL} [Field L] [Algebra K L] [FiniteDimensional K L] (ι : L →ₐ[K] D)

/-- Choose an original integral lift of a specified simple residue root. -/
def localDivisionSubfieldRootLift
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (z : DivisionValuation.Residue (localReducedNormValuation K D))
    (hroot : f.eval₂ (localDivisionBaseReduction K D) z = 0)
    (hder : f.derivative.eval₂ (localDivisionBaseReduction K D) z ≠ 0) :
    (localDivisionSubfieldValuation K D ι).integer :=
  Classical.choose (localDivisionSubfield_lift_base_polynomial K D ι hsurj f hf z hroot hder)

theorem localDivisionSubfieldRootLift_spec
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (z : DivisionValuation.Residue (localReducedNormValuation K D))
    (hroot : f.eval₂ (localDivisionBaseReduction K D) z = 0)
    (hder : f.derivative.eval₂ (localDivisionBaseReduction K D) z ≠ 0) :
    f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι)
        (localDivisionSubfieldRootLift K D ι hsurj f hf z hroot hder) = 0 ∧
      localDivisionSubfieldResidueMap K D ι
        (DivisionValuation.reduction _
          (localDivisionSubfieldRootLift K D ι hsurj f hf z hroot hder)) = z :=
  Classical.choose_spec
    (localDivisionSubfield_lift_base_polynomial K D ι hsurj f hf z hroot hder)

/-- A monic integral polynomial with simple split reduction splits in a full-residue subfield. -/
theorem localDivisionSubfield_splits_base_polynomial
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (hsep : (f.map (IsLocalRing.residue 𝒪[K])).Separable)
    (hsplit : ((f.map (IsLocalRing.residue 𝒪[K])).map
      (algebraMap 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)))).Splits) :
    ((f.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).Splits := by
  classical
  let R := DivisionValuation.Residue (localReducedNormValuation K D)
  let p := f.map (IsLocalRing.residue 𝒪[K])
  let q := (f.map (algebraMap 𝒪[K] K)).map (algebraMap K L)
  have heval (g : Polynomial 𝒪[K]) (z : R) :
      Polynomial.aeval z (g.map (IsLocalRing.residue 𝒪[K])) =
        g.eval₂ (localDivisionBaseReduction K D) z := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hlift (z : p.rootSet R) :
      ∃ b : (localDivisionSubfieldValuation K D ι).integer,
        q.eval (b : L) = 0 ∧
          localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ b) = z := by
    have hroot : f.eval₂ (localDivisionBaseReduction K D) (z : R) = 0 := by
      rw [← heval]
      exact Polynomial.aeval_eq_zero_of_mem_rootSet z.prop
    have hder : f.derivative.eval₂ (localDivisionBaseReduction K D) (z : R) ≠ 0 := by
      rw [← heval, ← Polynomial.derivative_map]
      exact hsep.aeval_derivative_ne_zero (Polynomial.aeval_eq_zero_of_mem_rootSet z.prop)
    let b := localDivisionSubfieldRootLift K D ι hsurj f hf z hroot hder
    obtain ⟨hb, hred⟩ := localDivisionSubfieldRootLift_spec K D ι hsurj f hf z hroot hder
    refine ⟨b, ?_, hred⟩
    let θ := (localDivisionSubfieldValuation K D ι).integer.subtype
    have hθ : θ.comp (localDivisionSubfieldBaseIntegerMap K D ι) =
        (algebraMap K L).comp (algebraMap 𝒪[K] K) := by
      ext a
      rfl
    change q.eval (θ b) = 0
    dsimp only [q]
    rw [Polynomial.map_map, Polynomial.eval_map, ← hθ, ← Polynomial.hom_eval₂, hb, map_zero]
  choose b hb hred using hlift
  have hq : q.Monic := (hf.map _).map _
  let g : p.rootSet R → q.rootSet L := fun z =>
    ⟨(b z : L), Polynomial.mem_rootSet_of_ne hq.ne_zero |>.mpr (by simpa using hb z)⟩
  have hg : Function.Injective g := by
    intro x y h
    have hv : (b x : L) = (b y : L) :=
      congrArg (fun t : q.rootSet L => (t : L)) h
    apply Subtype.ext
    rw [← hred x, ← hred y]
    apply congrArg (fun t => localDivisionSubfieldResidueMap K D ι
      (DivisionValuation.reduction _ t))
    apply Subtype.ext
    exact hv
  apply Polynomial.splits_iff_card_roots.mpr
  apply le_antisymm (Polynomial.card_roots' q)
  calc
    q.natDegree = p.natDegree := by
      dsimp only [q, p]
      rw [(hf.map _).natDegree_map, hf.natDegree_map, hf.natDegree_map]
    _ = Fintype.card (p.rootSet R) :=
      (Polynomial.card_rootSet_eq_natDegree hsep hsplit).symm
    _ ≤ Fintype.card (q.rootSet L) := Fintype.card_le_of_injective g hg
    _ = q.roots.toFinset.card := by simp [Polynomial.rootSet_def, Polynomial.aroots_def]
    _ ≤ q.roots.card := Multiset.toFinset_card_le q.roots

end Embedded

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra.IsCentral K D] in
/-- Splitting of its original minimal polynomial makes a singleton adjoin a splitting field. -/
theorem residueGenerator_isSplittingField (a : D)
    (hsplit : letI := residueGeneratorField K D a
      ((minpoly K a).map (algebraMap K (residueGeneratorSubalgebra K D a))).Splits) :
    letI := residueGeneratorField K D a
    Polynomial.IsSplittingField K (residueGeneratorSubalgebra K D a) (minpoly K a) := by
  let := residueGeneratorField K D a
  let E := residueGeneratorSubalgebra K D a
  let c : E := ⟨a, residueGenerator_mem K D a⟩
  refine ⟨hsplit, ?_⟩
  apply top_unique
  rw [← residueGenerator_adjoin_eq_top K D a]
  apply Algebra.adjoin_mono
  intro x hx
  have hxc : x = c := Set.mem_singleton_iff.mp hx
  subst x
  apply (Polynomial.mem_rootSet_of_ne
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral a))).mpr
  change (Polynomial.aeval c) (minpoly K (E.val c)) = 0
  rw [minpoly.algHom_eq E.val Subtype.val_injective c]
  exact minpoly.aeval K c

/-- The constructed original full-residue field is Galois and has exactly the residue degree. -/
theorem exists_localDivision_fullResidue_galois_subfield :
    ∃ b : (localReducedNormValuation K D).integer,
      letI := residueGeneratorField K D (b : D)
      IsSeparable K (b : D) ∧
        Function.Surjective (localDivisionSubfieldResidueMap K D
          (residueGeneratorSubalgebra K D (b : D)).val) ∧
        Module.finrank K (residueGeneratorSubalgebra K D (b : D)) =
          Module.finrank 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) ∧
        IsGalois K (residueGeneratorSubalgebra K D (b : D)) := by
  obtain ⟨f, b, hmon, hres, hmin, hsep, hsurj, hdim⟩ :=
    exists_localDivision_fullResidue_polynomial_subfield K D
  let := residueGeneratorField K D (b : D)
  let E := residueGeneratorSubalgebra K D (b : D)
  let R := DivisionValuation.Residue (localReducedNormValuation K D)
  have hsepR : (f.map (IsLocalRing.residue 𝒪[K])).Separable := by
    rw [hres]
    exact PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
  have hsplitR :
      ((f.map (IsLocalRing.residue 𝒪[K])).map (algebraMap 𝓀[K] R)).Splits := by
    rw [hres]
    exact IsGalois.splits 𝓀[K] _
  have hsplit : ((minpoly K (b : D)).map (algebraMap K E)).Splits := by
    rw [← hmin]
    exact localDivisionSubfield_splits_base_polynomial K D E.val hsurj f hmon hsepR hsplitR
  let : Polynomial.IsSplittingField K E (minpoly K (b : D)) :=
    residueGenerator_isSplittingField K D (b : D) hsplit
  refine ⟨b, hsep, hsurj, hdim, ?_⟩
  exact IsGalois.of_separable_splitting_field hsep

end Langlands.CentralDivision
