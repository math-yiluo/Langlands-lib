import Langlands.ClassFieldTheory.Local.ClassFormationCupLawsStatement
import Langlands.ClassFieldTheory.Local.FundamentalConsequencesProof

/-!
# Tate isomorphisms from the finite class-formation axioms

For a finite Galois extension `L/F` of p-adic fields and a subgroup `H` of
`Gal(L/F)` with fixed field `E`, subgroup reindexing identifies the
cohomology of `H` with that of `L/E`. The finite class-formation axioms give
vanishing of `H¹(L/E)`, and the restriction of a fundamental class of `L/F`
is the fundamental class of `L/E`, which generates `H²(L/E)` and has order
`[L : E] = |H|`. Tate's cup-product theorem then gives bijectivity of left
cup with the fundamental class in every integer Tate degree.
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- For an intermediate field, the image of its Galois group under restriction
of scalars is its fixing subgroup. -/
theorem relativeGaloisSubgroup_intermediateField (E : IntermediateField K M) :
    relativeGaloisSubgroup K E M = E.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    exact ⟨IntermediateField.fixingSubgroupEquiv E ⟨σ, hσ⟩, AlgEquiv.ext fun _ => rfl⟩

end Tower

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- Under the finite class-formation axioms, the subgroup of `Gal(L/F)` fixing
an intermediate p-adic field `E` satisfies the hypotheses of Tate's theorem for
the units of `L` and any fundamental class of `L/F`. -/
theorem relativeClassFormation_subgroupConditions (I : InvariantFamily.{u,u} p)
    (hI : I.RelativeClassFormation) (F E : PadicField.{u} p) (L : Type u) [Field L]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier L] [Algebra E.Carrier L] [IsScalarTower F.Carrier E.Carrier L]
    [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier L]
    [FiniteDimensional E.Carrier L] [IsGalois F.Carrier L] [IsGalois E.Carrier L]
    (c : relativeCohomology F.Carrier L 2)
    (hc : IsFundamentalClass F.Carrier L (I.relative F L) c) :
    Subsingleton (groupCohomology (Rep.res (relativeGaloisSubgroup F.Carrier E.Carrier L).subtype
        (unitsRepresentation F.Carrier L)) 1) ∧
      Nat.card (groupCohomology (Rep.res (relativeGaloisSubgroup F.Carrier E.Carrier L).subtype
        (unitsRepresentation F.Carrier L)) 2) =
          Nat.card (relativeGaloisSubgroup F.Carrier E.Carrier L) ∧
      AddSubgroup.zmultiples
          (groupCohomology.map (relativeGaloisSubgroup F.Carrier E.Carrier L).subtype
            (𝟙 (Rep.res (relativeGaloisSubgroup F.Carrier E.Carrier L).subtype
              (unitsRepresentation F.Carrier L))) 2 c) = ⊤ := by
  let e1 := relativeSubgroupCohomologyIso F.Carrier E.Carrier L 1
  let e2 := relativeSubgroupCohomologyIso F.Carrier E.Carrier L 2
  have h1 : Subsingleton (relativeCohomology E.Carrier L 1) := hI.1 E L
  obtain ⟨d, hd, -⟩ := (I.fundamentalClasses_of_relativeImages hI.2.1 E L).1
  have hres : relativeRestriction F.Carrier E.Carrier L 2 c = d :=
    I.fundamentalRestriction_of_relativeClassFormation hI F E L c d hc hd
  obtain ⟨hord, hgen⟩ := (I.fundamentalClasses_of_relativeImages hI.2.1 E L).2 d hd
  have hmap : groupCohomology.map (relativeGaloisSubgroup F.Carrier E.Carrier L).subtype
      (𝟙 (Rep.res (relativeGaloisSubgroup F.Carrier E.Carrier L).subtype
        (unitsRepresentation F.Carrier L))) 2 c = e2.hom d := by
    rw [← hres, ← relativeRestriction_comp_subgroupCohomologyIso]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact e1.toLinearEquiv.symm.injective.subsingleton
  · rw [← Nat.card_congr e2.toLinearEquiv.toEquiv, ← AddSubgroup.card_top, ← hgen,
      Nat.card_zmultiples, hord, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr (relativeGaloisSubgroupEquiv F.Carrier E.Carrier L).toEquiv
  · rw [hmap, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e2.toLinearEquiv.surjective y
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen ▸ AddSubgroup.mem_top x)
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, (map_zsmul e2.toLinearEquiv k d).symm⟩

end InvariantFamily

/-- Tate's cup-product theorem turns the finite class-formation axioms into
bijectivity of left cup with every fundamental class in every integer degree. -/
theorem classFormationTateIsomorphisms : ClassFormationTateIsomorphismsStatement.{u} := by
  intro hTate p _ I hI F L _ _ _ _ c hc n
  let := Fintype.ofFinite Gal(L/F.Carrier)
  refine hTate Gal(L/F.Carrier) (unitsRepresentation F.Carrier L) c ?_ n
  intro q _ P
  let E := IntermediateField.fixedField P.1
  let : Algebra (Padic p) E :=
    ((algebraMap F.Carrier E).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
  have : IsScalarTower (Padic p) F.Carrier E := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F.Carrier E
  let E' : PadicField.{u} p := PadicField.ofField E
  let : Algebra F.Carrier E'.Carrier := (inferInstance : Algebra F.Carrier E)
  let : Algebra E'.Carrier L := (inferInstance : Algebra E L)
  have : IsScalarTower (Padic p) F.Carrier E'.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F.Carrier E)
  have : IsScalarTower F.Carrier E'.Carrier L := (inferInstance : IsScalarTower F.Carrier E L)
  have : FiniteDimensional F.Carrier E'.Carrier :=
    (inferInstance : FiniteDimensional F.Carrier E)
  have : FiniteDimensional E'.Carrier L := (inferInstance : FiniteDimensional E L)
  have : IsGalois E'.Carrier L := (inferInstance : IsGalois E L)
  have hH : relativeGaloisSubgroup F.Carrier E'.Carrier L = P.1 :=
    (relativeGaloisSubgroup_intermediateField F.Carrier L E).trans
      (IntermediateField.fixingSubgroup_fixedField P.1)
  have h := I.relativeClassFormation_subgroupConditions hI F E' L c hc
  rw [hH] at h
  exact h

end Langlands.ClassFieldTheory.Local
