import Langlands.ClassFieldTheory.Local.FiniteNormH2Statement
import Langlands.ClassFieldTheory.Local.FinitePGroupNormH2Proof
import Langlands.Cohomology.Tate.TransferProof
import Mathlib.GroupTheory.Sylow
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

private theorem h2_subsingleton_of_sylow
    {R G : Type u} [CommRing R] [Group G] [Finite G] (A : Rep R G)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Subsingleton (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2)) :
    Subsingleton (groupCohomology A 2) := by
  let := Fintype.ofFinite G
  have hz : ∀ x : tateCohomology A 2, x = 0 := by
    intro x
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hpx
    let : Fact p.Prime := ⟨hp⟩
    let P : Sylow p G := Classical.choice inferInstance
    let := Fintype.ofFinite P
    let := Fintype.ofFinite (G ⧸ (P : Subgroup G))
    let := h p P
    let e := ((TateCohomology.isoGroupCohomology 2).app
      (Rep.res (P : Subgroup G).subtype A)).toLinearEquiv
    have hr : Langlands.Tate.restriction (P : Subgroup G) A 2 x = 0 := by
      apply e.injective
      exact (h p P).elim _ _
    have hi : (P : Subgroup G).index • x = 0 := by
      rw [← Langlands.Tate.corestriction_restriction (P : Subgroup G) A 2 x, hr,
        map_zero]
    exact P.not_dvd_index (hpx.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hi))
  let : Subsingleton (tateCohomology A 2) :=
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ((TateCohomology.isoGroupCohomology 2).app A).toLinearEquiv.symm.injective.subsingleton

private def fixedFieldSubgroupCohomologyIso
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (H : Subgroup Gal(L/K)) (n : ℕ) :
    groupCohomology (Rep.res H.subtype (unitsRepresentation K L)) n ≅
      relativeCohomology (IntermediateField.fixedField H) L n :=
  groupCohomology.mapIso (IntermediateField.subgroupEquivAlgEquiv H)
    (LinearEquiv.refl IntegerScalars (Additive Lˣ)) (fun _ => rfl) n

private theorem norm_surjective_restrictScalars
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (hn : ∀ E : IntermediateField K L,
      let : FiniteDimensional E L := FiniteDimensional.right K E L
      Function.Surjective (Langlands.LocalClassField.normUnits E L))
    (E : IntermediateField K L) (F : IntermediateField E L) :
    let : FiniteDimensional E L := FiniteDimensional.right K E L
    let : FiniteDimensional F L := FiniteDimensional.right E F L
    Function.Surjective (Langlands.LocalClassField.normUnits F L) := by
  exact hn (F.restrictScalars K)

/-- Surjective norms to every intermediate field force the actual relative
second cohomology of a finite Galois extension to vanish. -/
theorem finiteNormH2Vanishing : FiniteNormH2Vanishing.{u,v} := by
  intro K L _ _ _ _ _ hn
  apply h2_subsingleton_of_sylow (unitsRepresentation K L)
  intro p _ P
  let E := IntermediateField.fixedField (P : Subgroup Gal(L/K))
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  have hp : IsPGroup p Gal(L/E) :=
    P.isPGroup'.of_equiv
      (IntermediateField.subgroupEquivAlgEquiv (P : Subgroup Gal(L/K)))
  let : Subsingleton (relativeCohomology E L 2) :=
    finitePGroupNormH2Vanishing p E L hp (norm_surjective_restrictScalars K L hn E)
  exact (fixedFieldSubgroupCohomologyIso K L
    (P : Subgroup Gal(L/K)) 2).toLinearEquiv.injective.subsingleton

end Langlands.ClassFieldTheory.Local
