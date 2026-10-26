import Langlands.ClassFieldTheory.Local.FinitePGroupNormH2Statement
import Langlands.ClassFieldTheory.Local.IntermediateNormSurjectivityProof
import Langlands.ClassFieldTheory.Local.CyclicNorm
import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof
import Mathlib.GroupTheory.Nilpotent

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

private theorem cyclicH2_subsingleton_of_norm_surjective
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (hn : Function.Surjective (Langlands.LocalClassField.normUnits K L)) :
    Subsingleton (relativeCohomology K L 2) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have htop : Langlands.LocalClassField.normSubgroup K L = ⊤ :=
    MonoidHom.range_eq_top.mpr hn
  let : Subsingleton (Langlands.LocalClassField.NormQuotient K L) :=
    QuotientGroup.subsingleton_iff.mpr htop
  exact (cyclicH2NormEquiv K L σ hσ).injective.subsingleton

private theorem towerH2_subsingleton
    (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsGalois K E] [IsGalois K L]
    [Subsingleton (relativeCohomology K E 2)]
    [Subsingleton (relativeCohomology E L 2)] :
    Subsingleton (relativeCohomology K L 2) := by
  have hex := (finiteRelativeH2InflationExactness K E L).2
  have hz : ∀ x : relativeCohomology K L 2, x = 0 := by
    intro x
    have hx : x ∈ LinearMap.ker (relativeRestriction K E L 2).hom :=
      Subsingleton.elim _ _
    rw [← hex] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Surjective norms to all intermediate fields force relative H2 to vanish
for a finite Galois extension with p-group Galois group. -/
theorem finitePGroupNormH2Vanishing :
    FinitePGroupNormH2Vanishing.{u} := by
  intro p _
  have aux : ∀ n (K L : Type u) [Field K] [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L],
      Nat.card Gal(L/K) = n → IsPGroup p Gal(L/K) →
      (∀ E : IntermediateField K L,
        let : FiniteDimensional E L := FiniteDimensional.right K E L
        Function.Surjective (Langlands.LocalClassField.normUnits E L)) →
      Subsingleton (relativeCohomology K L 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K L _ _ _ _ _ hcard hp hn
      by_cases hc : IsCyclic Gal(L/K)
      · let := hc
        exact cyclicH2_subsingleton_of_norm_surjective K L
          (intermediateNormSurjectivityInheritance K L hn).1
      let : Nontrivial Gal(L/K) := Nontrivial.of_not_isCyclic hc
      let : Group.IsNilpotent Gal(L/K) := hp.isNilpotent
      have hpdvd : p ∣ Nat.card Gal(L/K) :=
        hp.card_eq_or_dvd.resolve_left (ne_of_gt Finite.one_lt_card)
      obtain ⟨H, hindex, hnormal⟩ :=
        Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hpdvd
      let := hnormal
      let E := IntermediateField.fixedField H
      let : FiniteDimensional E L := FiniteDimensional.right K E L
      let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
      have hupper : IsPGroup p Gal(L/E) :=
        (hp.to_subgroup H).of_equiv (IntermediateField.subgroupEquivAlgEquiv H)
      have hcardUpper : Nat.card Gal(L/E) = Nat.card H :=
        Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv H).symm.toEquiv
      have hlt : Nat.card Gal(L/E) < n := by
        rw [hcardUpper, ← hcard, ← H.card_mul_index, hindex]
        exact lt_mul_right Nat.card_pos (Fact.out : p.Prime).one_lt
      have hnormUpper : ∀ F : IntermediateField E L,
          let : FiniteDimensional F L := FiniteDimensional.right E F L
          Function.Surjective (Langlands.LocalClassField.normUnits F L) := by
        intro F
        exact hn (F.restrictScalars K)
      let : Subsingleton (relativeCohomology E L 2) :=
        ih (Nat.card Gal(L/E)) hlt E L rfl hupper hnormUpper
      have hcardLower : Nat.card Gal(E/K) = p := by
        rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv]
        exact H.index_eq_card.symm.trans hindex
      let : IsCyclic Gal(E/K) := isCyclic_of_prime_card hcardLower
      let : Subsingleton (relativeCohomology K E 2) :=
        cyclicH2_subsingleton_of_norm_surjective K E
          ((intermediateNormSurjectivityInheritance K L hn).2.1 E)
      exact towerH2_subsingleton K E L
  intro K L _ _ _ _ _ hp hn
  exact aux (Nat.card Gal(L/K)) K L rfl hp hn

end Langlands.ClassFieldTheory.Local
