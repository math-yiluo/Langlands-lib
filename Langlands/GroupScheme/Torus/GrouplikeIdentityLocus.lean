import Langlands.GroupScheme.Torus.CharacterTwist
import Mathlib.GroupTheory.Finiteness

/-! # The identity locus of a finite-character grouplike family -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {B C : CommAlgCat.{u} R}

/-- A character family has an idempotent identity locus when the image of a
single idempotent detects identity specialization over every coefficient map. -/
def HasIdempotentIdentityLocus
    (s : Multiplicative M →* (algebra (M := M) B)ˣ) : Prop :=
  ∃ e : B, IsIdempotentElem e ∧
    ∀ (C : CommAlgCat.{u} R) (f : B ⟶ C),
      mapCharacter (coefficientMap (M := M) f) s = universal C ↔ f.hom e = 1

/-- A grouplike element is the monomial at `m` precisely when its coefficient
at `m` is one. This applies to arbitrary, possibly torsion, character groups. -/
theorem IsGrouplike.eq_single_iff {w : AddMonoidAlgebra B M}
    (hw : IsGrouplike w) (m : M) :
    w = AddMonoidAlgebra.single m 1 ↔ w.coeff m = 1 := by
  classical
  constructor
  · rintro rfl
    simp
  · intro hm
    ext n
    by_cases hnm : n = m
    · subst n
      simpa using hm
    · have h := hw.coeff_mul_coeff_of_ne (p := m) (q := n) (Ne.symm hnm)
      simpa [hm, hnm, Ne.symm hnm] using h

/-- A coefficientwise image of a grouplike element is a given monomial
precisely when the distinguished coefficient maps to one. -/
theorem IsGrouplike.map_eq_single_iff {w : AddMonoidAlgebra B M}
    (hw : IsGrouplike w) (f : B ⟶ C) (m : M) :
    (coefficientMap (M := M) f).hom w = AddMonoidAlgebra.single m 1 ↔
      f.hom (w.coeff m) = 1 := by
  rw [(hw.map f).eq_single_iff, coefficientMap_coeff]

/-- On a finite generating set, equality with the universal character is
detected by the coefficients at the corresponding character degrees. -/
theorem mapCharacter_eq_universal_iff
    {s : Multiplicative M →* (algebra (M := M) B)ˣ} (hs : IsGrouplikeHom s)
    (T : Finset (Multiplicative M)) (hT : Subgroup.closure (T : Set (Multiplicative M)) = ⊤)
    (f : B ⟶ C) :
    mapCharacter (coefficientMap (M := M) f) s = universal C ↔
      ∀ m ∈ T, f.hom ((s m : AddMonoidAlgebra B M).coeff m.toAdd) = 1 := by
  constructor
  · intro h m _
    have hm := congrArg (fun t : Multiplicative M →* (algebra (M := M) C)ˣ =>
      ((t m : (algebra (M := M) C)ˣ) : AddMonoidAlgebra C M)) h
    exact ((hs m).map_eq_single_iff f m.toAdd).1 hm
  · intro h
    apply MonoidHom.eq_of_eqOn_dense hT
    intro m hm
    apply Units.ext
    exact ((hs m).map_eq_single_iff f m.toAdd).2 (h m hm)

/-- A finite-character grouplike family has an idempotent whose value is one
exactly where its coefficientwise specialization is the identity family. -/
theorem exists_idempotent_identity_locus [AddGroup.FG M]
    {s : Multiplicative M →* (algebra (M := M) B)ˣ} (hs : IsGrouplikeHom s) :
    HasIdempotentIdentityLocus s := by
  classical
  obtain ⟨T, hT⟩ := Group.FG.out (G := Multiplicative M)
  let e : B := ∏ m ∈ T, (s m : AddMonoidAlgebra B M).coeff m.toAdd
  have he : IsIdempotentElem e := by
    clear hT
    dsimp [e]
    induction T using Finset.induction_on with
    | empty => simpa using (IsIdempotentElem.one (M := B))
    | @insert m T hm ih =>
      rw [Finset.prod_insert hm]
      exact ((hs m).isIdempotentElem_coeff m.toAdd).mul ih
  refine ⟨e, he, fun C f => ?_⟩
  rw [mapCharacter_eq_universal_iff hs T hT]
  constructor
  · intro h
    simp only [e, map_prod]
    exact Finset.prod_eq_one h
  · intro h m hm
    have hunit : IsUnit (f.hom ((s m : AddMonoidAlgebra B M).coeff m.toAdd)) := by
      apply isUnit_iff_dvd_one.2
      rw [← h]
      simpa only [e, map_prod] using
        Finset.dvd_prod_of_mem
          (fun m => f.hom ((s m : AddMonoidAlgebra B M).coeff m.toAdd)) hm
    have hid := ((hs m).map f).isIdempotentElem_coeff m.toAdd
    rw [coefficientMap_coeff] at hid
    exact hunit.mul_left_cancel (by rw [hid.eq, mul_one])

end Langlands.GroupScheme.CharacterAction
