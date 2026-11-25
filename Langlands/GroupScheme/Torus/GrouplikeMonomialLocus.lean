import Langlands.GroupScheme.Torus.GrouplikeIdentityLocus

/-! # Monomial loci of finite-character grouplike families -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {Λ Γ : Type u} [AddCommGroup Λ] [AddCommGroup Γ]
    {B C : CommAlgCat.{u} R}

/-- A coefficient idempotent detects where a grouplike family is induced by
a specified homomorphism of full character groups. -/
def HasIdempotentMonomialLocus
    (s : Multiplicative Λ →* (algebra (M := Γ) B)ˣ) (p : Λ →+ Γ) : Prop :=
  ∃ e : B, IsIdempotentElem e ∧
    ∀ (C : CommAlgCat.{u} R) (f : B ⟶ C),
      mapCharacter (coefficientMap (M := Γ) f) s =
          (universal (M := Γ) C).comp (AddMonoidHom.toMultiplicative p) ↔
        f.hom e = 1

/-- Equality with a specified monomial family is detected on generators. -/
theorem mapCharacter_eq_monomials_iff
    {s : Multiplicative Λ →* (algebra (M := Γ) B)ˣ}
    (hs : ∀ m, IsGrouplike (M := Γ) (s m : AddMonoidAlgebra B Γ))
    (p : Λ →+ Γ) (T : Finset (Multiplicative Λ))
    (hT : Subgroup.closure (T : Set (Multiplicative Λ)) = ⊤) (f : B ⟶ C) :
    mapCharacter (coefficientMap (M := Γ) f) s =
        (universal (M := Γ) C).comp (AddMonoidHom.toMultiplicative p) ↔
      ∀ m ∈ T, f.hom ((s m : AddMonoidAlgebra B Γ).coeff (p m.toAdd)) = 1 := by
  constructor
  · intro h m _
    have hm := congrArg (fun t : Multiplicative Λ →* (algebra (M := Γ) C)ˣ =>
      ((t m : (algebra (M := Γ) C)ˣ) : AddMonoidAlgebra C Γ)) h
    exact ((hs m).map_eq_single_iff f (p m.toAdd)).1 hm
  · intro h
    apply MonoidHom.eq_of_eqOn_dense hT
    intro m hm
    apply Units.ext
    exact ((hs m).map_eq_single_iff f (p m.toAdd)).2 (h m hm)

/-- Finite generation of the source characters gives an idempotent
monomial locus for every proposed character homomorphism. -/
theorem exists_idempotent_monomial_locus [AddGroup.FG Λ]
    {s : Multiplicative Λ →* (algebra (M := Γ) B)ˣ}
    (hs : ∀ m, IsGrouplike (M := Γ) (s m : AddMonoidAlgebra B Γ)) (p : Λ →+ Γ) :
    HasIdempotentMonomialLocus s p := by
  classical
  obtain ⟨T, hT⟩ := Group.exists_of_isMulFG (Multiplicative Λ)
  let e : B := ∏ m ∈ T, (s m : AddMonoidAlgebra B Γ).coeff (p m.toAdd)
  have he : IsIdempotentElem e := by
    clear hT
    dsimp [e]
    induction T using Finset.induction_on with
    | empty => simpa using (IsIdempotentElem.one (M := B))
    | @insert m T hm ih =>
      rw [Finset.prod_insert hm]
      exact ((hs m).isIdempotentElem_coeff (p m.toAdd)).mul ih
  refine ⟨e, he, fun C f => ?_⟩
  rw [mapCharacter_eq_monomials_iff hs p T hT]
  constructor
  · intro h
    simp only [e, map_prod]
    exact Finset.prod_eq_one h
  · intro h m hm
    have hunit : IsUnit (f.hom ((s m : AddMonoidAlgebra B Γ).coeff (p m.toAdd))) := by
      apply isUnit_iff_dvd_one.2
      rw [← h]
      simpa only [e, map_prod] using
        Finset.dvd_prod_of_mem
          (fun m => f.hom ((s m : AddMonoidAlgebra B Γ).coeff (p m.toAdd))) hm
    have hid := ((hs m).map f).isIdempotentElem_coeff (p m.toAdd)
    rw [coefficientMap_coeff] at hid
    exact hunit.mul_left_cancel (by rw [hid.eq, mul_one])

/-- A grouplike element over a domain is a single monomial. -/
theorem IsGrouplike.eq_single_of_isDomain [IsDomain C]
    {w : AddMonoidAlgebra C Γ} (hw : IsGrouplike (M := Γ) w) :
    ∃ n, w = AddMonoidAlgebra.single n 1 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, w.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    have hsum := hw.sum_coeff
    rw [Finset.sum_eq_zero (fun n _ => h n)] at hsum
    exact zero_ne_one hsum
  exact ⟨n, (hw.eq_single_iff n).2
    (((IsIdempotentElem.iff_eq_zero_or_one (G₀ := C)).1
      (hw.isIdempotentElem_coeff n)).resolve_left hn)⟩

/-- Specialization over a domain gives a homomorphism of full character groups. -/
theorem exists_monomial_specialization [IsDomain C]
    {s : Multiplicative Λ →* (algebra (M := Γ) B)ˣ}
    (hs : ∀ m, IsGrouplike (M := Γ) (s m : AddMonoidAlgebra B Γ)) (f : B ⟶ C) :
    ∃ p : Λ →+ Γ, mapCharacter (coefficientMap (M := Γ) f) s =
      (universal (M := Γ) C).comp (AddMonoidHom.toMultiplicative p) := by
  classical
  let t := mapCharacter (coefficientMap (M := Γ) f) s
  have ht (m : Multiplicative Λ) :
      ∃ n, (t m : AddMonoidAlgebra C Γ) = AddMonoidAlgebra.single n 1 :=
    ((hs m).map f).eq_single_of_isDomain
  choose n hn using ht
  let p : Λ →+ Γ :=
    { toFun := fun l => n (.ofAdd l)
      map_zero' := by
        apply AddMonoidAlgebra.single_left_injective (one_ne_zero (α := C))
        calc
          _ = (t 1 : AddMonoidAlgebra C Γ) := (hn 1).symm
          _ = 1 := congrArg Units.val t.map_one
          _ = _ := rfl
      map_add' := by
        intro l m
        apply AddMonoidAlgebra.single_left_injective (one_ne_zero (α := C))
        calc
          _ = (t (.ofAdd (l + m)) : AddMonoidAlgebra C Γ) := (hn _).symm
          _ = (t (.ofAdd l) : AddMonoidAlgebra C Γ) *
              (t (.ofAdd m) : AddMonoidAlgebra C Γ) :=
            congrArg Units.val (t.map_mul (.ofAdd l) (.ofAdd m))
          _ = _ := by rw [hn, hn, AddMonoidAlgebra.single_mul_single, one_mul] }
  refine ⟨p, ?_⟩
  apply MonoidHom.ext
  intro m
  apply Units.ext
  exact hn m

/-- Every domain specialization has a monomial presentation on an idempotent
locus containing that specialization. -/
theorem exists_idempotent_monomial_presentation [AddGroup.FG Λ] [IsDomain C]
    {s : Multiplicative Λ →* (algebra (M := Γ) B)ˣ}
    (hs : ∀ m, IsGrouplike (M := Γ) (s m : AddMonoidAlgebra B Γ)) (f : B ⟶ C) :
    ∃ (p : Λ →+ Γ) (e : B), IsIdempotentElem e ∧ f.hom e = 1 ∧
      ∀ (D : CommAlgCat.{u} R) (g : B ⟶ D),
        mapCharacter (coefficientMap (M := Γ) g) s =
            (universal (M := Γ) D).comp (AddMonoidHom.toMultiplicative p) ↔
          g.hom e = 1 := by
  obtain ⟨p, hp⟩ := exists_monomial_specialization hs f
  obtain ⟨e, he, heval⟩ := exists_idempotent_monomial_locus hs p
  exact ⟨p, e, he, (heval C f).1 hp, heval⟩

end Langlands.GroupScheme.CharacterAction
