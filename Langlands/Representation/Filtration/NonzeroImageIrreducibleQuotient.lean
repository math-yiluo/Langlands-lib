import Langlands.Representation.Category.Subquotients

/-! A simple quotient of a nonzero image is a whole quotient of the source. -/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

theorem exists_irreducible_quotient_subquotient_of_nonzero
    {A B : SmoothRep.{uK, uG, uV} k G} (hA : A.HasFiniteLength)
    (f : A ⟶ B) (hf : hom f ≠ 0) :
    ∃ C : SmoothRep.{uK, uG, uV} k G,
      C.IsIrreducible ∧ IsQuotient C A ∧ IsSubquotient C B := by
  let I := image f
  let q : A.representation.IntertwiningMap I.representation :=
    { toLinearMap := (hom f).toLinearMap.rangeRestrict
      isIntertwining' := fun g => by
        ext v
        exact Subtype.ext
          (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v) }
  have hq : Function.Surjective q := by
    rintro ⟨_, v, hv⟩
    exact ⟨v, Subtype.ext hv⟩
  let qg := Representation.IntertwiningMap.equivLinearMapAsModule _ _ q
  have hIfin : IsFiniteLength (MonoidAlgebra k G) I.representation.asModule :=
    hA.of_surjective (f := qg) hq
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hIfin).1
  have hI : Nontrivial I := by
    by_contra h
    have : Subsingleton I := not_nontrivial_iff_subsingleton.mp h
    apply hf
    ext v
    exact congrArg Subtype.val (Subsingleton.elim (q v) 0)
  let : Nontrivial I.representation.asModule := hI
  obtain ⟨N, hN⟩ :=
    IsCoatomic.exists_coatom (α := Submodule (MonoidAlgebra k G) I.representation.asModule)
  let S : Subrepresentation I.representation := Subrepresentation.ofSubmodule' N
  let C := quotient I S
  let r : I ⟶ C := mkQ I S
  let rg := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom r)
  have hrg : Function.Surjective rg := mkQ_surjective I S
  have hker : rg.ker = N := by
    ext v
    change Submodule.Quotient.mk v = (0 : I ⧸ S.toSubmodule) ↔ v ∈ N
    exact Submodule.Quotient.mk_eq_zero _
  have hsimp : IsSimpleModule (MonoidAlgebra k G)
      (I.representation.asModule ⧸ rg.ker) := by
    apply isSimpleModule_iff_isCoatom.mpr
    rwa [hker]
  have hCsimp : IsSimpleModule (MonoidAlgebra k G) C.representation.asModule :=
    IsSimpleModule.congr (rg.quotKerEquivOfSurjective hrg).symm
  refine ⟨C, (Representation.irreducible_iff_isSimpleModule_asModule _).mpr hCsimp,
    ⟨ofHom q ≫ r, hrg.comp hq⟩, ?_⟩
  exact ⟨(hom f).range, S, ⟨CategoryTheory.Iso.refl C⟩⟩

end Langlands.SmoothRep
