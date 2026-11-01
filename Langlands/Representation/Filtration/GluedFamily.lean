import Langlands.Representation.Filtration.Splicing
import Langlands.Representation.Filtration.Transport
import Langlands.Representation.Filtration.OneStep
import Langlands.Representation.Filtration.Precomposition

/-!
# Gluing from families indexed by finite types

`IsGluedFromFamily M P` says that `M` is glued from the complete family `P`
indexed by a finite type, for some enumeration of the index type. It is
stable under natural isomorphisms, reindexing by equivalences, precomposition,
and splicing along short exact sequences; the empty and one-element families
cover zero functors and natural isomorphisms.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC uD vD uι uκ

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

namespace RepFunctorFiltration

/-- The empty filtration of a functor with zero values. -/
def empty (M : C ⥤ Rep.{uV} R G) (hM : ∀ X, Subsingleton (M.obj X)) :
    RepFunctorFiltration M 0 where
  step _ := RepSubfunctor.zero M
  monotone _ := fun _ _ _ => le_rfl
  zero _ := rfl
  top X := by
    apply eq_top_iff.mpr
    intro v _
    change v ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    exact Subsingleton.elim _ _

end RepFunctorFiltration

/-- `M` is glued from the complete finite family `P`, in some enumeration. -/
def IsGluedFromFamily (M : C ⥤ Rep.{uV} R G) {ι : Type uι} [Fintype ι]
    (P : ι → C ⥤ Rep.{uV} R G) : Prop :=
  ∃ e : Fin (Fintype.card ι) ≃ ι, IsGluedFrom M (P ∘ e)

namespace IsGluedFromFamily

variable {M M' L Q : C ⥤ Rep.{uV} R G}

/-- Convert an ordinary gluing statement with a complete enumeration. -/
theorem of_isGluedFrom {ι : Type uι} [Fintype ι] {P : ι → C ⥤ Rep.{uV} R G}
    {n : ℕ} (e : Fin n ≃ ι) (h : IsGluedFrom M (P ∘ e)) : IsGluedFromFamily M P := by
  have hn : Fintype.card ι = n := by simpa using (Fintype.card_congr e).symm
  refine ⟨(finCongr hn).trans e, ?_⟩
  have := h.reindex (finCongr hn)
  simpa only [Function.comp_def, Equiv.trans_apply] using this

/-- Unpack to any length equal to the cardinality of the index type. -/
theorem exists_equiv {ι : Type uι} [Fintype ι] {P : ι → C ⥤ Rep.{uV} R G}
    (h : IsGluedFromFamily M P) (n : ℕ) (hn : Fintype.card ι = n) :
    ∃ e : Fin n ≃ ι, IsGluedFrom M (P ∘ e) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(finCongr hn.symm).trans e, ?_⟩
  have := he.reindex (finCongr hn.symm)
  simpa only [Function.comp_def, Equiv.trans_apply] using this

/-- Transport along a natural isomorphism of the glued functor. -/
theorem iso {ι : Type uι} [Fintype ι] {P : ι → C ⥤ Rep.{uV} R G}
    (h : IsGluedFromFamily M P) (e : M ≅ M') : IsGluedFromFamily M' P := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, hσ.iso e (fun _ => Iso.refl _)⟩

/-- Reindex along an equivalence, with natural isomorphisms of the pieces. -/
theorem equiv {ι : Type uι} [Fintype ι] {κ : Type uκ} [Fintype κ]
    {P : ι → C ⥤ Rep.{uV} R G} {P' : κ → C ⥤ Rep.{uV} R G}
    (h : IsGluedFromFamily M P) (σ : ι ≃ κ) (a : ∀ i, P i ≅ P' (σ i)) :
    IsGluedFromFamily M P' := by
  obtain ⟨e, he⟩ := h
  refine of_isGluedFrom (e.trans σ) ?_
  exact he.iso (Iso.refl _) (fun i => a (e i))

/-- Replace the pieces by naturally isomorphic ones, with the same index type. -/
theorem isoPieces {ι : Type uι} [Fintype ι] {P P' : ι → C ⥤ Rep.{uV} R G}
    (h : IsGluedFromFamily M P) (a : ∀ i, P i ≅ P' i) : IsGluedFromFamily M P' :=
  h.equiv (Equiv.refl ι) a

/-- Precompose with a functor on the input category. -/
theorem precomp {ι : Type uι} [Fintype ι] {P : ι → C ⥤ Rep.{uV} R G}
    (h : IsGluedFromFamily M P) (J : D ⥤ C) :
    IsGluedFromFamily (J ⋙ M) (fun i => J ⋙ P i) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, he.precomp J⟩

/-- A naturally isomorphic copy of the only piece. -/
theorem of_iso_unique {ι : Type uι} [Fintype ι] [Unique ι] {P : ι → C ⥤ Rep.{uV} R G}
    (e : M ≅ P default) : IsGluedFromFamily M P := by
  refine of_isGluedFrom (Equiv.ofUnique (Fin 1) ι) (isGluedFrom_singleton _ fun i => ?_)
  exact e ≪≫ eqToIso (congrArg P (Subsingleton.elim _ _))

/-- A functor with zero values is glued from an empty family. -/
theorem of_isEmpty {ι : Type uι} [Fintype ι] [IsEmpty ι] {P : ι → C ⥤ Rep.{uV} R G}
    (hM : ∀ X, Subsingleton (M.obj X)) : IsGluedFromFamily M P := by
  exact of_isGluedFrom (Equiv.equivOfIsEmpty (Fin 0) ι)
    ⟨Equiv.refl _, RepFunctorFiltration.empty M hM, fun i => i.elim0⟩

/-- Splice the families of a natural short exact sequence. -/
theorem splice {ι : Type uι} [Fintype ι] {κ : Type uκ} [Fintype κ]
    {P : ι → C ⥤ Rep.{uV} R G} {P' : κ → C ⥤ Rep.{uV} R G}
    (hL : IsGluedFromFamily L P) (hQ : IsGluedFromFamily Q P')
    (ι' : L ⟶ M) (π : M ⟶ Q)
    (hexact : ∀ X, LinearMap.range (ι'.app X).hom.toLinearMap =
      LinearMap.ker (π.app X).hom.toLinearMap)
    (hinj : ∀ X, Function.Injective (ι'.app X).hom)
    (hsurj : ∀ X, Function.Surjective (π.app X).hom) :
    IsGluedFromFamily M (Sum.elim P P') := by
  obtain ⟨eL, hL⟩ := hL
  obtain ⟨eQ, hQ⟩ := hQ
  have h := hL.splice hQ ι' π hexact hinj hsurj
  let σ : Fin (Fintype.card ι + Fintype.card κ) ≃ ι ⊕ κ :=
    (RepFunctorFiltration.spliceIndexEquiv _ _).trans (Equiv.sumCongr eL eQ)
  refine of_isGluedFrom σ ?_
  have hp : RepFunctorFiltration.concatPieces (P ∘ eL) (P' ∘ eQ) = Sum.elim P P' ∘ σ := by
    funext i
    simp only [RepFunctorFiltration.concatPieces, Function.comp_apply, σ,
      Equiv.trans_apply]
    cases (RepFunctorFiltration.spliceIndexEquiv _ _) i <;> rfl
  rw [← hp]
  exact h

end IsGluedFromFamily

end Langlands
