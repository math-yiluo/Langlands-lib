import Langlands.Representation.Aubert.General.FirstAdjointness
import Langlands.Representation.Aubert.General.JacquetFiniteGeneration
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! Common irreducible constituents detected by nonzero actual Jacquet modules. -/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.Aubert.General.JacquetCommonConstituent

universe uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

/-- A nonzero Jacquet class already comes from a finitely generated smooth
subrepresentation. No exactness or quotient compactness is needed here. -/
theorem exists_finite_subrepresentation
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (E : SmoothRep.{0, uG, uV} ℂ G)
    (hE : Nontrivial ((jacquetFunctor h hU).obj E)) :
    ∃ S : Subrepresentation E.representation,
      Module.Finite ℂ[G] (subrepresentation E S).representation.asModule ∧
      Nontrivial ((jacquetFunctor h hU).obj (subrepresentation E S)) := by
  classical
  let := hE
  obtain ⟨y, hy⟩ := exists_ne (0 : (jacquetFunctor h hU).obj E)
  obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective E.representation U 1 y
  let N : Submodule ℂ[G] E.representation.asModule :=
    Submodule.span (M := E.representation.asModule) ℂ[G]
      {E.representation.asModuleEquiv.symm x}
  let S : Subrepresentation E.representation := Subrepresentation.ofSubmodule' N
  let A := subrepresentation E S
  have hxS : x ∈ S := by
    change E.representation.asModuleEquiv.symm x ∈ N
    exact Submodule.subset_span (Set.mem_singleton _)
  let x' : A := ⟨x, hxS⟩
  let j : A.representation.asModule →ₗ[ℂ[G]] N :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (hom (subtype E S))).codRestrict N (fun w => w.property)
  have hj : Function.Bijective j :=
    ⟨fun _ _ he => Subtype.ext (congrArg Subtype.val he),
      fun w => ⟨⟨w.val, w.property⟩, rfl⟩⟩
  have : Module.Finite ℂ[G] N :=
    Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hfinite : Module.Finite ℂ[G] A.representation.asModule :=
    Module.Finite.equiv (LinearEquiv.ofBijective j hj).symm
  have hx' : Jacquet.Localization.mk A.representation U 1 x' ≠ 0 := by
    intro hz
    apply hy
    let rj : Jacquet.Localization.Coinvariants A.representation U 1 →ₗ[ℂ]
        Jacquet.Localization.Coinvariants E.representation U 1 :=
      (hom ((jacquetFunctor h hU).map (subtype E S))).toLinearMap
    have he : rj (Jacquet.Localization.mk A.representation U 1 x') =
        Jacquet.Localization.mk E.representation U 1 x := rfl
    rw [hz, rj.map_zero] at he
    exact he.symm
  exact ⟨S, hfinite, ⟨⟨_, 0, hx'⟩⟩⟩

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- A finitely generated nonzero actual smooth representation admits an actual
surjective map to an irreducible representation, without a length hypothesis. -/
theorem exists_irreducible_quotient_of_moduleFinite
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : Nontrivial A)
    (hfinite : Module.Finite ℂ[G] A.representation.asModule) :
    ∃ τ : SmoothRep.{0, uG, uV} ℂ G,
      τ.IsIrreducible ∧ IsQuotient τ A := by
  classical
  let := hA
  let := hfinite
  have hco : IsCoatomic (Subrepresentation A.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := A.representation)).isCoatomic_iff.mpr inferInstance
  rcases hco.eq_top_or_exists_le_coatom ⊥ with he | ⟨S, hS, _⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : A)
    apply hx
    have hxS : x ∈ (⊥ : Subrepresentation A.representation) := by
      rw [he]
      exact Submodule.mem_top
    exact hxS
  · exact ⟨quotient A S,
      SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom A S hS,
      quotient_isQuotient S⟩

/-- The data of one irreducible representation of the Levi and one irreducible
representation shared by `E` and its actual normalized induction. -/
structure CommonConstituentData
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (E : SmoothRep.{0, uG, max uG uV} ℂ G) where
  levi : SmoothRep.{0, uG, max uG uV} ℂ M
  levi_irreducible : levi.IsIrreducible
  constituent : SmoothRep.{0, uG, max uG uV} ℂ G
  constituent_irreducible : constituent.IsIrreducible
  subquotient_original : IsSubquotient constituent E
  subquotient_induced :
    IsSubquotient constituent ((normalizedInductionFunctor h hU).obj levi)

/-- Nonzero Jacquet restriction gives a common constituent, provided the actual
left quotient is compact and the actual unipotent subgroup is unimodular. -/
def of_nontrivial_jacquet
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hδ : IsUnimodularModulus U hU)
    [CompactSpace (Induction.LeftQuotient P)]
    (E : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hE : Nontrivial ((jacquetFunctor h hU).obj E)) :
    CommonConstituentData h hU E := by
  classical
  have hex : Nonempty (CommonConstituentData h hU E) := by
    obtain ⟨S, hfinite, hnonzero⟩ := exists_finite_subrepresentation h hU E hE
    let A := subrepresentation E S
    let J := (jacquetFunctor h hU).obj A
    have hJfinite : Module.Finite ℂ[M] J.representation.asModule :=
      JacquetFiniteGeneration.finite_of_compactQuotient h hU A hfinite
    obtain ⟨τ, hτ, q, hq⟩ :=
      exists_irreducible_quotient_of_moduleFinite J hnonzero hJfinite
    let : IsSimpleModule ℂ[M] τ.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule τ.representation).mp hτ
    have hτnonzero : Nontrivial τ :=
      IsSimpleModule.nontrivial ℂ[M] τ.representation.asModule
    let := hτnonzero
    have hqnonzero : hom q ≠ 0 := by
      intro he
      obtain ⟨t, ht⟩ := exists_ne (0 : τ)
      obtain ⟨z, hz⟩ := hq t
      apply ht
      rw [← hz, he]
      rfl
    let f : A ⟶ (normalizedInductionFunctor h hU).obj τ :=
      ofHom ((FirstAdjointness.equiv h hU hδ A τ).symm (hom q))
    have hf : hom f ≠ 0 := by
      intro he
      apply hqnonzero
      have he' := congrArg (FirstAdjointness.equiv h hU hδ A τ) he
      simpa only [f, hom_ofHom, LinearEquiv.apply_symm_apply,
        map_zero] using he'
    let B := image f
    let p : A.representation.IntertwiningMap B.representation :=
      { toLinearMap := (hom f).toLinearMap.rangeRestrict
        isIntertwining' := fun g => by
          ext v
          exact Subtype.ext
            (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v) }
    have hp : Function.Surjective p := by
      rintro ⟨_, v, hv⟩
      exact ⟨v, Subtype.ext hv⟩
    have hB : Nontrivial B := by
      by_contra he
      have : Subsingleton B := not_nontrivial_iff_subsingleton.mp he
      apply hf
      ext v
      exact congrArg Subtype.val (Subsingleton.elim (p v) 0)
    let := hB
    obtain ⟨π, hπ, hπB⟩ :=
      SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient B
    have hBA : IsSubquotient B A :=
      SmoothRep.IsQuotient.isSubquotient ⟨ofHom p, hp⟩
    have hAE : IsSubquotient A E :=
      SmoothRep.IsSubrepresentation.isSubquotient (subrepresentation_isSubrepresentation S)
    have hBi : IsSubquotient B ((normalizedInductionFunctor h hU).obj τ) :=
      SmoothRep.IsSubrepresentation.isSubquotient
        (subrepresentation_isSubrepresentation (hom f).range)
    have hπA : IsSubquotient π A :=
      smoothSubquotientTransitivity ℂ G A B π hπB hBA
    exact ⟨⟨τ, hτ, π, hπ,
      smoothSubquotientTransitivity ℂ G E A π hπA hAE,
      smoothSubquotientTransitivity ℂ G
        ((normalizedInductionFunctor h hU).obj τ) B π hπB hBi⟩⟩
  exact Classical.choice hex

end Langlands.Aubert.General.JacquetCommonConstituent
