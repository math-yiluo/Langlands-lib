import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.Geometric.GeometricLemmaStatement

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV

/-- At rank zero the only ambient matrix is the identity, so the Levis are associated. -/
theorem levisAssociated_rankZero {F : Type uF} [Field F] (B C : BlockShape 0) :
    LevisAssociated (F := F) B C := by
  refine ⟨⟨1, ?_⟩⟩
  exact Subsingleton.elim _ _

/-- A rank-zero shape has no block index. -/
theorem blockShape_rankZero_index_false (B : BlockShape 0) (i : Fin B.length) : False :=
  Fin.elim0 (B.index i ⟨0, B.positive i⟩)

/-- The empty target has a refinement associated to any rank-zero source. -/
theorem exists_associated_refinement_rankZero {F : Type uF} [Field F]
    (B C : BlockShape 0) :
    ∃ (S : BlockRefinement C) (w : Equiv.Perm (Fin 0)),
      (B.leviSubgroup F).map (MulAut.conj (permutation 0 F w)).toMonoidHom =
        (refinedLevi F C S).map (C.leviEmbedding F) := by
  refine ⟨fun i => False.elim (blockShape_rankZero_index_false C i), 1, ?_⟩
  exact Subsingleton.elim _ _

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The nonassociation hypothesis is impossible at rank zero. -/
theorem nonassociatedJacquetSubquotients_rankZero :
    NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T 0 := by
  let := T.topology
  intro B C ρ hρ hBC
  exact False.elim (hBC (levisAssociated_rankZero B C))

/-- The absence of an associated refinement is impossible at rank zero. -/
theorem quasicuspidalJacquetVanishing_rankZero :
    QuasicuspidalJacquetVanishingTheorem.{uF, uV} F T 0 := by
  let := T.topology
  intro B C ρ hρ hBC
  exact False.elim (hBC (exists_associated_refinement_rankZero B C))

/-- Equality relabeling of the acting subgroup preserves a zero carrier. -/
theorem subgroupEqualityFunctor_subsingleton {G : Type uF} [Group G]
    [TopologicalSpace G] (H K : Subgroup G) (h : H = K)
    (A : SmoothRep.{0, uF, uV} ℂ H) [Subsingleton A] :
    Subsingleton ((subgroupEqualityFunctor H K h).obj A) := by
  subst K
  exact inferInstanceAs (Subsingleton A)

/-- Normalized refined induction of a zero representation is zero. -/
theorem normalizedRefinedInductionFunctor_subsingleton {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S),
      Subsingleton A → Subsingleton ((T.normalizedRefinedInductionFunctor B S).obj A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A hA
  let := hA
  change Subsingleton (Induction.SmoothFunctions _ _)
  infer_instance

/-- A geometric piece vanishes when its source refinement is proper and
its inducing representation is quasicuspidal. -/
theorem geometricPieceFunctor_subsingleton_of_proper_source {n : ℕ}
    (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation →
      refinedParabolic F.Carrier B S ≠ ⊤ →
      Subsingleton ((geometricPieceFunctor T B C w S R hS hR).obj A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A hA hproper
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  have hJ : Subsingleton J := hA S hproper
  let := hJ
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  have hJ' : Subsingleton J' := subgroupEqualityFunctor_subsingleton _ _ _ J
  let := hJ'
  let W := (intersectionTransportFunctor F.Carrier B C w).obj J'
  have hW : Subsingleton W := hJ'
  let := hW
  let W' := (subgroupEqualityFunctor _ _ hR).obj W
  have hW' : Subsingleton W' := subgroupEqualityFunctor_subsingleton _ _ _ W
  exact normalizedRefinedInductionFunctor_subsingleton F T C R W' hW'

/-- An actual smooth subquotient of a zero representation has zero carrier. -/
theorem subsingleton_of_isSubquotient {R G : Type*} [CommRing R] [Group G]
    [TopologicalSpace G] {A D : SmoothRep.{_, _, uV} R G}
    (h : SmoothRep.IsSubquotient D A) [Subsingleton A] : Subsingleton D := by
  obtain ⟨S, Q, ⟨e⟩⟩ := h
  let : Subsingleton (SmoothRep.subrepresentation A S) :=
    (SmoothRep.subtype_injective A S).subsingleton
  let : Subsingleton (SmoothRep.subquotient A S Q) := by
    exact (Submodule.mkQ_surjective Q.toSubmodule).subsingleton
  exact (SmoothRep.equivOfIso e).toLinearEquiv.injective.subsingleton

/-- Evaluate the actual natural filtration at a single source object. -/
def objectFiltrationAt {R G : Type*} [CommRing R] [Monoid G]
    {C : Type*} [Category C] {H : C ⥤ Rep.{uV} R G} {m : ℕ}
    (s : RepFunctorFiltration H m) (X : C) : ObjectRepFiltration (H.obj X) m :=
  ObjectRepFiltration.ofSubrepresentations (fun i => (s.step i).obj X)
    (s.monotone X) (s.zero X) (s.top X)

/-- Evaluation uses exactly the original actual quotient carrier and action. -/
theorem objectFiltrationAt_graded {R G : Type*} [CommRing R] [Monoid G]
    {C : Type*} [Category C] {H : C ⥤ Rep.{uV} R G} {m : ℕ}
    (s : RepFunctorFiltration H m) (X : C) (i : Fin m) :
    (objectFiltrationAt s X).gradedRepresentation i = (s.graded i).obj X := rfl

end Langlands.CuspidalSupport
