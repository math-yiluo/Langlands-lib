import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.CuspidalSupport.LeviCuspidalContragredientProof
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof

/-!
# The cuspidal constituent piece from product-Levi localization

The product-Levi localization piece, applied to the inner induction of an
irreducible cuspidal representation `ω`, places an irreducible cuspidal
subquotient in one transported inner opposite Jacquet module of `ω`. A proper
refinement gives a zero module, because `ω` is cuspidal; the full refinement
gives the transport of `ω` itself, and irreducibility turns the subquotient into
an equivalence.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison WeylBranchPieces

universe uF uV uW

namespace CuspidalInductionConstituent

section Subquotients

variable {G : Type*} [Group G] {V W : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A zero representation has no nonzero subquotient. -/
theorem not_isSubquotient_of_subsingleton (A : Representation ℂ G V)
    (X : Representation ℂ G W) (hV : Subsingleton V) (hW : Nontrivial W) :
    ¬ IsSubquotient A X := by
  rintro ⟨U, q, hq⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  obtain ⟨u, rfl⟩ := hq a
  obtain ⟨u', rfl⟩ := hq b
  exact hab (congrArg q (Subtype.ext (Subsingleton.elim _ _)))

/-- An irreducible subquotient of an irreducible representation is equivalent
to it. -/
theorem nonempty_equiv_of_isSubquotient {A : Representation ℂ G V}
    {X : Representation ℂ G W} (hA : A.IsIrreducible) (hX : X.IsIrreducible)
    (h : IsSubquotient A X) : Nonempty (X.Equiv A) := by
  obtain ⟨U, q, hq⟩ := h
  have hW : Nontrivial W :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible X hX
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  have hU : U = ⊤ := by
    rcases hA.eq_bot_or_eq_top U with hb | ht
    · exfalso
      subst hb
      have hzero : ∀ u : (⊥ : Subrepresentation A).toSubmodule, u = 0 := fun u =>
        Subtype.ext ((Submodule.mem_bot ℂ).mp u.property)
      obtain ⟨u, rfl⟩ := hq a
      obtain ⟨u', rfl⟩ := hq b
      exact hab (by rw [hzero u, hzero u'])
    · exact ht
  subst hU
  let j : A.IntertwiningMap (⊤ : Subrepresentation A).toRepresentation :=
    { toLinearMap := LinearMap.codRestrict (⊤ : Subrepresentation A).toSubmodule
        LinearMap.id (fun v => Submodule.mem_top)
      isIntertwining' := fun _ => rfl }
  let f : A.IntertwiningMap X := q.comp j
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨u, hu⟩ := hq x
    exact ⟨u.val, hu⟩
  have hf0 : f ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hf a
    obtain ⟨v', hv'⟩ := hf b
    rw [h0] at hv hv'
    exact hab (hv.symm.trans hv')
  have := hA
  have := hX
  exact ⟨(f.ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf0)).symm⟩

end Subquotients

section Geometry

variable {F : Type uF} [Field F] {n : ℕ} (C : BlockShape n) (S : BlockRefinement C)

/-- A full refinement has trivial opposite refined radical. -/
theorem refinedOppositeUnipotent_eq_bot_of_full (h : refinedParabolic F C S = ⊤) :
    refinedOppositeUnipotent F C S = ⊥ := by
  have hrev : refinedParabolic F C (ProductLeviDualOpposite.reverseRefinement C S) = ⊤ := by
    by_contra hne
    exact ((CuspidalSupport.innerReverseRefinement_refinedParabolic_ne_top_iff F C S).mp hne) h
  have hbot : refinedUnipotent F C (ProductLeviDualOpposite.reverseRefinement C S) = ⊥ :=
    CuspidalSupport.refinedUnipotent_eq_bot_of_full C _
      (CuspidalSupport.refinedLevi_eq_top_of_refinedParabolic_eq_top C _ hrev)
  rw [← CuspidalSupport.innerReverseRefinement_refinedUnipotent_map_conj, hbot,
    Subgroup.map_bot]

/-- A full refinement leaves the embedded Levi subgroup unchanged. -/
theorem flatten_leviSubgroup_of_full (h : refinedParabolic F C S = ⊤) :
    (C.flatten S).leviSubgroup F = C.leviSubgroup F := by
  have hL := CuspidalSupport.refinedLevi_eq_top_of_refinedParabolic_eq_top C S h
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨(flattenedLeviEquiv F C S m).val, flattenedLeviEquiv_embedding F C S m⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(flattenedLeviEquiv F C S).symm ⟨m, hL ▸ Subgroup.mem_top m⟩,
      flattenedLeviEquiv_symm_embedding F C S _⟩

/-- A permutation conjugating the flattened Levi of a full refinement conjugates
the original Levi. -/
theorem conjugatesLevi_of_full {E : BlockShape n} (h : refinedParabolic F C S = ⊤)
    (g : Equiv.Perm (Fin n))
    (hg : CuspidalSupport.ConjugatesLevi (F := F) (C.flatten S) E g) :
    CuspidalSupport.ConjugatesLevi (F := F) C E g := by
  unfold CuspidalSupport.ConjugatesLevi at hg ⊢
  rwa [flatten_leviSubgroup_of_full C S h] at hg

/-- For a full refinement, the two inverse conjugations agree after the
flattened identification. -/
theorem flattenedLeviEquiv_leviConjugation_symm {E : BlockShape n}
    (h : refinedParabolic F C S = ⊤) (g : Equiv.Perm (Fin n))
    (hg : CuspidalSupport.ConjugatesLevi (F := F) (C.flatten S) E g) (m : E.Levi F) :
    (flattenedLeviEquiv F C S
        ((CuspidalSupport.leviConjugation (C.flatten S) E g hg).symm m)).val =
      (CuspidalSupport.leviConjugation C E g (conjugatesLevi_of_full C S h g hg)).symm m := by
  apply C.leviEmbedding_injective F
  rw [flattenedLeviEquiv_embedding, CuspidalSupport.leviConjugation_symm_embedding,
    CuspidalSupport.leviConjugation_symm_embedding]

end Geometry

section Vanishing

variable {F : Type uF} [Field F] {n : ℕ} (C : BlockShape n) (S : BlockRefinement C)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Quasicuspidality kills the opposite coinvariants of every proper refinement. -/
theorem refinedOppositeJacquet_subsingleton (ω : Representation ℂ (C.Levi F) V)
    (hω : CuspidalSupport.IsLeviQuasicuspidal C ω) (hS : refinedParabolic F C S ≠ ⊤) :
    Subsingleton (RefinedOppositeJacquetModule C S ω) := by
  have hrev := hω (ProductLeviDualOpposite.reverseRefinement C S)
    ((CuspidalSupport.innerReverseRefinement_refinedParabolic_ne_top_iff F C S).mpr hS)
  have hopp := (Jacquet.coinvariants_conj_subsingleton_iff ω _
    (ProductLeviDualOpposite.reverseWeyl C S F)).mpr hrev
  rwa [CuspidalSupport.innerReverseRefinement_refinedUnipotent_map_conj] at hopp

/-- For a full refinement the opposite quotient map is a linear equivalence. -/
def fullOppositeJacquetLinearEquiv (h : refinedParabolic F C S = ⊤)
    (ω : Representation ℂ (C.Levi F) V) :
    V ≃ₗ[ℂ] RefinedOppositeJacquetModule C S ω := by
  let N := refinedOppositeUnipotent F C S
  have hN : N = ⊥ := refinedOppositeUnipotent_eq_bot_of_full C S h
  let f : RefinedOppositeJacquetModule C S ω →ₗ[ℂ] V := Jacquet.lift ω N LinearMap.id (by
    intro u
    have hu : (u : C.Levi F) = 1 := by
      simpa only [hN, Subgroup.mem_bot] using u.property
    ext v
    simp [hu])
  exact
    { refinedOppositeJacquetMk C S ω with
      invFun := f
      left_inv := fun v => rfl
      right_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ω N x
        rfl }

end Vanishing

section FullPiece

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (C E : BlockShape n) (S : BlockRefinement C)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The transported full inner opposite Jacquet module is the transport of the
representation itself. -/
def fullTransportEquiv (h : refinedParabolic F.Carrier C S = ⊤)
    (g : Equiv.Perm (Fin n))
    (hg : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (C.flatten S) E g)
    (ω : Representation ℂ (C.Levi F.Carrier) V) :
    (CuspidalSupport.transport C E g (conjugatesLevi_of_full C S h g hg) ω).Equiv
      (CuspidalSupport.transport (C.flatten S) E g hg
        ((T.normalizedRefinedOppositeJacquet C S ω).comp
          (flattenedLeviEquiv F.Carrier C S).toMonoidHom)) := by
  have hL := CuspidalSupport.refinedLevi_eq_top_of_refinedParabolic_eq_top C S h
  refine Representation.Equiv.mk (fullOppositeJacquetLinearEquiv C S h ω) ?_
  intro m
  apply LinearMap.ext
  intro v
  let k := flattenedLeviEquiv F.Carrier C S
    ((CuspidalSupport.leviConjugation (C.flatten S) E g hg).symm m)
  change refinedOppositeJacquetMk C S ω
      (ω ((CuspidalSupport.leviConjugation C E g
        (conjugatesLevi_of_full C S h g hg)).symm m) v) =
    T.normalizedRefinedOppositeJacquet C S ω k (refinedOppositeJacquetMk C S ω v)
  rw [T.normalizedRefinedOppositeJacquet_mk,
    CuspidalSupport.refinedHalfModulus_eq_one_of_full T C S hL, one_smul,
    flattenedLeviEquiv_leviConjugation_symm C S h g hg m]

end FullPiece

end CuspidalInductionConstituent

open CuspidalInductionConstituent

/-- The cuspidal constituent piece follows from the product-Levi localization
piece applied with coarse shape `D`, middle refinement `R` and `σ := ω`. -/
theorem glCuspidalInductionJacquetConstituent_of_localization
    (hloc : GLProductLeviCuspidalLocalizationStatement.{uF, uW, uV}) :
    GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uW} := by
  intro p _ F T
  let _ := T.topology
  intro n hn D R R' ω hωirr hωcusp ρ hρirr hρcusp hsub
  obtain ⟨g, hgW, R'', hg, -, hsub'⟩ :=
    hloc p F T n hn D R ω hωcusp.1.1 R' ρ hρirr hρcusp hsub
  have hρnt : Nontrivial ρ :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible ρ.ρ hρirr
  by_cases hfull : refinedParabolic F.Carrier (D.flatten R) R'' = ⊤
  · have hh := conjugatesLevi_of_full (D.flatten R) R'' hfull g hg
    refine ⟨g, hgW, hh, ?_⟩
    have hY := (CuspidalSupport.isIrreducible_transport g hh ω.ρ).mpr hωirr
    exact nonempty_equiv_of_isSubquotient hY hρirr (IsSubquotient.of_equiv_left
      (fullTransportEquiv T (D.flatten R) (D.flatten R') R'' hfull g hg ω.ρ) hsub')
  · exact absurd hsub' (not_isSubquotient_of_subsingleton _ _
      (refinedOppositeJacquet_subsingleton (D.flatten R) R'' ω.ρ hωcusp.2 hfull) hρnt)

end Langlands
