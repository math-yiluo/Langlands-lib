import Langlands.Representation.Classification.SegmentHeadSupportGeneric
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor
import Langlands.Representation.Smooth.ConstituentSupport
import Langlands.Representation.Category.RestrictionSubquotients
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Tensor.ExternalSubquotient

/-!
# Generic tools for the analysis of geometric pieces

* An irreducible subquotient of the image of a finite-length representation under a functor
  preserving short exact sequences of finite-length representations comes from an irreducible
  subquotient of the source.
* Restriction of smooth representations along a continuous homomorphism, as a functor.
* Restriction of an external tensor product to one coordinate group.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open WeylBranchPieces

universe uG uH uV uW uI

section Extraction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- A functor preserving short exact sequences of finite-length representations sends a
finite-length representation with subsingleton carrier to a subsingleton. -/
theorem subsingleton_map_of_preservesFiniteLengthShortExact
    {Φ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H}
    (hΦ : SmoothRep.PreservesFiniteLengthShortExact Φ) {Z : SmoothRep.{0, uG, uV} ℂ G}
    (hZl : Z.HasFiniteLength) (hZ : Subsingleton Z) :
    Subsingleton (Φ.obj Z) := by
  have hex : LinearMap.range (SmoothRep.hom (𝟙 Z)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (𝟙 Z)).toLinearMap := by
    ext x
    exact ⟨fun _ => LinearMap.mem_ker.mpr (Subsingleton.elim _ _), fun _ => ⟨x, rfl⟩⟩
  obtain ⟨-, -, hΦex⟩ := hΦ (𝟙 Z) (𝟙 Z) hZl hZl hZl
    ⟨fun x y _ => Subsingleton.elim x y, fun x => ⟨x, rfl⟩, hex⟩
  rw [Φ.map_id] at hΦex
  have hzero : ∀ x : Φ.obj Z, x = 0 := fun x => by
    have hx : x ∈ LinearMap.ker (SmoothRep.hom (𝟙 (Φ.obj Z))).toLinearMap :=
      hΦex ▸ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mp hx
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- An irreducible subquotient of the image, under a functor preserving short exact sequences
of finite-length representations, of a finite-length representation `Z` is a subquotient of
the image of an irreducible subquotient of `Z`. -/
theorem exists_irreducible_of_isSubquotient_map_of_finiteLength
    {Φ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H}
    (hΦ : SmoothRep.PreservesFiniteLengthShortExact Φ) {Z : SmoothRep.{0, uG, uV} ℂ G}
    (hZ : Z.HasFiniteLength)
    {X : SmoothRep.{0, uH, uW} ℂ H} (hX : X.IsIrreducible)
    (h : SmoothRep.IsSubquotient X (Φ.obj Z)) :
    ∃ τ : SmoothRep.{0, uG, uV} ℂ G, τ.IsIrreducible ∧ SmoothRep.IsSubquotient τ Z ∧
      SmoothRep.IsSubquotient X (Φ.obj τ) := by
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hZ
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Z.representation)
  let S : Fin (s.length + 1) → Subrepresentation Z.representation := fun i => e.symm (s i)
  have hcov : ∀ i : Fin s.length, S i.castSucc ⋖ S i.succ := fun i =>
    (apply_covBy_apply_iff e.symm).mpr (s.step i)
  have hfl : ∀ i, (SmoothRep.subrepresentation Z (S i)).HasFiniteLength := fun i =>
    SmoothRep.hasFiniteLength_of_isSubquotient hZ
      (SmoothRep.subrepresentation_isSubrepresentation (S i)).isSubquotient
  have key : ∀ i : Fin (s.length + 1),
      SmoothRep.IsSubquotient X (Φ.obj (SmoothRep.subrepresentation Z (S i))) →
      ∃ τ : SmoothRep.{0, uG, uV} ℂ G, τ.IsIrreducible ∧ SmoothRep.IsSubquotient τ Z ∧
        SmoothRep.IsSubquotient X (Φ.obj τ) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro hsq
      exfalso
      have hS : S 0 = ⊥ := by
        change e.symm s.head = ⊥
        rw [h₀]
        exact e.symm.map_bot
      have hmem : ∀ v, v ∈ S 0 → v = 0 := by
        intro v hv
        rw [hS] at hv
        exact LengthCriterionProof.mem_bot_iff.mp hv
      have hsub : Subsingleton (SmoothRep.subrepresentation Z (S 0)) :=
        ⟨fun x y => Subtype.ext ((hmem _ x.2).trans (hmem _ y.2).symm)⟩
      have hXs := SegmentHeadSupport.subsingleton_of_isSubquotient hsq
        (subsingleton_map_of_preservesFiniteLengthShortExact hΦ (hfl 0) hsub)
      exact (SegmentHeadSupport.nontrivial_of_isIrreducible hX).exists_pair_ne.elim
        fun x hx => hx.elim fun y hxy => hxy (Subsingleton.elim x y)
    | succ i ih =>
      intro hsq
      have hle : S i.castSucc ≤ S i.succ := (hcov i).le
      let A := SmoothRep.subrepresentation Z (S i.castSucc)
      let B := SmoothRep.subrepresentation Z (S i.succ)
      let U : Subrepresentation B.representation :=
        { toSubmodule := LengthCriterionProof.lower (S i.castSucc) (S i.succ)
          apply_mem_toSubmodule := fun g _ hv =>
            (S i.castSucc).apply_mem_toSubmodule g hv }
      let Q := SmoothRep.quotient B U
      let j : A ⟶ B := SmoothRep.ofHom
        { toLinearMap := Submodule.inclusion hle
          isIntertwining' := fun g => by ext v; rfl }
      let q : B ⟶ Q := SmoothRep.mkQ B U
      have hj : Function.Injective (SmoothRep.hom j) := Submodule.inclusion_injective hle
      have hq : Function.Surjective (SmoothRep.hom q) := SmoothRep.mkQ_surjective B U
      have hex : LinearMap.range (SmoothRep.hom j).toLinearMap =
          LinearMap.ker (SmoothRep.hom q).toLinearMap := by
        ext v
        change (∃ w : (S i.castSucc).toSubmodule, Submodule.inclusion hle w = v) ↔
          Submodule.Quotient.mk (p := U.toSubmodule) v = 0
        rw [Submodule.Quotient.mk_eq_zero]
        constructor
        · rintro ⟨w, rfl⟩
          exact w.property
        · intro hv
          exact ⟨⟨v.1, hv⟩, rfl⟩
      have hQsq : SmoothRep.IsSubquotient Q Z := ⟨S i.succ, U, ⟨Iso.refl _⟩⟩
      have hQl : Q.HasFiniteLength := SmoothRep.hasFiniteLength_of_isSubquotient hZ hQsq
      obtain ⟨-, -, hΦex⟩ := hΦ j q (hfl _) (hfl _) hQl ⟨hj, hq, hex⟩
      rcases SegmentHeadSupport.smooth_isSubquotient_or_of_exact hX (Φ.map j) (Φ.map q)
          hΦex hsq with hA | hQ
      · exact ih hA
      · refine ⟨Q, ?_, hQsq, hQ⟩
        exact (LengthCriterionProof.isIrreducible_quotientRep_iff hle).mpr (hcov i)
  have hS : S (Fin.last s.length) = ⊤ := by
    change e.symm s.last = ⊤
    rw [h₁]
    exact e.symm.map_top
  have key' := key (Fin.last s.length)
  rw [hS] at key'
  let eZ : SmoothRep.subrepresentation Z ⊤ ≅ Z :=
    SmoothRep.mkIso (Representation.Equiv.mk Submodule.topEquiv (fun g => by ext v; rfl))
  exact key' (SmoothRep.IsSubquotient.of_iso_right h (Φ.mapIso eZ).symm)

end Extraction

section Restriction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- Restriction of smooth representations along a continuous homomorphism. -/
def restrictionFunctor (φ : H →* G) (hφ : Continuous φ) :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H where
  obj A := SmoothRep.of (A.representation.comp φ)
    (Langlands.isSmooth_comp φ hφ A.isSmooth)
  map f := SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom f).toLinearMap
      isIntertwining' := fun h => (SmoothRep.hom f).isIntertwining' (φ h) }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem restrictionFunctor_obj_representation (φ : H →* G) (hφ : Continuous φ)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    ((restrictionFunctor φ hφ).obj A).representation = A.representation.comp φ := rfl

/-- Restriction keeps the underlying linear maps, so it preserves short exact sequences. -/
theorem restrictionFunctor_preservesFiniteLengthShortExact (φ : H →* G) (hφ : Continuous φ) :
    SmoothRep.PreservesFiniteLengthShortExact (restrictionFunctor.{uG, uH, uV} φ hφ) := by
  intro A B C f g _ _ _ h
  exact h

end Restriction

section Slot

variable {ι : Type uI} [Fintype ι] [DecidableEq ι] {H : ι → Type uG} [∀ i, Group (H i)]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {X : Type uW} [AddCommGroup X] [Module ℂ X]

omit [Fintype ι] in
/-- An irreducible subquotient of the restriction of an external tensor product to one
coordinate group is a subquotient of that coordinate's factor. -/
theorem isSubquotient_factor_of_external_comp_mulSingle
    (J : ∀ i, Representation ℂ (H i) (V i)) (k : ι)
    (ρ : Representation ℂ (H k) X) (hρ : ρ.IsIrreducible)
    (h : IsSubquotient ((FiniteTensor.external J).comp (MonoidHom.mulSingle H k)) ρ) :
    IsSubquotient (J k) ρ := by
  have := hρ
  have h0 : IsSubquotient (FiniteTensor.action (FiniteTensor.slotRestriction J k)) ρ := h
  have h1 := IsSubquotient.of_equiv_left
    (FiniteTensor.slotEquiv (FiniteTensor.slotRestriction J k) k).symm h0
  have h3 := FiniteTensor.isSubquotient_of_tprod_trivial _
    (FiniteTensor.action_slotRestriction_compl J k) _ h1
  rwa [FiniteTensor.slotRestriction_self J k] at h3

/-- In an external tensor product of nonzero factors, each factor is a subquotient of the
restriction to its coordinate group. -/
theorem isSubquotient_external_comp_mulSingle (ρ : ∀ i, Representation ℂ (H i) (V i))
    (hV : ∀ i, Nontrivial (V i)) (k : ι) :
    IsSubquotient ((FiniteTensor.external ρ).comp (MonoidHom.mulSingle H k)) (ρ k) := by
  have h0 : IsSubquotient ((FiniteTensor.external ρ).comp (MonoidHom.mulSingle H k))
      (FiniteTensor.action (FiniteTensor.slotRestriction ρ k)) :=
    IsSubquotient.refl _
  have h1 := h0.of_equiv_right (FiniteTensor.slotEquiv (FiniteTensor.slotRestriction ρ k) k)
  have hV' : Nontrivial (PiTensorProduct ℂ (fun i : ({k}ᶜ : Set ι) => V i)) :=
    FiniteTensor.nontrivial_piTensorProduct fun i => hV i
  obtain ⟨m, hm⟩ := exists_ne (0 : PiTensorProduct ℂ (fun i : ({k}ᶜ : Set ι) => V i))
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hm
  have h2 := h1.trans (IsSubquotient.of_surjective
    (FiniteTensor.trivialContraction _ (FiniteTensor.action_slotRestriction_compl ρ k) _ φ)
    (FiniteTensor.trivialContraction_surjective _
      (FiniteTensor.action_slotRestriction_compl ρ k) _ φ hφ))
  rwa [FiniteTensor.slotRestriction_self ρ k] at h2

end Slot

end Langlands.Classification.LeftCuspidalDerivative
