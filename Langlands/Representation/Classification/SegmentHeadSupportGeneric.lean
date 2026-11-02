import Langlands.Representation.Tensor.SmoothSubquotients
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Parabolic.InductionExactnessProof
import Langlands.Representation.Shahidi.IntertwiningInduced
import Langlands.Representation.Filtration.LengthCriterionProof
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Generic subquotient tools for the support of segment-head derivatives

Composition of actual smooth subquotients, the location of an irreducible
subquotient in a short exact sequence, exactness of the binary normalized
product with a fixed first factor, and the passage from a finite-length second
factor to one of its irreducible subquotients.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.SegmentHeadSupport

open GeneralLinear WeylBranchPieces

universe uG uH uV uW uX uY uF

section Laws

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Actual smooth subquotients compose. -/
theorem isSubquotient_trans {A B C : SmoothRep.{0, uG, uV} ℂ G}
    (h₁ : SmoothRep.IsSubquotient A B) (h₂ : SmoothRep.IsSubquotient B C) :
    SmoothRep.IsSubquotient A C :=
  SmoothRep.isSubquotient_iff_representation.mpr
    ((SmoothRep.isSubquotient_iff_representation.mp h₂).trans
      (SmoothRep.isSubquotient_iff_representation.mp h₁))

/-- Every smooth representation is a subquotient of itself. -/
theorem isSubquotient_refl (A : SmoothRep.{0, uG, uV} ℂ G) : SmoothRep.IsSubquotient A A :=
  SmoothRep.isSubquotient_iff_representation.mpr (IsSubquotient.refl _)

/-- A subquotient of a representation with a subsingleton carrier has a
subsingleton carrier. -/
theorem subsingleton_of_isSubquotient {A B : SmoothRep.{0, uG, uV} ℂ G}
    (h : SmoothRep.IsSubquotient A B) (hB : Subsingleton B) : Subsingleton A := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  have hC : Subsingleton C := ⟨fun x y => hi (Subsingleton.elim _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hq x
  obtain ⟨y', rfl⟩ := hq y
  rw [Subsingleton.elim x' y']

/-- An irreducible representation has a nontrivial carrier. -/
theorem nontrivial_of_isIrreducible {A : SmoothRep.{0, uG, uV} ℂ G} (hA : A.IsIrreducible) :
    Nontrivial A :=
  IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) A.representation.asModule

end Laws

section ShortExact

variable {G : Type uG} [Group G]
  {U : Type uV} {V : Type uW} {W : Type uX} {Y : Type uY}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

/-- An irreducible actual subquotient of the middle term of a short exact
sequence is an actual subquotient of its kernel or of its cokernel. -/
theorem isSubquotient_or_of_exact {A : Representation ℂ G U} {B : Representation ℂ G V}
    {C : Representation ℂ G W} {X : Representation ℂ G Y} [X.IsIrreducible]
    (i : A.IntertwiningMap B) (q : B.IntertwiningMap C)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (h : IsSubquotient B X) : IsSubquotient A X ∨ IsSubquotient C X := by
  obtain ⟨S, f, hf⟩ := h
  by_cases hz : ∀ u : S.toSubmodule, q (u : V) = 0 → f u = 0
  · right
    let R : Subrepresentation C :=
      { toSubmodule := S.toSubmodule.map q.toLinearMap
        apply_mem_toSubmodule := by
          rintro g _ ⟨v, hv, rfl⟩
          exact ⟨B g v, S.apply_mem_toSubmodule g hv,
            Representation.IntertwiningMap.isIntertwining _ _ q g v⟩ }
    let qS : S.toRepresentation.IntertwiningMap R.toRepresentation :=
      { toLinearMap :=
          { toFun := fun u => ⟨q (u : V), u, u.2, rfl⟩
            map_add' := fun a b => Subtype.ext (map_add q (a : V) b)
            map_smul' := fun c a => Subtype.ext (map_smul q c (a : V)) }
        isIntertwining' := fun g => by
          ext u
          exact Representation.IntertwiningMap.isIntertwining _ _ q g (u : V) }
    have hqS : Function.Surjective qS := by
      rintro ⟨_, v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    have hker : qS.toLinearMap.ker ≤ f.toLinearMap.ker := by
      intro u hu
      have hu' : q (u : V) = 0 := congrArg Subtype.val hu
      exact hz u hu'
    obtain ⟨d, hd⟩ := exists_descend qS f hqS hker
    refine ⟨R, d, fun y => ?_⟩
    obtain ⟨u, rfl⟩ := hf y
    exact ⟨qS u, hd u⟩
  · left
    push Not at hz
    obtain ⟨u, hqu, hfu⟩ := hz
    let P : Subrepresentation A :=
      { toSubmodule := S.toSubmodule.comap i.toLinearMap
        apply_mem_toSubmodule := by
          intro g a ha
          change i (A g a) ∈ S.toSubmodule
          rw [Representation.IntertwiningMap.isIntertwining _ _ i g a]
          exact S.apply_mem_toSubmodule g ha }
    let iP : P.toRepresentation.IntertwiningMap S.toRepresentation :=
      { toLinearMap :=
          { toFun := fun a => ⟨i (a : U), a.2⟩
            map_add' := fun a b => Subtype.ext (map_add i (a : U) b)
            map_smul' := fun c a => Subtype.ext (map_smul i c (a : U)) }
        isIntertwining' := fun g => by
          ext a
          exact Representation.IntertwiningMap.isIntertwining _ _ i g (a : U) }
    have hfi : Function.Surjective (f.comp iP) := by
      refine (Representation.IsIrreducible.surjective_or_eq_zero (f.comp iP)).resolve_right ?_
      intro h0
      have hmem : (u : V) ∈ LinearMap.range i.toLinearMap := by
        rw [hex]
        exact hqu
      obtain ⟨a, ha⟩ := hmem
      have haP : a ∈ P.toSubmodule := by
        change i a ∈ S.toSubmodule
        rw [show i a = (u : V) from ha]
        exact u.2
      apply hfu
      have hcomp : (f.comp iP) ⟨a, haP⟩ = 0 := by rw [h0]; rfl
      have hiP : iP ⟨a, haP⟩ = u := Subtype.ext ha
      rw [← hiP]
      exact hcomp
    exact ⟨P, f.comp iP, hfi⟩

end ShortExact

section SmoothShortExact

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The smooth form of `isSubquotient_or_of_exact`. -/
theorem smooth_isSubquotient_or_of_exact {A B C X : SmoothRep.{0, uG, uV} ℂ G}
    (hX : X.IsIrreducible) (i : A ⟶ B) (q : B ⟶ C)
    (hex : LinearMap.range (SmoothRep.hom i).toLinearMap =
      LinearMap.ker (SmoothRep.hom q).toLinearMap)
    (h : SmoothRep.IsSubquotient X B) :
    SmoothRep.IsSubquotient X A ∨ SmoothRep.IsSubquotient X C := by
  let : X.representation.IsIrreducible := hX
  rcases isSubquotient_or_of_exact (SmoothRep.hom i) (SmoothRep.hom q) hex
      (SmoothRep.isSubquotient_iff_representation.mp h) with h' | h'
  · exact Or.inl (SmoothRep.isSubquotient_iff_representation.mpr h')
  · exact Or.inr (SmoothRep.isSubquotient_iff_representation.mpr h')

end SmoothShortExact

section FiniteLength

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- A functor between smooth categories sends every short exact sequence of
actual intertwiners to a short exact sequence. -/
def PreservesShortExact
    (Φ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H) : Prop :=
  ∀ ⦃S P Q : SmoothRep.{0, uG, uV} ℂ G⦄ (i : S ⟶ P) (q : P ⟶ Q),
    Function.Injective (SmoothRep.hom i) → Function.Surjective (SmoothRep.hom q) →
    LinearMap.range (SmoothRep.hom i).toLinearMap =
      LinearMap.ker (SmoothRep.hom q).toLinearMap →
    Function.Injective (SmoothRep.hom (Φ.map i)) ∧
      LinearMap.range (SmoothRep.hom (Φ.map i)).toLinearMap =
        LinearMap.ker (SmoothRep.hom (Φ.map q)).toLinearMap ∧
      Function.Surjective (SmoothRep.hom (Φ.map q))

/-- An exact functor sends representations with subsingleton carriers to
representations with subsingleton carriers. -/
theorem PreservesShortExact.subsingleton
    {Φ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H}
    (hΦ : PreservesShortExact Φ) {Z : SmoothRep.{0, uG, uV} ℂ G} (hZ : Subsingleton Z) :
    Subsingleton (Φ.obj Z) := by
  have hex : LinearMap.range (SmoothRep.hom (𝟙 Z)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (𝟙 Z)).toLinearMap := by
    ext x
    exact ⟨fun _ => LinearMap.mem_ker.mpr (Subsingleton.elim _ _), fun _ => ⟨x, rfl⟩⟩
  obtain ⟨-, hΦex, -⟩ := hΦ (𝟙 Z) (𝟙 Z) (fun x y _ => Subsingleton.elim x y)
    (fun x => ⟨x, rfl⟩) hex
  rw [Φ.map_id] at hΦex
  have hzero : ∀ x : Φ.obj Z, x = 0 := fun x => by
    have hx : x ∈ LinearMap.ker (SmoothRep.hom (𝟙 (Φ.obj Z))).toLinearMap :=
      hΦex ▸ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mp hx
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- An actual irreducible subquotient of the image, under an exact functor, of a
finite-length representation `Z` is an actual subquotient of the image of an
actual irreducible subquotient of `Z`. -/
theorem exists_irreducible_of_isSubquotient_map
    {Φ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H}
    (hΦ : PreservesShortExact Φ) {Z : SmoothRep.{0, uG, uV} ℂ G} (hZ : Z.HasFiniteLength)
    {X : SmoothRep.{0, uH, uW} ℂ H} (hX : X.IsIrreducible)
    (h : SmoothRep.IsSubquotient X (Φ.obj Z)) :
    ∃ τ : SmoothRep.{0, uG, uV} ℂ G, τ.IsIrreducible ∧ SmoothRep.IsSubquotient τ Z ∧
      SmoothRep.IsSubquotient X (Φ.obj τ) := by
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hZ
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Z.representation)
  let S : Fin (s.length + 1) → Subrepresentation Z.representation := fun i => e.symm (s i)
  have hcov : ∀ i : Fin s.length, S i.castSucc ⋖ S i.succ := fun i =>
    (apply_covBy_apply_iff e.symm).mpr (s.step i)
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
      have hXs := subsingleton_of_isSubquotient hsq (hΦ.subsingleton hsub)
      exact (nontrivial_of_isIrreducible hX).exists_pair_ne.elim
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
      obtain ⟨-, hΦex, -⟩ := hΦ j q hj hq hex
      rcases smooth_isSubquotient_or_of_exact hX (Φ.map j) (Φ.map q) hΦex hsq with hA | hQ
      · exact ih hA
      · refine ⟨Q, ?_, ⟨S i.succ, U, ⟨Iso.refl _⟩⟩, hQ⟩
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

end FiniteLength

end Langlands.Classification.SegmentHeadSupport
