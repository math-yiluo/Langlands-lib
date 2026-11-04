import Langlands.CategoryTheory.RenardCategoryDecomposition
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! Actual coproducts and irreducible-subquotient factors of natural projectors. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual kernel and range, with the range indexed by `true`. -/
def idempotentComponents (A : SmoothRep.{0, uG, uV} ℂ G)
    (p : A.representation.IntertwiningMap A.representation) :
    Bool → SmoothRep.{0, uG, uV} ℂ G
  | false => subrepresentation A p.ker
  | true => subrepresentation A p.range

/-- The actual inclusions of the kernel and range. -/
def idempotentCofan (A : SmoothRep.{0, uG, uV} ℂ G)
    (p : A.representation.IntertwiningMap A.representation) :
    Cofan (idempotentComponents A p) :=
  Cofan.mk A (fun b => match b with
    | false => subtype A p.ker
    | true => subtype A p.range)

private def toRange {A : SmoothRep.{0, uG, uV} ℂ G}
    (p : A.representation.IntertwiningMap A.representation) :
    A ⟶ subrepresentation A p.range :=
  ofHom {
    toLinearMap := p.toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext v
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ p g v) }

private def toKernel {A : SmoothRep.{0, uG, uV} ℂ G}
    (p : A.representation.IntertwiningMap A.representation)
    (hp : ∀ v : A, p (p v) = p v) :
    A ⟶ subrepresentation A p.ker :=
  ofHom {
    toLinearMap := (LinearMap.id - p.toLinearMap).codRestrict p.ker.toSubmodule
      (by intro v; change p (v - p v) = 0; rw [map_sub, hp, sub_self])
    isIntertwining' g := by
      ext v
      apply Subtype.ext
      change A.representation g v - p (A.representation g v) =
        A.representation g (v - p v)
      rw [map_sub, Representation.IntertwiningMap.isIntertwining _ _ p g v] }

/-- An idempotent intertwiner presents the ambient object as the actual
coproduct of its kernel and range. -/
def idempotentCofanIsColimit (A : SmoothRep.{0, uG, uV} ℂ G)
    (p : A.representation.IntertwiningMap A.representation)
    (hp : ∀ v : A, p (p v) = p v) :
    IsColimit (idempotentCofan A p) := by
  refine Cofan.IsColimit.mk _ (fun s =>
    toRange p ≫ s.inj true + toKernel p hp ≫ s.inj false) ?_ ?_
  · intro s b
    cases b
    · ext v
      change hom (s.inj true) ⟨p v.val, _⟩ +
        hom (s.inj false) ⟨v.val - p v.val, _⟩ = hom (s.inj false) v
      have hv : p v.val = 0 := v.property
      simp only [hv, sub_zero]
      change hom (s.inj true) 0 + hom (s.inj false) v = _
      rw [map_zero, zero_add]
    · ext v
      change hom (s.inj true) ⟨p v.val, _⟩ +
        hom (s.inj false) ⟨v.val - p v.val, _⟩ = hom (s.inj true) v
      obtain ⟨w, hw⟩ := v.property
      have hv : p v.val = v.val := by
        rw [← hw]
        exact hp w
      simp only [hv, sub_self]
      change hom (s.inj true) v + hom (s.inj false) 0 = _
      rw [map_zero, add_zero]
  · intro s m hm
    change A ⟶ s.pt at m
    ext v
    have ht := congrArg (fun f => hom f (hom (toRange p) v)) (hm true)
    have hf := congrArg (fun f => hom f (hom (toKernel p hp) v)) (hm false)
    change hom m (p v) = hom (s.inj true) (hom (toRange p) v) at ht
    change hom m (v - p v) = hom (s.inj false) (hom (toKernel p hp) v) at hf
    change hom m v = hom (s.inj true) (hom (toRange p) v) +
      hom (s.inj false) (hom (toKernel p hp) v)
    rw [← ht, ← hf, ← map_add, add_sub_cancel]

/-- All or none of the actual irreducible subquotients satisfy `P`. -/
def irreducibleSubquotientProperties
    (P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)) :
    Bool → ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)
  | false => fun A => ∀ D, D.IsIrreducible → IsSubquotient D A → ¬ P D
  | true => fun A => ∀ D, D.IsIrreducible → IsSubquotient D A → P D

private theorem scalar_action_on_subquotient
    (e : ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      A.representation.IntertwiningMap A.representation)
    (hnat : ∀ (A B : SmoothRep.{0, uG, uV} ℂ G) (f : A ⟶ B) (v : A),
      e B (hom f v) = hom f (e A v))
    (a : ℂ) {A D : SmoothRep.{0, uG, uV} ℂ G}
    (hA : ∀ v : A, e A v = a • v) (hDA : IsSubquotient D A) :
    ∀ v : D, e D v = a • v := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hDA
  have hC : ∀ v : C, e C v = a • v := by
    intro v
    apply hi
    rw [← hnat C A i v, hA, map_smul]
  intro v
  obtain ⟨w, rfl⟩ := hq v
  rw [hnat C D q w, hC, map_smul]

private theorem not_irreducible_of_fixed_and_zero
    {D : SmoothRep.{0, uG, uV} ℂ G}
    (p : D.representation.IntertwiningMap D.representation)
    (hfix : ∀ v : D, p v = v) (hzero : ∀ v : D, p v = 0) :
    ¬ D.IsIrreducible := by
  intro hD
  let : D.representation.IsIrreducible := hD
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) D.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  exact hv ((hfix v).symm.trans (hzero v))

/-- The two constituent conditions force every morphism in either
off-diagonal direction to vanish, even for objects of infinite length. -/
theorem irreducibleSubquotientProperties_offDiagonalHomsZero
    (P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)) :
    Renard.OffDiagonalHomsZero (irreducibleSubquotientProperties P) := by
  intro b c hbc A B hA hB f
  by_contra hf
  have hv : ∃ v : A, hom f v ≠ 0 := by
    by_contra hn
    apply hf
    ext v
    exact Classical.not_not.mp (not_exists.mp hn v)
  obtain ⟨v, hv⟩ := hv
  let I := image f
  have hI : Nontrivial I :=
    ⟨⟨⟨hom f v, ⟨v, rfl⟩⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  let q : A ⟶ I := ofHom {
    toLinearMap := (hom f).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext w
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g w) }
  have hIA : IsSubquotient I A :=
    isSubquotient_iff_exists.mpr ⟨A, 𝟙 A, q, Function.injective_id,
      LinearMap.surjective_rangeRestrict _⟩
  have hIB : IsSubquotient I B :=
    (subrepresentation_isSubrepresentation (hom f).range).isSubquotient
  obtain ⟨D, hD, hDI⟩ := exists_isIrreducible_isSubquotient_of_nontrivial I
  have hDA := Langlands.smoothSubquotientTransitivity ℂ G A I D hDI hIA
  have hDB := Langlands.smoothSubquotientTransitivity ℂ G B I D hDI hIB
  cases b <;> cases c
  · exact hbc rfl
  · exact hA D hD hDA (hB D hD hDB)
  · exact hB D hD hDB (hA D hD hDA)
  · exact hbc rfl

/-- A natural idempotent classified on irreducibles yields the full
all/no-irreducible-subquotient category decomposition. -/
theorem categoryDecomposition_of_natural_idempotent
    (P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G))
    (e : ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      A.representation.IntertwiningMap A.representation)
    (hnat : ∀ (A B : SmoothRep.{0, uG, uV} ℂ G) (f : A ⟶ B) (v : A),
      e B (hom f v) = hom f (e A v))
    (hid : ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (v : A), e A (e A v) = e A v)
    (htest : ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible →
      ((∀ v : D, e D v = v) ↔ P D)) :
    Renard.IsCategoryDecomposition (irreducibleSubquotientProperties P) := by
  refine ⟨?_, irreducibleSubquotientProperties_offDiagonalHomsZero P⟩
  intro A
  refine ⟨idempotentComponents A (e A), (idempotentCofan A (e A)).inj, ?_,
    ⟨idempotentCofanIsColimit A (e A) (hid A)⟩⟩
  have hrange : ∀ v : subrepresentation A (e A).range,
      e (subrepresentation A (e A).range) v = v := by
    intro v
    apply subtype_injective A (e A).range
    rw [← hnat _ A (subtype A (e A).range)]
    obtain ⟨w, hw⟩ := v.property
    change e A v.val = v.val
    rw [← hw]
    exact hid A w
  have hker : ∀ v : subrepresentation A (e A).ker,
      e (subrepresentation A (e A).ker) v = 0 := by
    intro v
    apply subtype_injective A (e A).ker
    rw [← hnat _ A (subtype A (e A).ker), map_zero]
    exact v.property
  intro b
  cases b
  · change ∀ D, D.IsIrreducible →
      IsSubquotient D (subrepresentation A (e A).ker) → ¬ P D
    intro D hD hDA hP
    have hzero : ∀ v : D, e D v = 0 := by
      simpa only [zero_smul] using
        scalar_action_on_subquotient e hnat 0
          (by simpa only [zero_smul] using hker) hDA
    exact not_irreducible_of_fixed_and_zero (e D) ((htest D hD).mpr hP) hzero hD
  · change ∀ D, D.IsIrreducible →
      IsSubquotient D (subrepresentation A (e A).range) → P D
    intro D hD hDA
    apply (htest D hD).mp
    simpa only [one_smul] using
      scalar_action_on_subquotient e hnat 1
        (by simpa only [one_smul] using hrange) hDA

end Langlands.SmoothRep
