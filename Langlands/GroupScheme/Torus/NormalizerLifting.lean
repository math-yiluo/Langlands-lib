import Langlands.GroupScheme.Torus.TwistedLifting
import Langlands.GroupScheme.CorepresentedNormalizer
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.Dynamic.Representability
import Langlands.GroupScheme.Torus.AffineCharacterAction

/-! # Square-zero lifting for normalizers of embedded diagonalizable groups

For a group functor `F` corepresented by a formally smooth algebra and an embedded
diagonalizable group `ι`, the algebra-level normalizer family of the embedded characters has
the square-zero lifting property. A normalizing point over `C ⧸ N` conjugates the characters by a
grouplike family; this family lifts uniquely to `C`, and the point lifts as a twisted
transporter. Uniqueness of grouplike lifts shows that the lifted twist is invertible, so the
lift normalizes in both directions.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.CharacterAction

open Corepresented

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (ι : CharacterEmbedding F M)

/-- A point normalizing the embedded characters gives the conjugation hypothesis. -/
theorem exists_conj_of_mem_normalizerFamily {A : CommAlgCat.{u} R} {g : F.obj A}
    (hg : g ∈ normalizerFamily ι.range A) (D : CommAlgCat.{u} R) (f : A ⟶ D)
    (t : Multiplicative M →* Dˣ) :
    ∃ t', ι.hom D t' = F.map f g * ι.hom D t * (F.map f g)⁻¹ := by
  obtain ⟨t', ht'⟩ := (hg D f (ι.hom D t) ⟨t, rfl⟩).1
  exact ⟨t', ht'⟩

theorem exists_conj_inv_of_mem_normalizerFamily {A : CommAlgCat.{u} R} {g : F.obj A}
    (hg : g ∈ normalizerFamily ι.range A) (D : CommAlgCat.{u} R) (f : A ⟶ D)
    (t : Multiplicative M →* Dˣ) :
    ∃ t', ι.hom D t' = F.map f g⁻¹ * ι.hom D t * (F.map f g⁻¹)⁻¹ := by
  obtain ⟨t', ht'⟩ := (hg D f (ι.hom D t) ⟨t, rfl⟩).2
  refine ⟨t', ?_⟩
  rw [ht', map_inv, inv_inv]

/-- Conjugating by a normalizing point and then by its inverse is the identity on
characters. -/
theorem conjChar_conjChar {A : CommAlgCat.{u} R} {g : F.obj A}
    (hg : ∀ (D : CommAlgCat.{u} R) (f : A ⟶ D) (t : Multiplicative M →* Dˣ),
      ∃ t', ι.hom D t' = F.map f g * ι.hom D t * (F.map f g)⁻¹)
    (hg' : ∀ (D : CommAlgCat.{u} R) (f : A ⟶ D) (t : Multiplicative M →* Dˣ),
      ∃ t', ι.hom D t' = F.map f g⁻¹ * ι.hom D t * (F.map f g⁻¹)⁻¹)
    {D : CommAlgCat.{u} R} (f : A ⟶ D) (t : Multiplicative M →* Dˣ) :
    conjChar ι hg f (conjChar ι hg' f t) = t := by
  apply ι.injective D
  rw [hom_conjChar, hom_conjChar, map_inv]
  group

variable [Algebra.FormallySmooth R B]

include e in
/-- **Square-zero lifting for the normalizer** of an embedded diagonalizable group, for a
group functor corepresented by a formally smooth algebra. -/
theorem hasSquareZeroLifting_normalizerFamily :
    HasSquareZeroLifting (normalizerFamily ι.range) := by
  intro C N hN g₀ hg₀
  have hNil : IsNilpotent N := ⟨2, hN⟩
  let Aq : CommAlgCat.{u} R := CommAlgCat.of R (C ⧸ N)
  let π : C ⟶ Aq := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)
  have hπ : Function.Surjective π.hom := Ideal.Quotient.mk_surjective
  have hker : ∀ x, π.hom x = 0 → IsNilpotent x := fun x hx => by
    have hxN : x ∈ N := Ideal.Quotient.eq_zero_iff_mem.1 hx
    refine ⟨2, ?_⟩
    have h2 : x ^ 2 ∈ N ^ 2 := Ideal.pow_mem_pow hxN 2
    rw [hN] at h2
    exact h2
  have hg := exists_conj_of_mem_normalizerFamily ι hg₀
  have hg' := exists_conj_inv_of_mem_normalizerFamily ι hg₀
  obtain ⟨s, hs, hsπ⟩ := exists_isGrouplikeHom_lift π hker hπ (isGrouplikeHom_conjUniversal ι hg)
  obtain ⟨s', hs', hs'π⟩ :=
    exists_isGrouplikeHom_lift π hker hπ (isGrouplikeHom_conjUniversal ι hg')
  have hyp : ∀ (D : CommAlgCat.{u} R) (f : Aq ⟶ D) (t : Multiplicative M →* Dˣ),
      ι.hom D (twist s (π ≫ f) t) * F.map f g₀ = F.map f g₀ * ι.hom D t := by
    intro D f t
    rw [← twist_coefficientMap, hsπ, ← conjChar_eq_twist, hom_conjChar]
    group
  obtain ⟨g, hgπ, hgT⟩ := exists_twisted_lift ι e hs N hNil g₀ hyp
  have hinv : twist s (constant C) s' = universal C := by
    apply isGrouplikeHom_lift_unique π hker (hs.twist hs') isGrouplikeHom_universal
    rw [mapCharacter_coefficientMap_universal, twist, mapCharacter_mapCharacter, evaluate_comp,
      constant_coefficientMap, hs'π, ← coefficientMap_evaluate, ← mapCharacter_mapCharacter, hsπ]
    change twist (conjUniversal ι hg) (constant Aq) (conjUniversal ι hg') = _
    rw [← twist_constant_universal (s := conjUniversal ι hg'), ← conjChar_eq_twist,
      ← conjChar_eq_twist, conjChar_conjChar]
  refine ⟨g, ?_, hgπ⟩
  intro D f x hx
  obtain ⟨t, rfl⟩ := hx
  constructor
  · refine ⟨twist s f t, ?_⟩
    rw [← hgT, mul_inv_cancel_right]
  · refine ⟨twist s' f t, ?_⟩
    have h := hgT D f (twist s' f t)
    rw [twist_twist, hinv, twist_universal] at h
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

end Langlands.GroupScheme.CharacterAction

namespace Langlands.GroupScheme

open Opposite AlgebraicGeometry Corepresented CharacterAction
open scoped CategoryTheory.MonObj

section Embedding

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (j : (Diagonalizable.groupScheme R M).toGrp ⟶ groupScheme F e) [Mono j.hom.hom]

/-- The characters of a diagonalizable subgroup `j` of a corepresented group, embedded into
the algebra points. -/
def diagonalizableEmbedding : CharacterEmbedding F M where
  hom A := (affinePointsEquiv F e A).toMonoidHom.comp
    (((yonedaGrp.map j).app (op ((algSpec R).obj (op A)))).hom.comp
      (affinePointsEquiv (Diagonalizable.functor R M) (Diagonalizable.grpCorepresentation R M)
        A).symm.toMonoidHom)
  naturality {D D'} f t := by
    change F.map f (affinePointsEquiv F e D (characterPoint t ≫ j.hom.hom)) =
      affinePointsEquiv F e D' (characterPoint (mapCharacter f t) ≫ j.hom.hom)
    rw [characterPoint_mapCharacter, Category.assoc, affinePointsEquiv_naturality]
  injective A t t' h := by
    change affinePointsEquiv F e A (characterPoint t ≫ j.hom.hom) =
      affinePointsEquiv F e A (characterPoint t' ≫ j.hom.hom) at h
    have h' := (cancel_mono j.hom.hom).1 ((affinePointsEquiv F e A).injective h)
    exact (affinePointsEquiv (Diagonalizable.functor R M)
      (Diagonalizable.grpCorepresentation R M) A).symm.injective h'

theorem diagonalizableEmbedding_range (A : CommAlgCat.{u} R) :
    (diagonalizableEmbedding e j).range A = affineSubgroups (SubgroupFunctor.range j) A := by
  ext x
  change (∃ t, affinePointsEquiv F e A (characterPoint t ≫ j.hom.hom) = x) ↔
    ∃ y, y ≫ j.hom.hom = (affinePointsEquiv F e A).symm x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨characterPoint t, (MulEquiv.symm_apply_apply _ _).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨t, rfl⟩ := (affinePointsEquiv (Diagonalizable.functor R M)
      (Diagonalizable.grpCorepresentation R M) A).symm.surjective y
    refine ⟨t, ?_⟩
    exact (congrArg (affinePointsEquiv F e A) hy).trans (MulEquiv.apply_symm_apply _ _)

end Embedding

end Langlands.GroupScheme
