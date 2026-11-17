import Langlands.GroupScheme.Torus.GrouplikeIdentityLocus
import Langlands.GroupScheme.Torus.NormalizerLifting
import Langlands.GroupScheme.Torus.CentralizerOpenInNormalizer
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizer
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines

/-! # Idempotent centralizer loci for diagonalizable subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace CharacterAction

open Corepresented

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} (emb : CharacterEmbedding F M)
  {A : CommAlgCat.{u} R} {g : F.obj A}
  (hg : g ∈ normalizerFamily emb.range A)

/-- The conjugated universal character is the identity after a coefficient map
if and only if that refinement centralizes the embedded diagonalizable group. -/
theorem conjUniversal_eq_universal_iff {C : CommAlgCat.{u} R} (f : A ⟶ C) :
    mapCharacter (coefficientMap (M := M) f)
        (conjUniversal emb (exists_conj_of_mem_normalizerFamily emb hg)) = universal C ↔
      F.map f g ∈ centralizerFamily emb.range C := by
  let h := exists_conj_of_mem_normalizerFamily emb hg
  constructor
  · intro he D k x hx
    obtain ⟨t, rfl⟩ := hx
    have ht : conjChar emb h (f ≫ k) t = t := by
      rw [conjChar_eq_twist, ← twist_coefficientMap, he, twist_universal]
    have hc := hom_conjChar emb h (f ≫ k) t
    rw [ht, F.map_comp, ConcreteCategory.comp_apply] at hc
    exact (mul_inv_eq_iff_eq_mul.1 hc.symm)
  · intro hc
    have he : mapCharacter (coefficientMap (M := M) f) (conjUniversal emb h) =
        conjChar emb h (f ≫ constant C) (universal C) := by
      unfold conjUniversal
      rw [mapCharacter_conjChar, constant_coefficientMap,
        mapCharacter_coefficientMap_universal]
    rw [he]
    apply emb.injective _
    rw [hom_conjChar]
    have hcomm := hc (algebra (M := M) C) (constant C)
      (emb.hom _ (universal C)) ⟨universal C, rfl⟩
    rw [F.map_comp, ConcreteCategory.comp_apply]
    rw [hcomm.eq, mul_inv_cancel_right]

include hg in
/-- On a normalizer family, all-test centralization is the condition that a
single idempotent in the parameter algebra becomes one. -/
theorem exists_idempotent_centralizer_locus [AddGroup.FG M] :
    ∃ e : A, IsIdempotentElem e ∧
      ∀ (C : CommAlgCat.{u} R) (f : A ⟶ C),
        F.map f g ∈ centralizerFamily emb.range C ↔ f.hom e = 1 := by
  obtain ⟨e, he, h⟩ := exists_idempotent_identity_locus
    (isGrouplikeHom_conjUniversal emb (exists_conj_of_mem_normalizerFamily emb hg))
  exact ⟨e, he, fun C f => (conjUniversal_eq_universal_iff emb hg f).symm.trans (h C f)⟩

end CharacterAction

namespace Corepresented

/-- For a closed affine cutout, membership on any test scheme is membership
of its point in the subgroup on global sections. -/
theorem mem_iff_points_mem_affineSubgroups_of_isCutOutBy
    {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
    {K : SubgroupFunctor (groupScheme F e)} {I : Ideal B}
    (hK : IsCutOutBy e (affineSubgroups K) I)
    {U : Over (Spec R)} (x : U ⟶ (groupScheme F e).X) :
    x ∈ K.carrier U ↔ pointsEquiv F e U x ∈ affineSubgroups K ((algΓ R).obj U).unop := by
  have h := cutSubgroupFunctor_affineSubgroups
    (isAffineCutOutBy_of_isCutOutBy hK)
  change x ∈ K.carrier U ↔
    x ∈ (cutSubgroupFunctor (isCutOutBy_affineSubgroups
      (isAffineCutOutBy_of_isCutOutBy hK))).carrier U
  rw [h]

end Corepresented

/-- For an idempotent global section, containment of a morphism's range in
its unit open is exactly the equation that its pullback is one. -/
theorem range_subset_basicOpen_idempotent_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) {a : Γ(Y, ⊤)} (ha : IsIdempotentElem a) :
    Set.range f ⊆ Y.basicOpen a ↔ f.appTop a = 1 := by
  have htop : Set.range f ⊆ Y.basicOpen a ↔ f ⁻¹ᵁ Y.basicOpen a = ⊤ := by
    constructor
    · intro h
      apply top_unique
      intro x _
      exact h ⟨x, rfl⟩
    · intro h y hy
      obtain ⟨x, rfl⟩ := hy
      have hx : x ∈ f ⁻¹ᵁ Y.basicOpen a := by rw [h]; trivial
      exact hx
  rw [htop, Scheme.preimage_basicOpen_top]
  constructor
  · intro h
    have hu := Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines.isUnit_of_basicOpen_eq_top
      X (f.appTop a) h
    have hi : IsIdempotentElem (f.appTop a) := by
      change f.appTop a * f.appTop a = f.appTop a
      rw [← map_mul, ha.eq]
    exact hu.mul_left_cancel (by rw [hi.eq, mul_one])
  · intro h
    rw [h, X.basicOpen_one]

namespace DiagonalizableCentralizer

open Corepresented CharacterAction

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  (j : (Diagonalizable.groupScheme R M).toGrp ⟶ groupScheme F e) [Mono j.hom.hom]
  {I : Ideal B}
  (hI : ∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
    y ∈ (SubgroupFunctor.range j).carrier U ↔
      ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0)
  [hproj : Module.Projective R (B ⧸ I)]

include hI hproj

/-- The centralizing part of any normalizing family is an open subscheme
of its parameter scheme, with the all-test factorization property. -/
theorem exists_openLocus {U : Over (Spec R)} {g : U ⟶ (groupScheme F e).X}
    (hg : g ∈ (SubgroupFunctor.range j).normalizer.carrier U) :
    ∃ W : U.left.Opens, ∀ (V : Over (Spec R)) (a : V ⟶ U),
      Set.range a.left ⊆ W ↔ a ≫ g ∈ (SubgroupFunctor.range j).centralizer.carrier V := by
  let emb := diagonalizableEmbedding e j
  have hrange : emb.range = affineSubgroups (SubgroupFunctor.range j) := by
    funext A
    exact diagonalizableEmbedding_range e j A
  have hgn : pointsEquiv F e U g ∈
      normalizerFamily emb.range ((algΓ R).obj U).unop := by
    rw [hrange, ← affineSubgroups_normalizer hI]
    exact (mem_iff_points_mem_affineSubgroups_of_isCutOutBy
      (isCutOutBy_affineSubgroups_normalizer hI) g).mp hg
  obtain ⟨a, ha, haC⟩ := exists_idempotent_centralizer_locus emb hgn
  refine ⟨U.left.basicOpen a, fun V b => ?_⟩
  rw [range_subset_basicOpen_idempotent_iff b.left ha,
    mem_iff_points_mem_affineSubgroups_of_isCutOutBy
      (isCutOutBy_affineSubgroups_centralizer hI),
    affineSubgroups_centralizer hI, pointsEquiv_naturality]
  have h := (haC ((algΓ R).obj V).unop ((algΓ R).map b).unop).symm
  rw [hrange] at h
  exact h

/-- A chosen open centralizer locus inside a normalizing family. -/
def openLocus {U : Over (Spec R)} {g : U ⟶ (groupScheme F e).X}
    (hg : g ∈ (SubgroupFunctor.range j).normalizer.carrier U) : U.left.Opens :=
  (exists_openLocus e j hI hg).choose

/-- A morphism factors through the chosen open precisely when its restriction
centralizes after every further test. -/
theorem range_subset_openLocus_iff {U : Over (Spec R)} {g : U ⟶ (groupScheme F e).X}
    (hg : g ∈ (SubgroupFunctor.range j).normalizer.carrier U)
    {V : Over (Spec R)} (a : V ⟶ U) :
    Set.range a.left ⊆ openLocus e j hI hg ↔
      a ≫ g ∈ (SubgroupFunctor.range j).centralizer.carrier V :=
  (exists_openLocus e j hI hg).choose_spec V a

end DiagonalizableCentralizer

end Langlands.GroupScheme
