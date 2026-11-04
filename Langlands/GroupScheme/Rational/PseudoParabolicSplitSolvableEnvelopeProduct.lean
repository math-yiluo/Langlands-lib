import Langlands.GroupScheme.Unipotent.SplitTorusSubgroupHom
import Langlands.GroupScheme.AutomorphicAction.SemidirectHomLift
import Langlands.GroupScheme.AutomorphicAction.SemidirectMaps
import Langlands.GroupScheme.SubgroupFunctor.FppfProductCriterion
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Rational.FppfLocalLifting
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # The semidirect product `U ⋊ S` as an fppf-local product inside its ambient group -/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitSolvableEnvelope

open AutomorphicAction SubgroupFunctor

variable {k : Type u} [Field k] {P U : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))} (s : S.toGrp ⟶ P) (j : U ⟶ P)
  [Mono j.hom.hom] (hn : (range j).IsNormalizedBy (range s))

/-- The reordering morphism `S × U ⟶ U × S`, `(t, u) ↦ (t u t⁻¹, t)`, onto the underlying
scheme of `U ⋊ S`. -/
def reorder : S.X ⊗ U.X ⟶ U.X ⊗ S.X :=
  lift (ofNormalizedConjugation j s hn).hom (fst S.X U.X)

/-- The inverse of `reorder`, `(u, t) ↦ (t, t⁻¹ u t)`. -/
def reorderInv : U.X ⊗ S.X ⟶ S.X ⊗ U.X :=
  lift (snd U.X S.X) (lift (snd U.X S.X)⁻¹ (fst U.X S.X) ≫ (ofNormalizedConjugation j s hn).hom)

theorem reorder_reorderInv : reorder s j hn ≫ reorderInv s j hn = 𝟙 _ := by
  let a := ofNormalizedConjugation j s hn
  have ha : a.hom = a.act (fst S.X U.X) (snd S.X U.X) := by
    rw [act_eq, lift_fst_snd, Category.id_comp]
  apply CartesianMonoidalCategory.hom_ext
  · rw [reorderInv, reorder, Category.assoc, lift_fst, lift_snd, Category.id_comp]
  · rw [reorderInv, reorder, Category.assoc, lift_snd, comp_lift_assoc, GrpObj.comp_inv,
      lift_snd, lift_fst, Category.id_comp]
    change a.act (fst S.X U.X)⁻¹ a.hom = snd S.X U.X
    rw [ha, act_inv_act]

theorem reorderInv_reorder : reorderInv s j hn ≫ reorder s j hn = 𝟙 _ := by
  let a := ofNormalizedConjugation j s hn
  apply CartesianMonoidalCategory.hom_ext
  · rw [reorder, Category.assoc, lift_fst, reorderInv, Category.id_comp]
    change lift (snd U.X S.X) (a.act (snd U.X S.X)⁻¹ (fst U.X S.X)) ≫ a.hom = fst U.X S.X
    rw [← act_eq, act_act_inv]
  · rw [reorder, Category.assoc, lift_snd, reorderInv, lift_fst, Category.id_comp]

instance isIso_reorder : IsIso (reorder s j hn) :=
  ⟨⟨reorderInv s j hn, reorder_reorderInv s j hn, reorderInv_reorder s j hn⟩⟩

instance isIso_reorder_left : IsIso (reorder s j hn).left :=
  Functor.map_isIso (Over.forget _) (reorder s j hn)

/-- After reordering, the ordered product `(u, t) ↦ u t` becomes `(t, u) ↦ t u`. -/
theorem reorder_mul :
    reorder s j hn ≫ ((fst U.X S.X ≫ j.hom.hom) * (snd U.X S.X ≫ s.hom.hom)) =
      (fst S.X U.X ≫ s.hom.hom) * (snd S.X U.X ≫ j.hom.hom) := by
  have hc := lift_comp_normalizedConjugation_comp j s hn (fst S.X U.X) (snd S.X U.X)
  rw [lift_fst_snd, Category.id_comp] at hc
  rw [MonObj.comp_mul, reorder, lift_fst_assoc, lift_snd_assoc]
  change (normalizedConjugation j s hn ≫ j.hom.hom) * _ = _
  rw [hc, inv_mul_cancel_right]

/-- After reordering, the product homomorphism `U ⋊ S ⟶ P` is the multiplication
`(t, u) ↦ t u`. -/
theorem reorder_normalizedProductHom :
    reorder s j hn ≫ (normalizedProductHom j s hn).hom.hom =
      (fst S.X U.X ≫ s.hom.hom) * (snd S.X U.X ≫ j.hom.hom) :=
  (congrArg (fun f => reorder s j hn ≫ f) (normalizedProductHom_hom j s hn)).trans
    (reorder_mul s j hn)

variable [IsAffineHom S.X.hom] [IsAffineHom U.X.hom]

local instance : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
local instance : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom

/-- If the split torus `S` and the unipotent closed subgroup `U` meet trivially, which holds
by `IsSplitTorus.eq_one_of_comp_eq_comp`, the product homomorphism `U ⋊ S ⟶ P` is a
monomorphism. -/
theorem mono_normalizedProductHom [Mono s.hom.hom] (hS : IsSplitTorus S.toGrp)
    (hU : IsUnipotent U) (hj : IsClosedSubgroup j) :
    Mono (normalizedProductHom j s hn).hom.hom := by
  let a := ofNormalizedConjugation j s hn
  let h := normalizedProductHom j s hn
  have coord : ∀ {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ U.X ⊗ S.X),
      z ≫ ((fst U.X S.X ≫ j.hom.hom) * (snd U.X S.X ≫ s.hom.hom)) = 1 →
        z ≫ fst U.X S.X = 1 ∧ z ≫ snd U.X S.X = 1 := by
    intro T z hz
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc] at hz
    have h1 : (z ≫ snd U.X S.X) ≫ s.hom.hom = (z ≫ fst U.X S.X)⁻¹ ≫ j.hom.hom := by
      rw [GrpObj.inv_comp]
      exact eq_inv_of_mul_eq_one_right hz
    have ht : z ≫ snd U.X S.X = 1 := IsSplitTorus.eq_one_of_comp_eq_comp hS hU hj _ _ h1
    refine ⟨?_, ht⟩
    rw [ht, MonObj.one_comp, _root_.mul_one] at hz
    apply (cancel_mono j.hom.hom).mp
    rw [hz, MonObj.one_comp]
  have key : ∀ {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ a.semidirectProduct.X),
      z ≫ h.hom.hom = 1 → z = 1 := by
    intro T z hz
    obtain ⟨hu, ht⟩ := coord z
      ((congrArg (fun f => z ≫ f) (normalizedProductHom_hom j s hn)).symm.trans hz)
    apply (a.semidirectPointsEquiv T).injective
    rw [map_one]
    apply SemidirectProduct.ext
    · rw [semidirectPointsEquiv_left, SemidirectProduct.one_left]
      exact hu
    · rw [semidirectPointsEquiv_right, SemidirectProduct.one_right]
      exact ht
  constructor
  intro T x y hxy
  have hxy' := key (x * y⁻¹) (by rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel])
  exact mul_inv_eq_one.mp hxy'

variable [Smooth S.X.hom] [Smooth U.X.hom] [LocallyOfFiniteType P.X.hom] [IsAffineHom P.X.hom]

/-- The product homomorphism `U ⋊ S ⟶ P` is a closed subgroup when `U ⋊ S` is connected: it
factors through its schematic image by an fppf homomorphism, which is a monomorphism and hence
an isomorphism. -/
theorem isClosedSubgroup_normalizedProductHom [Mono s.hom.hom] (hS : IsSplitTorus S.toGrp)
    (hU : IsUnipotent U) (hj : IsClosedSubgroup j)
    [ConnectedSpace (ofNormalizedConjugation j s hn).semidirectProduct.X.left] :
    IsClosedSubgroup (normalizedProductHom j s hn) := by
  have hm := mono_normalizedProductHom s j hn hS hU hj
  obtain ⟨D, inc, fac, hinc, hfac, hflat, hsurj, hqc, -, -, -, -⟩ :=
    HomImage.exists_image (normalizedProductHom j s hn)
  have hfac' : fac.hom.hom ≫ inc.hom.hom = (normalizedProductHom j s hn).hom.hom := by
    rw [← hfac]
    rfl
  have : Mono fac.hom.hom := by
    rw [← hfac'] at hm
    exact mono_of_mono _ inc.hom.hom
  have : IsIso fac.hom.hom :=
    RelativeRoot.isIso_of_effectiveEpi_factorization fac.hom.hom fac.hom.hom (𝟙 _)
      (Category.id_comp _)
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : IsIso fac.hom.hom.left := Functor.map_isIso (Over.forget _) fac.hom.hom
  change IsClosedImmersion (normalizedProductHom j s hn).hom.hom.left
  rw [← hfac']
  change IsClosedImmersion (fac.hom.hom.left ≫ inc.hom.hom.left)
  infer_instance

/-- The product homomorphism `U ⋊ S ⟶ P` represents the fppf-local product of the images of
`S` and `U`. -/
theorem isFppfProduct_normalizedProductHom [Mono s.hom.hom] (hS : IsSplitTorus S.toGrp)
    (hU : IsUnipotent U) (hj : IsClosedSubgroup j)
    [ConnectedSpace (ofNormalizedConjugation j s hn).semidirectProduct.X.left] :
    IsFppfProduct (range s) (range j) (normalizedProductHom j s hn) := by
  let q : S.X ⊗ U.X ⟶ (ofNormalizedConjugation j s hn).semidirectProduct.X := reorder s j hn
  have : IsIso q.left := isIso_reorder_left s j hn
  exact isFppfProduct_of_fppf_factorization s j (normalizedProductHom j s hn)
    (isClosedSubgroup_normalizedProductHom s j hn hS hU hj) q
    (reorder_normalizedProductHom s j hn)

omit [Mono j.hom.hom] [IsAffineHom S.X.hom] [IsAffineHom U.X.hom] [Smooth S.X.hom] [Smooth U.X.hom]
  [LocallyOfFiniteType P.X.hom] [IsAffineHom P.X.hom] in
/-- Assembly of the split solvable envelope, given split solvability of the semidirect products
`U ⋊ S`. Let `P` be a closed subgroup of a smooth affine group `G`, let `s` be a split subtorus
of `P` and let `j` be a split unipotent radical of `P`. If every semidirect product of `S` acting
on `U` is split solvable, then `normalizedProductHom` provides a split solvable group scheme
representing the fppf-local product of the images of `s` and `j`. -/
theorem exists_envelope_of_isSplitSolvable {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {i : P ⟶ G} (hi : IsClosedSubgroup i)
    (hs : IsSplitSubtorus s) (hj : IsSplitUnipotentRadical j)
    (hA : ∀ [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
      (a : AutomorphicAction S.toGrp U), IsSplitSolvableGroupScheme a.semidirectProduct) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ P),
      IsSplitSolvableGroupScheme H ∧ IsFppfProduct (range s) (range j) h := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom U.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have := hj.smooth
  have := hj.connectedSpace
  have : IsClosedImmersion s.hom.hom.left := hs.2
  have : Mono s.hom.hom := Over.mono_of_mono_left _
  have : Smooth S.X.hom := hs.1.smooth
  have : IsAffineHom S.X.hom := hs.1.isAffineHom
  let hn : (range j).IsNormalizedBy (range s) := fun T g x _ hx => hj.isNormal T g x trivial hx
  have hH := hA (ofNormalizedConjugation j s hn)
  have := hH.connectedSpace
  exact ⟨_, normalizedProductHom j s hn, hH,
    isFppfProduct_normalizedProductHom s j hn hs.1 hj.isUnipotent hj.isClosedSubgroup⟩

end Langlands.GroupScheme.SplitSolvableEnvelope
