import Langlands.GroupScheme.Reductive.AffinePinnedTestCentrality
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # Detecting pinning units through an fppf cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Units of the original affine ring are detected by local-ring tests over
any flat surjective scheme cover. -/
theorem unit_eq_one_of_local_tests_over_flat_cover
    {R : Type u} [CommRing R] {U : Scheme.{u}}
    (q : U ⟶ Spec (CommRingCat.of R)) [Flat q] [Surjective q] (c : Rˣ)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A]
      (a : Spec (CommRingCat.of A) ⟶ U),
      (Spec.preimage (a ≫ q)).hom (c : R) = 1) : c = 1 := by
  let S := Spec (CommRingCat.of R)
  let z : Over.mk (𝟙 S) ⟶ (Gm S).X := (Gm.affinePointsEquiv (𝟙 S)).symm c
  let onePoint : Over.mk (𝟙 S) ⟶ (Gm S).X := 1
  let : IsAffineHom (Gm S).X.hom := (isSplitTorus_gm (S := S)).isAffineHom
  let : IsAffine (Gm S).X.left := isAffine_of_isAffineHom (Gm S).X.hom
  have hz : q ≫ z.left = q ≫ onePoint.left := by
    apply CellGluing.hom_ext_of_localRingPoints
    intro A _ _ a
    let φ : CommRingCat.of R ⟶ CommRingCat.of A := Spec.preimage (a ≫ q)
    have hφ : Spec.map φ = a ≫ q := Spec.map_preimage _
    have hu : Units.map φ.hom.toMonoidHom c = 1 := Units.ext (h A a)
    have ht : Gm.affineMap φ (𝟙 S) ≫ z =
        Gm.affineMap φ (𝟙 S) ≫ onePoint := by
      apply (Gm.affinePointsEquiv (Spec.map φ ≫ 𝟙 S)).injective
      rw [Gm.affinePointsEquiv_naturality, Gm.affinePointsEquiv_naturality]
      simpa only [z, onePoint, MulEquiv.apply_symm_apply, map_one] using hu
    simpa only [Over.comp_left, Gm.affineMap, Over.homMk_left, hφ, Category.assoc]
      using congrArg (fun t => t.left) ht
  let : Epi q := Flat.epi_of_flat_of_surjective q
  have hz' : z = onePoint := Over.OverMorphism.ext ((cancel_epi q).mp hz)
  simpa only [z, onePoint, MulEquiv.apply_symm_apply, map_one] using
    congrArg (Gm.affinePointsEquiv (𝟙 S)) hz'

namespace AffinePinnedModel

variable {M : AffinePinnedModel.{u}}

/-- A scalar coefficient of an original simple-vector equation equals one
on every local coefficient test over a scheme where the pullback is pinned. -/
theorem pinning_coefficient_eq_one_on_local_test
    (σ : CategoryTheory.Aut M.group)
    {T : Scheme.{u}} (f : T ⟶ M.base)
    (hpin : PreservesLocalPinning ((baseChange f).mapIso σ))
    {s t : M.basis.support} {c : M.ring}
    (hv : Lie.targetMapLinear σ.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      c • (M.pinning t 1).val)
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra M.ring A]
    (a : Spec (CommRingCat.of A) ⟶ T)
    (ha : algebraBaseMap M.ring A = a ≫ f) :
    algebraMap M.ring A c = 1 := by
  obtain ⟨p, hp⟩ := hpin A a ha ha
  have hmap : ((baseChange f).map σ.hom).hom.hom.left ≫
      pullback.fst M.group.X.hom f =
    pullback.fst M.group.X.hom f ≫ σ.hom.hom.hom.left := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_fst _ _ _
  have he := congrArg (fun k => k ≫ pullback.fst M.group.X.hom f) (hp s)
  change (M.rootVectorPoint f A a ha s ≫
    ((baseChange f).map σ.hom).hom.hom.left) ≫ pullback.fst M.group.X.hom f =
      M.rootVectorPoint f A a ha (p s) ≫ pullback.fst M.group.X.hom f at he
  rw [Category.assoc, hmap, ← Category.assoc,
    rootVectorPoint_fst, rootVectorPoint_fst] at he
  have hLie : Lie.targetMapLinear σ.hom A
      (lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning s 1).val) =
    lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning (p s) 1).val := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact he
  have hcoeff := congrArg (lieKernelMapLinear M.group (Algebra.ofId M.ring A)) hv
  rw [← lieKernelTargetLinear_map, LinearMap.map_smulₛₗ] at hcoeff
  exact (M.simpleVectorAt_smul_eq A (hcoeff.symm.trans hLie)).2

/-- Normalized pullback of an actual base-changed automorphism is the direct
base change of that same automorphism. -/
theorem pullComparison_baseChangeIso
    (σ : CategoryTheory.Aut M.group)
    {T U : Scheme.{u}} (f : T ⟶ M.base) (q : U ⟶ T) :
    pullComparison ((baseChange f).mapIso σ) q =
      (baseChange (q ≫ f)).mapIso σ := by
  apply Iso.ext
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  have h := congrArg (fun a => a ≫ (baseChangeCompIso f q M.group).inv)
    (baseChangeCompIso_hom_naturality f q σ.hom)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

/-- A concrete fppf cover on which the direct base change of the original
automorphism preserves local pinning. -/
structure DirectFppfPinningCover (M : AffinePinnedModel.{u})
    (σ : CategoryTheory.Aut M.group) where
  space : Scheme.{u}
  projection : space ⟶ M.base
  flat : Flat projection
  surjective : Surjective projection
  locallyOfFinitePresentation : LocallyOfFinitePresentation projection
  pinning : PreservesLocalPinning ((baseChange projection).mapIso σ)

/-- Normalize the cover supplied by fppf-local pinning into a cover carrying
the direct base change of the original automorphism. -/
def directFppfPinningCover (M : AffinePinnedModel.{u})
    (σ : CategoryTheory.Aut M.group)
    (hpin : IsFppfLocallyPinned ((baseChange (𝟙 M.base)).mapIso σ)) :
    DirectFppfPinningCover M σ := by
  classical
  let U := hpin.choose
  let q := hpin.choose_spec.choose
  have hq := hpin.choose_spec.choose_spec
  exact {
    space := U
    projection := q
    flat := hq.1
    surjective := hq.2.1
    locallyOfFinitePresentation := hq.2.2.1
    pinning := by
      have hh : PreservesLocalPinning ((baseChange (q ≫ 𝟙 M.base)).mapIso σ) := by
        simpa only [pullComparison_baseChangeIso] using hq.2.2.2.2.2
      exact Eq.mp (congrArg
        (fun z => PreservesLocalPinning (M := M) (N := M)
          ((baseChange z).mapIso σ)) (Category.comp_id q)) hh
  }

/-- An original unit coefficient is one if the identity pullback of the
actual automorphism is only fppf-locally pinned. -/
theorem pinning_unit_eq_one_of_fppfLocalPinning
    (σ : CategoryTheory.Aut M.group)
    (hpin : IsFppfLocallyPinned ((baseChange (𝟙 M.base)).mapIso σ))
    {s t : M.basis.support} {c : M.ringˣ}
    (hv : Lie.targetMapLinear σ.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
      (c : M.ring) • (M.pinning t 1).val) : c = 1 := by
  let C := directFppfPinningCover M σ hpin
  let : Flat C.projection := C.flat
  let : Surjective C.projection := C.surjective
  apply unit_eq_one_of_local_tests_over_flat_cover C.projection c
  intro A _ _ a
  let : Algebra M.ring A := (Spec.preimage (a ≫ C.projection)).hom.toAlgebra
  have ha : algebraBaseMap M.ring A = a ≫ C.projection := Spec.map_preimage _
  exact pinning_coefficient_eq_one_on_local_test σ C.projection C.pinning hv A a ha

end AffinePinnedModel

end Langlands.GroupScheme
