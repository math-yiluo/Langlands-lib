import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionScalarBaseChange
import Mathlib.CategoryTheory.Yoneda

/-! # Tensor-algebra base change of actual affine-chart Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- Affine inverse images preserve the condition that every finite set of
actual scheme points lies in an affine open. -/
theorem hasFiniteAffineNeighborhoods_of_affine
    {X Z : Scheme.{u}} (f : X ⟶ Z) [IsAffineHom f]
    (hZ : HasFiniteAffineNeighborhoods Z) :
    HasFiniteAffineNeighborhoods X := by
  intro E hE
  obtain ⟨V, hV⟩ := hZ (f '' E) (hE.image f)
  refine ⟨⟨f ⁻¹ᵁ V.val, V.property.preimage f⟩, ?_⟩
  intro x hx
  exact hV ⟨x, hx, rfl⟩

/-- The actual base change along a ring map preserves the finite-set
affine-neighborhood property, since its projection to the target is affine. -/
theorem hasFiniteAffineNeighborhoods_ringBaseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (Y : Over (Spec (CommRingCat.of R)))
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    HasFiniteAffineNeighborhoods (ringBaseChange R S Y).left := by
  let : IsAffineHom (pullback.fst Y.hom (Spec.algebraMap R S)) :=
    MorphismProperty.pullback_fst Y.hom (Spec.algebraMap R S) inferInstance
  exact hasFiniteAffineNeighborhoods_of_affine
    (pullback.fst Y.hom (Spec.algebraMap R S)) hY

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual test pullback transported through the tensor-spectrum
isomorphism is the usual ring base change to the tensor algebra. -/
def weilRestrictionTensorBaseChangeTestIso
    (T : Over (Spec (CommRingCat.of C))) :
    (Over.map (pullbackSpecIso A C B).hom).obj
        ((Over.pullback
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).obj T) ≅
      ringBaseChange C (C ⊗[A] B) T :=
  Over.isoMk
    (asIso (pullback.map T.hom
      (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))
      T.hom (Spec.algebraMap C (C ⊗[A] B))
      (𝟙 _) (pullbackSpecIso A C B).hom (𝟙 _)
      (by simp) (by simpa only [Category.comp_id, Category.id_comp] using
        (pullbackSpecIso_hom_fst' A C B).symm)))
    (by simp [ringBaseChange])

/-- The actual target pullback transported through the tensor-spectrum
isomorphism is its base change along the actual right algebra inclusion. -/
def weilRestrictionTensorBaseChangeTargetIso
    (Y : Over (Spec (CommRingCat.of B))) :
    (Over.map (pullbackSpecIso A C B).hom).obj
        ((Over.pullback
          (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).obj Y) ≅
      ringBaseChange B (C ⊗[A] B) Y :=
  Over.isoMk
    (asIso (pullback.map Y.hom
      (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))
      Y.hom (Spec.algebraMap B (C ⊗[A] B))
      (𝟙 _) (pullbackSpecIso A C B).hom (𝟙 _)
      (by simp) (by
        simp only [Category.comp_id]
        change pullback.snd _ _ =
          (pullbackSpecIso A C B).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom)
        exact (pullbackSpecIso_hom_snd A C B).symm)))
    (by simp [ringBaseChange])

/-- Naturality of the actual tensor-algebra test-pullback isomorphism. -/
theorem weilRestrictionTensorBaseChangeTestIso_natural
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S) :
    (Over.map (pullbackSpecIso A C B).hom).map
        ((Over.pullback
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f) ≫
        (weilRestrictionTensorBaseChangeTestIso A B C S).hom =
      (weilRestrictionTensorBaseChangeTestIso A B C T).hom ≫
        (Over.pullback (Spec.algebraMap C (C ⊗[A] B))).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [weilRestrictionTensorBaseChangeTestIso, Over.pullback_map_left,
      Category.assoc]
  · simp [weilRestrictionTensorBaseChangeTestIso, Over.pullback_map_left,
      Category.assoc]

/-- The inverse test-pullback isomorphism is natural as well. -/
theorem weilRestrictionTensorBaseChangeTestIso_inv_natural
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S) :
    (weilRestrictionTensorBaseChangeTestIso A B C T).inv ≫
        (Over.map (pullbackSpecIso A C B).hom).map
          ((Over.pullback
            (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f) =
      (Over.pullback (Spec.algebraMap C (C ⊗[A] B))).map f ≫
        (weilRestrictionTensorBaseChangeTestIso A B C S).inv := by
  apply (cancel_mono (weilRestrictionTensorBaseChangeTestIso A B C S).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [weilRestrictionTensorBaseChangeTestIso_natural, Iso.inv_hom_id_assoc]

variable [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

local instance affineChartWeilRestrictionTensorBaseChangeInst1 : LocallyOfFiniteType (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs
    (LocallyOfFiniteType (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

/-- Canonical comparison with the actual tensor-algebra Weil functor.
It is the original scalar-base-change counit comparison transported through
the actual tensor-spectrum and pullback isomorphisms. -/
def affineChartWeilRestrictionTensorBaseChangeComparison
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    ringBaseChange C (C ⊗[A] B) T ⟶ ringBaseChange B (C ⊗[A] B) Y :=
  (weilRestrictionTensorBaseChangeTestIso A B C T).inv ≫
    (Over.map (pullbackSpecIso A C B).hom).map
      (affineChartWeilRestrictionScalarBaseChangeComparison A B C Y T p) ≫
    (weilRestrictionTensorBaseChangeTargetIso A B C Y).hom

/-- Naturality of the canonical tensor-algebra comparison on all actual
test schemes over the new base ring. -/
theorem affineChartWeilRestrictionTensorBaseChangeComparison_natural
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (p : S ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionTensorBaseChangeComparison A B C Y T (f ≫ p) =
      (Over.pullback (Spec.algebraMap C (C ⊗[A] B))).map f ≫
        affineChartWeilRestrictionTensorBaseChangeComparison A B C Y S p := by
  simp only [affineChartWeilRestrictionTensorBaseChangeComparison,
    affineChartWeilRestrictionScalarBaseChangeComparison_natural, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc,
    weilRestrictionTensorBaseChangeTestIso_inv_natural]
  simp only [Category.assoc]

variable [IsSeparated Y.hom]

local instance affineChartWeilRestrictionTensorBaseChangeInst2 : IsSeparated (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

/-- The actual base change of the original representing scheme represents
the Weil functor for the actual tensor-algebra extension, on every test. -/
def affineChartWeilRestrictionTensorBaseChangeTestEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C))) :
    (T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) ≃
      (ringBaseChange C (C ⊗[A] B) T ⟶ ringBaseChange B (C ⊗[A] B) Y) :=
  (affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y hY T).trans
    (((Functor.FullyFaithful.ofFullyFaithful
      (Over.map (pullbackSpecIso A C B).hom)).homEquiv).trans
      (Iso.homCongr (weilRestrictionTensorBaseChangeTestIso A B C T)
        (weilRestrictionTensorBaseChangeTargetIso A B C Y)))

/-- The representing equivalence uses the canonical tensor comparison. -/
@[simp]
theorem affineChartWeilRestrictionTensorBaseChangeTestEquiv_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY T p =
      affineChartWeilRestrictionTensorBaseChangeComparison A B C Y T p := by
  simp [affineChartWeilRestrictionTensorBaseChangeTestEquiv,
    affineChartWeilRestrictionTensorBaseChangeComparison, Iso.homCongr]

/-- Naturality of the equivalence for the actual tensor-algebra functor. -/
theorem affineChartWeilRestrictionTensorBaseChangeTestEquiv_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (p : S ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY T (f ≫ p) =
      (Over.pullback (Spec.algebraMap C (C ⊗[A] B))).map f ≫
        affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY S p := by
  simp only [affineChartWeilRestrictionTensorBaseChangeTestEquiv_apply]
  exact affineChartWeilRestrictionTensorBaseChangeComparison_natural A B C Y f p

/-- Inverse naturality of the actual tensor-algebra representing equivalence. -/
theorem affineChartWeilRestrictionTensorBaseChangeTestEquiv_symm_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (q : ringBaseChange C (C ⊗[A] B) S ⟶ ringBaseChange B (C ⊗[A] B) Y) :
    (affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY T).symm
        ((Over.pullback (Spec.algebraMap C (C ⊗[A] B))).map f ≫ q) =
      f ≫ (affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY S).symm q := by
  apply (affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY T).injective
  rw [Equiv.apply_symm_apply,
    affineChartWeilRestrictionTensorBaseChangeTestEquiv_natural,
    Equiv.apply_symm_apply]

/-- The natural equivalence between Hom sets into the actual base-changed
original Weil scheme and into the separately constructed tensor-algebra
Weil scheme. The geometry of the new target follows from base change. -/
def affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C))) :
    (T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) ≃
      (T ⟶ affineChartWeilRestriction C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y)) :=
  (affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY T).trans
    (affineChartWeilRestrictionTestEquiv C (C ⊗[A] B)
      (ringBaseChange B (C ⊗[A] B) Y)
      (hasFiniteAffineNeighborhoods_ringBaseChange B (C ⊗[A] B) Y hY) T).symm

/-- Naturality into the two separately constructed representing schemes. -/
theorem affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (p : S ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv A B C Y hY T (f ≫ p) =
      f ≫ affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv A B C Y hY S p := by
  unfold affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv
  simp only [Equiv.trans_apply,
    affineChartWeilRestrictionTensorBaseChangeTestEquiv_natural]
  exact affineChartWeilRestrictionInverse_natural C (C ⊗[A] B)
    (ringBaseChange B (C ⊗[A] B) Y) _ f _

/-- The canonical morphism from the actual base change of the original
Weil restriction to the separately constructed tensor-algebra Weil restriction. -/
def affineChartWeilRestrictionTensorBaseChangeHom
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    ringBaseChange A C (affineChartWeilRestriction A B Y) ⟶
      affineChartWeilRestriction C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y) :=
  affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv A B C Y hY _ (𝟙 _)

/-- On every test, the representing equivalence is composition with the
same canonical comparison morphism. -/
theorem affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv_eq_comp
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv A B C Y hY T p =
      p ≫ affineChartWeilRestrictionTensorBaseChangeHom A B C Y hY := by
  simpa only [Category.comp_id, affineChartWeilRestrictionTensorBaseChangeHom] using
    affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv_natural
      A B C Y hY p (𝟙 _)

/-- The canonical comparison is an isomorphism, by the proved bijections
on all actual test schemes. -/
instance affineChartWeilRestrictionTensorBaseChangeHom_isIso
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    IsIso (affineChartWeilRestrictionTensorBaseChangeHom A B C Y hY) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  simp_rw [← affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv_eq_comp]
  exact (affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv A B C Y hY T).bijective

/-- Base change of the actual affine-chart Weil restriction is canonically
isomorphic to the independently glued Weil restriction for the actual
tensor-algebra extension. -/
def affineChartWeilRestrictionTensorBaseChangeIso
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    ringBaseChange A C (affineChartWeilRestriction A B Y) ≅
      affineChartWeilRestriction C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y) :=
  asIso (affineChartWeilRestrictionTensorBaseChangeHom A B C Y hY)

/-- The scheme isomorphism carries every test morphism to precisely the
tensor comparison under the second scheme's original counit comparison. -/
@[simp]
theorem affineChartWeilRestrictionTensorBaseChangeIso_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionComparison C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y) T
        (p ≫ (affineChartWeilRestrictionTensorBaseChangeIso A B C Y hY).hom) =
      affineChartWeilRestrictionTensorBaseChangeComparison A B C Y T p := by
  change affineChartWeilRestrictionTestEquiv C (C ⊗[A] B)
    (ringBaseChange B (C ⊗[A] B) Y)
    (hasFiniteAffineNeighborhoods_ringBaseChange B (C ⊗[A] B) Y hY) T
      (p ≫ affineChartWeilRestrictionTensorBaseChangeHom A B C Y hY) = _
  rw [← affineChartWeilRestrictionTensorBaseChangeRepresentingEquiv_eq_comp]
  exact (affineChartWeilRestrictionTestEquiv C (C ⊗[A] B)
    (ringBaseChange B (C ⊗[A] B) Y)
    (hasFiniteAffineNeighborhoods_ringBaseChange B (C ⊗[A] B) Y hY) T).apply_symm_apply
      (affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y hY T p)

omit [IsSeparated Y.hom] in
/-- An actual relative projective immersion supplies all the original
target geometry for the tensor-algebra representing equivalence. -/
def projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of C))) :
    (T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) ≃
      (ringBaseChange C (C ⊗[A] B) T ⟶ ringBaseChange B (C ⊗[A] B) Y) := by
  letI := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTensorBaseChangeTestEquiv A B C Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n i) T

omit [IsSeparated Y.hom] in
/-- The projective-immersion equivalence retains the same canonical
tensor-algebra comparison on every test scheme. -/
@[simp]
theorem projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv A B C Y n i hi T p =
      affineChartWeilRestrictionTensorBaseChangeComparison A B C Y T p := by
  let := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTensorBaseChangeTestEquiv_apply A B C Y _ T p

omit [IsSeparated Y.hom] in
/-- Naturality on every test for actual projective-immersion inputs. -/
theorem projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv_natural
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (p : S ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv A B C Y n i hi T
        (f ≫ p) =
      (Over.pullback (Spec.algebraMap C (C ⊗[A] B))).map f ≫
        projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv A B C Y n i hi S p := by
  simp only [projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv_apply]
  exact affineChartWeilRestrictionTensorBaseChangeComparison_natural A B C Y f p

omit [IsSeparated Y.hom] in
/-- Inverse naturality for actual projective-immersion inputs. -/
theorem projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv_symm_natural
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (q : ringBaseChange C (C ⊗[A] B) S ⟶ ringBaseChange B (C ⊗[A] B) Y) :
    (projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv A B C Y n i hi T).symm
        ((Over.pullback (Spec.algebraMap C (C ⊗[A] B))).map f ≫ q) =
      f ≫
        (projectiveImmersionWeilRestrictionTensorBaseChangeTestEquiv A B C Y n i hi S).symm
          q := by
  let := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTensorBaseChangeTestEquiv_symm_natural A B C Y _ f q

omit [IsSeparated Y.hom] in
/-- Tensor base change of the original actual Weil scheme agrees with the
separately glued tensor-algebra Weil scheme for an actual projective immersion.
No geometry of the base-changed target is an input. -/
def projectiveImmersionWeilRestrictionTensorBaseChangeIso
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom) :
    ringBaseChange A C (affineChartWeilRestriction A B Y) ≅
      affineChartWeilRestriction C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y) := by
  letI := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTensorBaseChangeIso A B C Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n i)

omit [IsSeparated Y.hom] in
/-- The projective-immersion scheme isomorphism has the same exact
all-test counit identity as the general tensor base-change isomorphism. -/
@[simp]
theorem projectiveImmersionWeilRestrictionTensorBaseChangeIso_comparison
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionComparison C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y) T
        (p ≫ (projectiveImmersionWeilRestrictionTensorBaseChangeIso
          A B C Y n i hi).hom) =
      affineChartWeilRestrictionTensorBaseChangeComparison A B C Y T p := by
  let := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTensorBaseChangeIso_comparison A B C Y _ T p

end Langlands.AlgebraicGeometry.PointTopology
