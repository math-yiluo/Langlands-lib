import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionTensorBaseChange
import Mathlib.CategoryTheory.Extensive

/-! # Actual finite-product decomposition for Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {ι : Type u} (B : ι → Type u) [∀ i, CommRing (B i)] [hι : Finite ι]

/-- The actual spectrum map of the coordinate ring projection. -/
def finiteProductSpecProjection (i : ι) :
    Spec (CommRingCat.of (B i)) ⟶ Spec (CommRingCat.of (∀ j, B j)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom B i))

/-- Every actual scheme over a finite product ring is the coproduct of
its pullbacks to the factors, using the actual pullback projections. -/
def finiteProductPullbackCofanIsColimit
    (X : Over (Spec (CommRingCat.of (∀ i, B i)))) :
    IsColimit (Cofan.mk X.left (fun i =>
      pullback.fst X.hom (finiteProductSpecProjection B i))) := by
  let a := Cofan.mk (Spec (CommRingCat.of (∀ i, B i)))
    (finiteProductSpecProjection B)
  have ha : IsColimit a :=
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc a).mpr
      (inferInstanceAs (IsIso (sigmaSpec (fun i => CommRingCat.of (B i)))))).some
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts ha
  exact (hu.nonempty_isColimit_of_pullbackCone_left
    (finiteProductSpecProjection B) (𝟙 _) X.hom
    (fun i => pullback.cone X.hom (finiteProductSpecProjection B i))
    (fun i => pullback.isLimit X.hom (finiteProductSpecProjection B i))
    (PullbackCone.mk (𝟙 _) X.hom (by simp)) (IsPullback.id_horiz X.hom).isLimit
    (Cofan.mk X.left (fun i => pullback.fst X.hom (finiteProductSpecProjection B i)))
    (Iso.refl _) (by simp [a, Cofan.inj]) (by simp)
    (by simp [a, Cofan.inj, pullback.condition])).some

/-- Gluing actual relative morphisms on the disjoint finite factor schemes. -/
def finiteProductOverHomGlue
    (X Y : Over (Spec (CommRingCat.of (∀ i, B i))))
    (g : ∀ i, (Over.pullback (finiteProductSpecProjection B i)).obj X ⟶
      (Over.pullback (finiteProductSpecProjection B i)).obj Y) : X ⟶ Y :=
  Over.homMk
    ((finiteProductPullbackCofanIsColimit B X).desc
      (Cofan.mk Y.left (fun i =>
        (g i).left ≫ pullback.fst Y.hom (finiteProductSpecProjection B i)))) (by
      apply (finiteProductPullbackCofanIsColimit B X).hom_ext
      intro i
      obtain ⟨i⟩ := i
      dsimp
      have hf := (finiteProductPullbackCofanIsColimit B X).fac
        (Cofan.mk Y.left (fun j =>
          (g j).left ≫ pullback.fst Y.hom (finiteProductSpecProjection B j))) ⟨i⟩
      dsimp at hf
      rw [← Category.assoc, hf]
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (g i).left ≫ pullback.snd Y.hom (finiteProductSpecProjection B i) =
          pullback.snd X.hom (finiteProductSpecProjection B i) from Over.w (g i),
        pullback.condition])

@[reassoc (attr := simp)]
theorem finiteProductOverHomGlue_fst
    (X Y : Over (Spec (CommRingCat.of (∀ i, B i))))
    (g : ∀ i, (Over.pullback (finiteProductSpecProjection B i)).obj X ⟶
      (Over.pullback (finiteProductSpecProjection B i)).obj Y) (i : ι) :
    pullback.fst X.hom (finiteProductSpecProjection B i) ≫
        (finiteProductOverHomGlue B X Y g).left =
      (g i).left ≫ pullback.fst Y.hom (finiteProductSpecProjection B i) :=
  (finiteProductPullbackCofanIsColimit B X).fac _ ⟨i⟩

/-- Actual morphisms over a finite product ring are exactly compatible
factor morphisms; no finite-type or separation hypothesis is required. -/
def finiteProductOverHomEquiv
    (X Y : Over (Spec (CommRingCat.of (∀ i, B i)))) :
    (X ⟶ Y) ≃ (∀ i, (Over.pullback (finiteProductSpecProjection B i)).obj X ⟶
      (Over.pullback (finiteProductSpecProjection B i)).obj Y) where
  toFun f i := (Over.pullback (finiteProductSpecProjection B i)).map f
  invFun := finiteProductOverHomGlue B X Y
  left_inv f := by
    apply Over.OverMorphism.ext
    apply (finiteProductPullbackCofanIsColimit B X).hom_ext
    rintro ⟨i⟩
    simp [Over.pullback_map_left, finiteProductOverHomGlue_fst]
  right_inv g := by
    funext i
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [Over.pullback_map_left, finiteProductOverHomGlue_fst]
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact (Over.w (g i)).symm

@[simp]
theorem finiteProductOverHomEquiv_apply
    (X Y : Over (Spec (CommRingCat.of (∀ i, B i)))) (f : X ⟶ Y) (i : ι) :
    finiteProductOverHomEquiv B X Y f i =
      (Over.pullback (finiteProductSpecProjection B i)).map f := rfl

/-- The finite-product morphism equivalence is natural in its source. -/
theorem finiteProductOverHomEquiv_natural
    {X X' Y : Over (Spec (CommRingCat.of (∀ i, B i)))}
    (f : X ⟶ X') (g : X' ⟶ Y) (i : ι) :
    finiteProductOverHomEquiv B X Y (f ≫ g) i =
      (Over.pullback (finiteProductSpecProjection B i)).map f ≫
        finiteProductOverHomEquiv B X' Y g i :=
  (Over.pullback (finiteProductSpecProjection B i)).map_comp f g

omit hι

variable (A : Type u) [CommRing A] [∀ i, Algebra A (B i)]

/-- The spectrum coordinate projection is compatible with the original base. -/
@[reassoc (attr := simp)]
theorem finiteProductSpecProjection_comp (i : ι) :
    finiteProductSpecProjection B i ≫ Spec.algebraMap A (∀ j, B j) =
      Spec.algebraMap A (B i) := by
  rw [finiteProductSpecProjection, ← Spec.map_comp]
  rfl

/-- The actual iterated test pullback is the usual test over the factor ring. -/
def finiteProductBaseChangeTestIso
    (T : Over (Spec (CommRingCat.of A))) (i : ι) :
    (Over.pullback (finiteProductSpecProjection B i)).obj
        (ringBaseChange A (∀ j, B j) T) ≅ ringBaseChange A (B i) T :=
  Over.isoMk
    ((pullbackLeftPullbackSndIso T.hom (Spec.algebraMap A (∀ j, B j))
      (finiteProductSpecProjection B i)).trans
      (pullback.congrHom rfl (finiteProductSpecProjection_comp B A i)))
    (by simp [ringBaseChange, pullback.congrHom])

/-- Naturality of the actual factor test identification. -/
theorem finiteProductBaseChangeTestIso_natural
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S) (i : ι) :
    (Over.pullback (finiteProductSpecProjection B i)).map
        ((Over.pullback (Spec.algebraMap A (∀ j, B j))).map f) ≫
        (finiteProductBaseChangeTestIso B A S i).hom =
      (finiteProductBaseChangeTestIso B A T i).hom ≫
        (Over.pullback (Spec.algebraMap A (B i))).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [finiteProductBaseChangeTestIso, Over.pullback_map_left, Category.assoc,
      pullback.congrHom]
  · simp [finiteProductBaseChangeTestIso, Over.pullback_map_left, Category.assoc,
      pullback.congrHom]

/-- Naturality of the inverse factor test identification. -/
theorem finiteProductBaseChangeTestIso_inv_natural
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S) (i : ι) :
    (finiteProductBaseChangeTestIso B A T i).inv ≫
        (Over.pullback (finiteProductSpecProjection B i)).map
          ((Over.pullback (Spec.algebraMap A (∀ j, B j))).map f) =
      (Over.pullback (Spec.algebraMap A (B i))).map f ≫
        (finiteProductBaseChangeTestIso B A S i).inv := by
  apply (cancel_mono (finiteProductBaseChangeTestIso B A S i).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [finiteProductBaseChangeTestIso_natural, Iso.inv_hom_id_assoc]

/-- The actual factor of a scheme over the product ring. -/
def finiteProductFactorScheme
    (Y : Over (Spec (CommRingCat.of (∀ j, B j)))) (i : ι) :
    Over (Spec (CommRingCat.of (B i))) :=
  (Over.pullback (finiteProductSpecProjection B i)).obj Y

/-- Finite-set affine neighborhoods descend to each actual factor pullback. -/
theorem hasFiniteAffineNeighborhoods_finiteProductFactor
    (Y : Over (Spec (CommRingCat.of (∀ j, B j))))
    (hY : HasFiniteAffineNeighborhoods Y.left) (i : ι) :
    HasFiniteAffineNeighborhoods (finiteProductFactorScheme B Y i).left := by
  let : IsAffineHom (pullback.fst Y.hom (finiteProductSpecProjection B i)) :=
    MorphismProperty.pullback_fst Y.hom (finiteProductSpecProjection B i) inferInstance
  exact hasFiniteAffineNeighborhoods_of_affine
    (pullback.fst Y.hom (finiteProductSpecProjection B i)) hY

include hι

variable [∀ i, Module.Finite A (B i)] [∀ i, Module.Projective A (B i)]

/-- A finite product of projective algebras is projective over the base. -/
instance finiteProductAlgebraProjective : Module.Projective A (∀ i, B i) := by
  classical
  let := Fintype.ofFinite ι
  exact Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := A) (M := B))

variable (Y : Over (Spec (CommRingCat.of (∀ j, B j)))) [LocallyOfFiniteType Y.hom]

local instance finiteProductFactorLocallyOfFiniteType (i : ι) :
    LocallyOfFiniteType (finiteProductFactorScheme B Y i).hom :=
  inferInstanceAs
    (LocallyOfFiniteType (pullback.snd Y.hom (finiteProductSpecProjection B i)))

/-- The canonical component of the Weil comparison, obtained by the actual
factor pullback of the original counit and the actual test identification. -/
def affineChartWeilRestrictionProductComparison
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    ringBaseChange A (B i) T ⟶ finiteProductFactorScheme B Y i :=
  (finiteProductBaseChangeTestIso B A T i).inv ≫
    (Over.pullback (finiteProductSpecProjection B i)).map
      (affineChartWeilRestrictionComparison A (∀ i, B i) Y T p)

/-- The component counit comparison is natural on all actual test schemes. -/
theorem affineChartWeilRestrictionProductComparison_natural
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (p : S ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    affineChartWeilRestrictionProductComparison B A Y T (f ≫ p) i =
      (Over.pullback (Spec.algebraMap A (B i))).map f ≫
        affineChartWeilRestrictionProductComparison B A Y S p i := by
  simp only [affineChartWeilRestrictionProductComparison,
    affineChartWeilRestrictionComparison_natural, Functor.map_comp]
  rw [← Category.assoc, finiteProductBaseChangeTestIso_inv_natural, Category.assoc]

variable [IsSeparated Y.hom]

local instance finiteProductFactorIsSeparated (i : ι) :
    IsSeparated (finiteProductFactorScheme B Y i).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y.hom (finiteProductSpecProjection B i)))

/-- The original Weil scheme represents the product of the actual factor
Weil functors, on arbitrary actual test schemes. -/
def affineChartWeilRestrictionProductTestEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) ≃
      (∀ i, ringBaseChange A (B i) T ⟶ finiteProductFactorScheme B Y i) :=
  ((affineChartWeilRestrictionTestEquiv A (∀ i, B i) Y hY T).trans
    (finiteProductOverHomEquiv B _ Y)).trans
      (Equiv.piCongrRight (fun i => Iso.homCongr
        (finiteProductBaseChangeTestIso B A T i)
        (Iso.refl (finiteProductFactorScheme B Y i))))

/-- The product test equivalence uses exactly the factor counit maps. -/
@[simp]
theorem affineChartWeilRestrictionProductTestEquiv_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    affineChartWeilRestrictionProductTestEquiv B A Y hY T p i =
      affineChartWeilRestrictionProductComparison B A Y T p i := by
  simp [affineChartWeilRestrictionProductTestEquiv,
    affineChartWeilRestrictionProductComparison, Iso.homCongr]
  exact Category.comp_id _

/-- All-test equivalence to the separately glued factor Weil schemes. -/
def affineChartWeilRestrictionProductRepresentingEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) ≃
      (∀ i, T ⟶ affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) :=
  (affineChartWeilRestrictionProductTestEquiv B A Y hY T).trans
    (Equiv.piCongrRight (fun i =>
      (affineChartWeilRestrictionTestEquiv A (B i) (finiteProductFactorScheme B Y i)
        (hasFiniteAffineNeighborhoods_finiteProductFactor B Y hY i) T).symm))

/-- Naturality in the source of the product representing equivalence. -/
theorem affineChartWeilRestrictionProductRepresentingEquiv_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (p : S ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    affineChartWeilRestrictionProductRepresentingEquiv B A Y hY T (f ≫ p) i =
      f ≫ affineChartWeilRestrictionProductRepresentingEquiv B A Y hY S p i := by
  change affineChartWeilRestrictionInverse A (B i) (finiteProductFactorScheme B Y i)
    _ T (affineChartWeilRestrictionProductTestEquiv B A Y hY T (f ≫ p) i) = _
  rw [affineChartWeilRestrictionProductTestEquiv_apply,
    affineChartWeilRestrictionProductComparison_natural]
  exact affineChartWeilRestrictionInverse_natural A (B i)
    (finiteProductFactorScheme B Y i) _ f _

/-- The canonical projection to the separately constructed factor Weil scheme. -/
def affineChartWeilRestrictionProductProjection
    (hY : HasFiniteAffineNeighborhoods Y.left) (i : ι) :
    affineChartWeilRestriction A (∀ i, B i) Y ⟶
      affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i) :=
  affineChartWeilRestrictionProductRepresentingEquiv B A Y hY _ (𝟙 _) i

/-- Every test comparison to the factor representing scheme is composition
with the same canonical projection. -/
theorem affineChartWeilRestrictionProductRepresentingEquiv_eq_comp
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    affineChartWeilRestrictionProductRepresentingEquiv B A Y hY T p i =
      p ≫ affineChartWeilRestrictionProductProjection B A Y hY i := by
  simpa only [Category.comp_id, affineChartWeilRestrictionProductProjection] using
    affineChartWeilRestrictionProductRepresentingEquiv_natural B A Y hY p (𝟙 _) i

/-- The actual original Weil scheme, with its canonical factor projections. -/
def affineChartWeilRestrictionProductFan
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    Fan (fun i => affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) :=
  Fan.mk (affineChartWeilRestriction A (∀ i, B i) Y)
    (affineChartWeilRestrictionProductProjection B A Y hY)

/-- The original Weil scheme is the finite product of the separately glued
factor Weil schemes, by its proved all-test universal property. -/
def affineChartWeilRestrictionProductFanIsLimit
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    IsLimit (affineChartWeilRestrictionProductFan B A Y hY) := by
  refine Fan.IsLimit.mk _
    (fun s => (affineChartWeilRestrictionProductRepresentingEquiv B A Y hY s.pt).symm
      s.proj) ?_ ?_
  · intro s i
    change _ ≫ affineChartWeilRestrictionProductProjection B A Y hY i = _
    rw [← affineChartWeilRestrictionProductRepresentingEquiv_eq_comp]
    exact congrFun
      ((affineChartWeilRestrictionProductRepresentingEquiv B A Y hY s.pt).apply_symm_apply
        s.proj) i
  · intro s m hm
    apply (affineChartWeilRestrictionProductRepresentingEquiv B A Y hY s.pt).injective
    rw [Equiv.apply_symm_apply]
    funext i
    rw [affineChartWeilRestrictionProductRepresentingEquiv_eq_comp]
    exact hm i

/-- The canonical finite-product isomorphism of actual Weil schemes. -/
def affineChartWeilRestrictionProductIso
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    affineChartWeilRestriction A (∀ i, B i) Y ≅
      ∏ᶜ (fun i => affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) :=
  IsLimit.conePointUniqueUpToIso (affineChartWeilRestrictionProductFanIsLimit B A Y hY)
    (productIsProduct _)

/-- The product isomorphism has exactly the specified canonical projections. -/
@[reassoc (attr := simp)]
theorem affineChartWeilRestrictionProductIso_hom_π
    (hY : HasFiniteAffineNeighborhoods Y.left) (i : ι) :
    (affineChartWeilRestrictionProductIso B A Y hY).hom ≫
        Pi.π (fun j => affineChartWeilRestriction A (B j)
          (finiteProductFactorScheme B Y j)) i =
      affineChartWeilRestrictionProductProjection B A Y hY i :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (affineChartWeilRestrictionProductFanIsLimit B A Y hY) (productIsProduct _) ⟨i⟩

/-- The canonical factor projection is characterized by the actual counit
comparison on every test scheme. -/
@[simp]
theorem affineChartWeilRestrictionProductProjection_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    affineChartWeilRestrictionComparison A (B i) (finiteProductFactorScheme B Y i) T
        (p ≫ affineChartWeilRestrictionProductProjection B A Y hY i) =
      affineChartWeilRestrictionProductComparison B A Y T p i := by
  rw [← affineChartWeilRestrictionProductRepresentingEquiv_eq_comp]
  change affineChartWeilRestrictionTestEquiv A (B i) (finiteProductFactorScheme B Y i)
      (hasFiniteAffineNeighborhoods_finiteProductFactor B Y hY i) T
      ((affineChartWeilRestrictionTestEquiv A (B i) (finiteProductFactorScheme B Y i)
        (hasFiniteAffineNeighborhoods_finiteProductFactor B Y hY i) T).symm
        (affineChartWeilRestrictionProductTestEquiv B A Y hY T p i)) = _
  rw [Equiv.apply_symm_apply, affineChartWeilRestrictionProductTestEquiv_apply]

/-- Exact all-test counit identity for the finite-product scheme isomorphism. -/
@[simp]
theorem affineChartWeilRestrictionProductIso_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    affineChartWeilRestrictionComparison A (B i) (finiteProductFactorScheme B Y i) T
        (p ≫ (affineChartWeilRestrictionProductIso B A Y hY).hom ≫
          Pi.π (fun j => affineChartWeilRestriction A (B j)
            (finiteProductFactorScheme B Y j)) i) =
      affineChartWeilRestrictionProductComparison B A Y T p i := by
  rw [affineChartWeilRestrictionProductIso_hom_π]
  exact affineChartWeilRestrictionProductProjection_comparison B A Y hY T p i

omit [IsSeparated Y.hom] in
/-- An actual projective immersion supplies the original geometric premises
for the canonical finite-product Weil isomorphism. -/
def projectiveImmersionWeilRestrictionProductIso
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (∀ i, B i) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (∀ i, B i) n = Y.hom) :
    affineChartWeilRestriction A (∀ i, B i) Y ≅
      ∏ᶜ (fun i => affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) := by
  letI := isSeparated_of_projectiveImmersion (∀ i, B i) Y n j hj
  exact affineChartWeilRestrictionProductIso B A Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion (∀ i, B i) n j)

omit [IsSeparated Y.hom] in
/-- The projective-immersion specialization has the same actual all-test
counit formula, with no extra geometry supplied for the factor targets. -/
@[simp]
theorem projectiveImmersionWeilRestrictionProductIso_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (∀ i, B i) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (∀ i, B i) n = Y.hom)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A (∀ i, B i) Y) (i : ι) :
    affineChartWeilRestrictionComparison A (B i) (finiteProductFactorScheme B Y i) T
        (p ≫ (projectiveImmersionWeilRestrictionProductIso B A Y n j hj).hom ≫
          Pi.π (fun k => affineChartWeilRestriction A (B k)
            (finiteProductFactorScheme B Y k)) i) =
      affineChartWeilRestrictionProductComparison B A Y T p i := by
  let := isSeparated_of_projectiveImmersion (∀ i, B i) Y n j hj
  exact affineChartWeilRestrictionProductIso_comparison B A Y _ T p i

end Langlands.AlgebraicGeometry.PointTopology
