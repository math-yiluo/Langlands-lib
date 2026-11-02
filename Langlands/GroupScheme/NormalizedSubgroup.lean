import Langlands.GroupScheme.SubgroupFunctor
import Mathlib.Algebra.Group.Conj

/-! # Conjugation on a normalized subgroup as a morphism of schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H K : GroupScheme S} (iH : H ⟶ G) (iK : K ⟶ G)

/-- Conjugation of the image of `H` by the image of `K`, before factoring through `H`. -/
def conjugationMap : K.X ⊗ H.X ⟶ G.X :=
  (fst K.X H.X ≫ iK.hom.hom) * (snd K.X H.X ≫ iH.hom.hom) *
    (fst K.X H.X ≫ iK.hom.hom)⁻¹

theorem lift_comp_conjugationMap {T : Over S} (g : T ⟶ K.X) (h : T ⟶ H.X) :
    lift g h ≫ conjugationMap iH iK =
      (g ≫ iK.hom.hom) * (h ≫ iH.hom.hom) * (g ≫ iK.hom.hom)⁻¹ := by
  simp only [conjugationMap, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, lift_snd_assoc]

/-- Normalization on every test scheme is equivalent to factorization of the actual
conjugation morphism through the subgroup. No monomorphism hypothesis is needed here. -/
theorem isNormalizedBy_range_iff_exists_conjugationMap :
    (range iH).IsNormalizedBy (range iK) ↔
      ∃ a : K.X ⊗ H.X ⟶ H.X, a ≫ iH.hom.hom = conjugationMap iH iK := by
  constructor
  · intro hn
    exact mem_range.1 (hn _ _ _ (mem_range.2 ⟨fst K.X H.X, rfl⟩)
      (mem_range.2 ⟨snd K.X H.X, rfl⟩))
  · rintro ⟨a, ha⟩ T g h hg hh
    obtain ⟨g', rfl⟩ := mem_range.1 hg
    obtain ⟨h', rfl⟩ := mem_range.1 hh
    refine mem_range.2 ⟨lift g' h' ≫ a, ?_⟩
    rw [Category.assoc, ha, lift_comp_conjugationMap]

variable (hn : (range iH).IsNormalizedBy (range iK))

/-- The scheme morphism giving the conjugation action on a normalized subgroup. When `iH`
is a monomorphism this is the unique factorization of `conjugationMap iH iK`. -/
def normalizedConjugation : K.X ⊗ H.X ⟶ H.X :=
  Classical.choose ((isNormalizedBy_range_iff_exists_conjugationMap iH iK).1 hn)

theorem normalizedConjugation_comp :
    normalizedConjugation iH iK hn ≫ iH.hom.hom = conjugationMap iH iK :=
  Classical.choose_spec ((isNormalizedBy_range_iff_exists_conjugationMap iH iK).1 hn)

theorem lift_comp_normalizedConjugation_comp {T : Over S}
    (g : T ⟶ K.X) (h : T ⟶ H.X) :
    (lift g h ≫ normalizedConjugation iH iK hn) ≫ iH.hom.hom =
      (g ≫ iK.hom.hom) * (h ≫ iH.hom.hom) * (g ≫ iK.hom.hom)⁻¹ := by
  rw [Category.assoc, normalizedConjugation_comp, lift_comp_conjugationMap]

/-- Restriction of the action is composition with the same morphism of schemes. -/
theorem normalizedConjugation_naturality {T T' : Over S} (f : T' ⟶ T)
    (g : T ⟶ K.X) (h : T ⟶ H.X) :
    f ≫ (lift g h ≫ normalizedConjugation iH iK hn) =
      lift (f ≫ g) (f ≫ h) ≫ normalizedConjugation iH iK hn := by
  rw [← Category.assoc, comp_lift]

variable [Mono iH.hom.hom]

theorem normalizedConjugation_unique (a : K.X ⊗ H.X ⟶ H.X)
    (ha : a ≫ iH.hom.hom = conjugationMap iH iK) :
    a = normalizedConjugation iH iK hn := by
  apply (cancel_mono iH.hom.hom).1
  rw [ha, normalizedConjugation_comp]

/-- The identity of `K` acts trivially on `H`. -/
theorem normalizedConjugation_one_left {T : Over S} (h : T ⟶ H.X) :
    lift (1 : T ⟶ K.X) h ≫ normalizedConjugation iH iK hn = h := by
  apply (cancel_mono iH.hom.hom).1
  rw [lift_comp_normalizedConjugation_comp, MonObj.one_comp]
  simp

/-- Multiplication in `K` acts by composition of the conjugation maps. -/
theorem normalizedConjugation_mul_left {T : Over S}
    (g g' : T ⟶ K.X) (h : T ⟶ H.X) :
    lift (g * g') h ≫ normalizedConjugation iH iK hn =
      lift g (lift g' h ≫ normalizedConjugation iH iK hn) ≫
        normalizedConjugation iH iK hn := by
  apply (cancel_mono iH.hom.hom).1
  rw [lift_comp_normalizedConjugation_comp, lift_comp_normalizedConjugation_comp,
    lift_comp_normalizedConjugation_comp, MonObj.mul_comp]
  simp only [mul_inv_rev, mul_assoc]

/-- Conjugation preserves the multiplication of `H`. -/
theorem normalizedConjugation_mul_right {T : Over S}
    (g : T ⟶ K.X) (h h' : T ⟶ H.X) :
    lift g (h * h') ≫ normalizedConjugation iH iK hn =
      (lift g h ≫ normalizedConjugation iH iK hn) *
        (lift g h' ≫ normalizedConjugation iH iK hn) := by
  apply (cancel_mono iH.hom.hom).1
  simp only [MonObj.mul_comp, lift_comp_normalizedConjugation_comp]
  exact conj_mul.symm

/-- Conjugation by a `T`-point of `K` is a group automorphism of the `T`-points of `H`. -/
def normalizedConjAut (T : Over S) (g : T ⟶ K.X) : MulAut (T ⟶ H.X) where
  toFun h := lift g h ≫ normalizedConjugation iH iK hn
  invFun h := lift g⁻¹ h ≫ normalizedConjugation iH iK hn
  left_inv h := by
    dsimp only
    rw [← normalizedConjugation_mul_left, inv_mul_cancel, normalizedConjugation_one_left]
  right_inv h := by
    dsimp only
    rw [← normalizedConjugation_mul_left, mul_inv_cancel, normalizedConjugation_one_left]
  map_mul' h h' := normalizedConjugation_mul_right iH iK hn g h h'

theorem normalizedConjAut_apply (T : Over S) (g : T ⟶ K.X) (h : T ⟶ H.X) :
    normalizedConjAut iH iK hn T g h = lift g h ≫ normalizedConjugation iH iK hn :=
  rfl

/-- The action on `T`-points by automorphisms, induced by the single morphism
`normalizedConjugation iH iK hn`. -/
def normalizedConjAction (T : Over S) : (T ⟶ K.X) →* MulAut (T ⟶ H.X) where
  toFun := normalizedConjAut iH iK hn T
  map_one' := MulEquiv.ext (normalizedConjugation_one_left iH iK hn)
  map_mul' g g' := MulEquiv.ext (normalizedConjugation_mul_left iH iK hn g g')

theorem normalizedConjAction_apply (T : Over S) (g : T ⟶ K.X) (h : T ⟶ H.X) :
    normalizedConjAction iH iK hn T g h = lift g h ≫ normalizedConjugation iH iK hn :=
  rfl

end Langlands.GroupScheme.SubgroupFunctor
