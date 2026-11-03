import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Langlands.GroupScheme.FixedRepresentabilityFieldReduction
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # The closed locus of conjugation into a closed subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ConjugationInto

variable {S : Scheme.{u}} {H B G : GroupScheme S}

/-- Every refinement of `g` conjugates the full image of `s` into `b`. -/
def Holds (s : H ⟶ G) (b : B ⟶ G) {T : Over S} (g : T ⟶ G.X) : Prop :=
  ∀ (V : Over S) (a : V ⟶ T) (h : V ⟶ H.X),
    (a ≫ g)⁻¹ * (h ≫ s.hom.hom) * (a ≫ g) ∈ (SubgroupFunctor.range b).carrier V

theorem Holds.comp {s : H ⟶ G} {b : B ⟶ G} {T V : Over S}
    {g : T ⟶ G.X} (hg : Holds s b g) (a : V ⟶ T) : Holds s b (a ≫ g) := by
  intro W c h
  simpa only [Category.assoc] using hg W (c ≫ a) h

/-- The actual morphism `(h,g) ↦ g⁻¹ s(h) g`. -/
def conjugationHom (s : H ⟶ G) : H.X ⊗ G.X ⟶ G.X :=
  (snd H.X G.X)⁻¹ * (fst H.X G.X ≫ s.hom.hom) * snd H.X G.X

theorem lift_conjugationHom (s : H ⟶ G) {T : Over S}
    (h : T ⟶ H.X) (g : T ⟶ G.X) :
    lift h g ≫ conjugationHom s = g⁻¹ * (h ≫ s.hom.hom) * g := by
  simp only [conjugationHom, MonObj.comp_mul, GrpObj.comp_inv,
    lift_snd, lift_fst_assoc]

/-- Pull back the closed target subgroup along the inverse-conjugation map. -/
abbrev productLocus (s : H ⟶ G) (b : B ⟶ G) : Over S :=
  pullback (conjugationHom s) b.hom.hom

def productInclusion (s : H ⟶ G) (b : B ⟶ G) :
    productLocus s b ⟶ H.X ⊗ G.X :=
  pullback.fst _ _

theorem productInclusion_isClosedImmersion (s : H ⟶ G) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) : IsClosedImmersion (productInclusion s b).left := by
  exact MorphismProperty.of_isPullback
    (((IsPullback.of_hasPullback (conjugationHom s) b.hom.hom).map
      (Over.forget S)).flip) hb

/-- The all-test transporter condition is exactly the universal product factorization. -/
theorem holds_iff_factors (s : H ⟶ G) (b : B ⟶ G) {T : Over S}
    (g : T ⟶ G.X) :
    Holds s b g ↔
      ∃ q : H.X ⊗ T ⟶ productLocus s b, q ≫ productInclusion s b = H.X ◁ g := by
  have huniv : lift (fst H.X T) (snd H.X T ≫ g) = H.X ◁ g := by
    apply hom_ext <;> simp
  constructor
  · intro hg
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp
      (hg (H.X ⊗ T) (snd H.X T) (fst H.X T))
    have he : (H.X ◁ g) ≫ conjugationHom s = v ≫ b.hom.hom := by
      rw [← huniv, lift_conjugationHom, hv]
    exact ⟨pullback.lift (H.X ◁ g) v he, pullback.lift_fst _ _ _⟩
  · rintro ⟨q, hq⟩ V a h
    refine SubgroupFunctor.mem_range.mpr
      ⟨lift h a ≫ q ≫ pullback.snd _ _, ?_⟩
    calc
      (lift h a ≫ q ≫ pullback.snd (conjugationHom s) b.hom.hom) ≫ b.hom.hom =
          lift h a ≫ q ≫ productInclusion s b ≫ conjugationHom s := by
        simp only [Category.assoc, productInclusion, pullback.condition]
      _ = lift h (a ≫ g) ≫ conjugationHom s := by
        rw [← Category.assoc q, hq, ← Category.assoc, lift_whiskerLeft]
      _ = (a ≫ g)⁻¹ * (h ≫ s.hom.hom) * (a ≫ g) := lift_conjugationHom s h _

section Field

variable {k : Type u} [Field k]
variable {H B G : GroupScheme (Spec (CommRingCat.of k))}

/-- The transporter into any closed subgroup is represented by an actual closed
subscheme of the ambient group. The source need only be affine. -/
theorem exists_closed_locus [IsAffineHom H.X.hom]
    (s : H ⟶ G) (b : B ⟶ G) (hb : IsClosedSubgroup b) :
    ∃ (Z : Over (Spec (CommRingCat.of k))) (i : Z ⟶ G.X),
      IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
        (∃ z : T ⟶ Z, z ≫ i = g) ↔ Holds s b g := by
  obtain ⟨Z, i, hi, h⟩ :=
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus
      (CommRingCat.of k) H.X inferInstance (flat_field k H)
      (hasFpqcProjectiveCoordinateModule_field k H)
      G.X (productLocus s b) (productInclusion s b)
      (productInclusion_isClosedImmersion s b hb)
  exact ⟨Z, i, hi, fun T g => (h T g).trans (holds_iff_factors s b g).symm⟩

/-- A chosen actual closed inverse-conjugation locus. -/
def locus [IsAffineHom H.X.hom]
    (s : H ⟶ G) (b : B ⟶ G) (hb : IsClosedSubgroup b) :
    Over (Spec (CommRingCat.of k)) :=
  (exists_closed_locus s b hb).choose

def inclusion [IsAffineHom H.X.hom]
    (s : H ⟶ G) (b : B ⟶ G) (hb : IsClosedSubgroup b) :
    locus s b hb ⟶ G.X :=
  (exists_closed_locus s b hb).choose_spec.choose

theorem inclusion_isClosedImmersion [IsAffineHom H.X.hom]
    (s : H ⟶ G) (b : B ⟶ G) (hb : IsClosedSubgroup b) :
    IsClosedImmersion (inclusion s b hb).left :=
  (exists_closed_locus s b hb).choose_spec.choose_spec.1

theorem factors_inclusion_iff [IsAffineHom H.X.hom]
    (s : H ⟶ G) (b : B ⟶ G) (hb : IsClosedSubgroup b)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) :
    (∃ z : T ⟶ locus s b hb, z ≫ inclusion s b hb = g) ↔ Holds s b g :=
  (exists_closed_locus s b hb).choose_spec.choose_spec.2 T g

end Field

end Langlands.GroupScheme.ConjugationInto
