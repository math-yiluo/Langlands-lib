import Langlands.GroupScheme.SchematicImage
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Functoriality of actual schematic-image subgroup functors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchematicImage

variable {k : Type u} [Field k]

local instance affine_group (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

variable {A B H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom A.X.hom] [IsAffineHom B.X.hom] [IsAffineHom H.X.hom]

omit [IsAffineHom B.X.hom] in
/-- Containment of the actual schematic image in a closed subgroup is
exactly containment of the original all-test point range. -/
theorem range_inclusion_le_iff (f : A ⟶ H) (j : B ⟶ H)
    (hj : IsClosedSubgroup j) :
    SubgroupFunctor.range (inclusion f) ≤ SubgroupFunctor.range j ↔
      SubgroupFunctor.range f ≤ SubgroupFunctor.range j := by
  simpa only [projection_inclusion] using
    (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
      (projection f) (inclusion f) j hj).symm

/-- Precomposition can only shrink the schematic-image subgroup functor. -/
theorem range_inclusion_comp_le (p : A ⟶ B) (q : B ⟶ H) :
    SubgroupFunctor.range (inclusion (p ≫ q)) ≤ SubgroupFunctor.range (inclusion q) := by
  apply (range_inclusion_le_iff (p ≫ q) (inclusion q)
    (inferInstanceAs (IsClosedImmersion (inclusion q).hom.hom.left))).mpr
  intro T x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr
    ⟨t ≫ p.hom.hom ≫ (projection q).hom.hom, by
      simp only [Category.assoc, ← Grp.comp_hom_hom, projection_inclusion]⟩

/-- A source isomorphism leaves the actual schematic-image subgroup unchanged. -/
theorem range_inclusion_iso_comp (e : A ≅ B) (q : B ⟶ H) :
    SubgroupFunctor.range (inclusion (e.hom ≫ q)) =
      SubgroupFunctor.range (inclusion q) := by
  apply le_antisymm (range_inclusion_comp_le e.hom q)
  have hh : e.inv ≫ (e.hom ≫ q) = q := by simp
  have h := range_inclusion_comp_le e.inv (e.hom ≫ q)
  rw [hh] at h
  exact h

variable {H' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H'.X.hom]

/-- An ambient isomorphism transports the actual schematic image on every
test scheme. -/
theorem range_inclusion_comp_iso (f : A ⟶ H) (e : H ≅ H') :
    SubgroupFunctor.range (inclusion (f ≫ e.hom)) =
      (SubgroupFunctor.range (inclusion f)).comap e.inv := by
  have hclosed : IsClosedSubgroup (inclusion f ≫ e.hom) := by
    change IsClosedImmersion ((inclusion f).hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  have heq := range_eq_of_dominantFactorizations
    (projection (f ≫ e.hom)) (projection f)
    (inclusion (f ≫ e.hom)) (inclusion f ≫ e.hom)
    (inferInstanceAs (IsClosedImmersion (inclusion (f ≫ e.hom)).hom.hom.left))
    hclosed (by rw [projection_inclusion, ← Category.assoc,
      projection_inclusion])
  exact heq.trans (SubgroupFunctor.range_comp_iso (inclusion f) e)

section BaseChange

variable {L : Type u} [Field L]
  (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) [Flat b]

local instance baseChange_affine (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Flat field-coefficient pullback preserves the all-test subgroup functor
of the actual schematic image. -/
theorem range_inclusion_baseChange (f : A ⟶ H) :
    SubgroupFunctor.range (inclusion ((GroupScheme.baseChange b).map f)) =
      (SubgroupFunctor.range (inclusion f)).baseChange b := by
  let F := GroupScheme.baseChange b
  have : IsSchemeTheoreticallyDominant (F.map (projection f)).hom.hom.left :=
    isSchemeTheoreticallyDominant_baseChange b (projection f)
  have hclosed : IsClosedSubgroup (F.map (inclusion f)) :=
    IsClosedSubgroup.baseChange b (inferInstanceAs
      (IsClosedImmersion (inclusion f).hom.hom.left))
  have heq := range_eq_of_dominantFactorizations
    (projection (F.map f)) (F.map (projection f))
    (inclusion (F.map f)) (F.map (inclusion f))
    (inferInstanceAs (IsClosedImmersion (inclusion (F.map f)).hom.hom.left)) hclosed
    (by rw [projection_inclusion, ← F.map_comp, projection_inclusion])
  exact heq.trans (SubgroupFunctor.range_baseChangeHom b (inclusion f))

/-- Closed containment, precomposition, isomorphism transport and flat
coefficient pullback for actual schematic-image subgroup functors. -/
def FunctorialityStatement (L : Type u) [Field L]
    (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) [Flat b] : Prop :=
  (∀ (f : A ⟶ H) (j : B ⟶ H), IsClosedSubgroup j →
    (SubgroupFunctor.range (inclusion f) ≤ SubgroupFunctor.range j ↔
      SubgroupFunctor.range f ≤ SubgroupFunctor.range j)) ∧
  (∀ (p : A ⟶ B) (q : B ⟶ H),
    SubgroupFunctor.range (inclusion (p ≫ q)) ≤
      SubgroupFunctor.range (inclusion q)) ∧
  (∀ (e : A ≅ B) (q : B ⟶ H),
    SubgroupFunctor.range (inclusion (e.hom ≫ q)) =
      SubgroupFunctor.range (inclusion q)) ∧
  (∀ (f : A ⟶ H) (e : H ≅ H'),
    SubgroupFunctor.range (inclusion (f ≫ e.hom)) =
      (SubgroupFunctor.range (inclusion f)).comap e.inv) ∧
  (∀ (f : A ⟶ H),
    SubgroupFunctor.range (inclusion ((GroupScheme.baseChange b).map f)) =
      (SubgroupFunctor.range (inclusion f)).baseChange b)

theorem functoriality (L : Type u) [Field L]
    (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) [Flat b] :
    FunctorialityStatement (A := A) (B := B) (H := H) (H' := H') L b :=
  ⟨range_inclusion_le_iff, range_inclusion_comp_le, range_inclusion_iso_comp,
    range_inclusion_comp_iso, range_inclusion_baseChange b⟩

end BaseChange
end Langlands.GroupScheme.SchematicImage
