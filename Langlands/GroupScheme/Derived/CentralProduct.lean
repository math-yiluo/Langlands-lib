import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Derived.PerfectQuotientImage
import Langlands.GroupScheme.Derived.SplitTorusTransport
import Langlands.GroupScheme.Reductive.CommutingMultiplication

/-! # Full derived subgroups of fpqc central products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G Z D E : GroupScheme S}

/-- A central factor does not change the commutator of two product points. -/
theorem commutator_subgroupMultiplication_of_isCentral
    (i : Z ⟶ G) (d : D ⟶ G) (hi : IsCentral i)
    {T : Over S} (x y : T ⟶ Z.X ⊗ D.X) :
    (x ≫ subgroupMultiplication i d) * (y ≫ subgroupMultiplication i d) *
        (x ≫ subgroupMultiplication i d)⁻¹ * (y ≫ subgroupMultiplication i d)⁻¹ =
      ((x ≫ snd Z.X D.X) * (y ≫ snd Z.X D.X) *
        (x ≫ snd Z.X D.X)⁻¹ * (y ≫ snd Z.X D.X)⁻¹) ≫ d.hom.hom := by
  simp only [subgroupMultiplication, MonObj.comp_mul, ← Category.assoc,
    MonObj.mul_comp, GrpObj.inv_comp]
  rw [(commute_of_mem_center (hi T (x ≫ fst Z.X D.X)) _).eq,
    (commute_of_mem_center (hi T (y ≫ fst Z.X D.X)) _).eq]
  exact commutator_mul_central _ _ _ _
    (commute_of_mem_center (hi T (x ≫ fst Z.X D.X)))
    (commute_of_mem_center (hi T (y ≫ fst Z.X D.X)))

/-- A closed factor contains every commutator if its multiplication with a
central factor is faithfully flat and quasi-compact. -/
theorem containsCommutators_range_of_fpqc_centralProduct
    (i : Z ⟶ G) (d : D ⟶ G) (hi : IsCentral i) (hd : IsClosedSubgroup d)
    [QuasiCompact (subgroupMultiplication i d).left]
    [Flat (subgroupMultiplication i d).left]
    [Surjective (subgroupMultiplication i d).left] :
    (SubgroupFunctor.range d).ContainsCommutators := by
  let hc := fun (T : Over S) (z : T ⟶ Z.X) (x : T ⟶ D.X) =>
    commute_of_mem_center (hi T z) (x ≫ d.hom.hom)
  let q := commutingSubgroupMultiplicationHom i d hc
  have : QuasiCompact q.hom.hom.left := inferInstanceAs
    (QuasiCompact (subgroupMultiplication i d).left)
  have : Flat q.hom.hom.left := inferInstanceAs
    (Flat (subgroupMultiplication i d).left)
  have : Surjective q.hom.hom.left := inferInstanceAs
    (Surjective (subgroupMultiplication i d).left)
  have : IsClosedImmersion d.hom.hom.left := hd
  have := CommutatorDescent.effectiveEpi_tensorHom q
  let P := (Z ⊗ D).X
  let w : P ⊗ P ⟶ D.X :=
    (fst P P ≫ snd Z.X D.X) * (snd P P ≫ snd Z.X D.X) *
      (fst P P ≫ snd Z.X D.X)⁻¹ * (snd P P ≫ snd Z.X D.X)⁻¹
  have hw : w ≫ d.hom.hom =
      (q.hom.hom ⊗ₘ q.hom.hom) ≫ commutatorMap (𝟙 G) (𝟙 G) := by
    rw [commutatorMap_points]
    simp only [tensorHom_fst, tensorHom_snd, Grp.id_hom_hom, Category.comp_id]
    exact (commutator_subgroupMultiplication_of_isCentral i d hi (fst P P) (snd P P)).symm
  have hw' : w.left ≫ d.hom.hom.left =
      (q.hom.hom ⊗ₘ q.hom.hom).left ≫ (commutatorMap (𝟙 G) (𝟙 G)).left :=
    congrArg (fun f => f.left) hw
  obtain ⟨l, hl⟩ := PerfectQuotientImage.exists_lift_of_effectiveEpi _ _ _ _ hw'
  have hlw : l ≫ D.X.hom = (G.X ⊗ G.X).hom := by
    rw [← Over.w d.hom.hom, ← Category.assoc, hl, Over.w]
  let lO : G.X ⊗ G.X ⟶ D.X := Over.homMk l hlw
  have hlO : lO ≫ d.hom.hom = commutatorMap (𝟙 G) (𝟙 G) :=
    Over.OverMorphism.ext hl
  intro T x y
  refine SubgroupFunctor.mem_range.mpr ⟨lift x y ≫ lO, ?_⟩
  rw [Category.assoc, hlO, commutatorMap_lift]
  simp only [Grp.id_hom_hom, Category.comp_id]

/-- A perfect closed factor in an fpqc central product is the full derived
subgroup, on every test scheme. -/
theorem isDerivedSubgroup_of_fpqc_centralProduct
    (i : Z ⟶ G) (d : D ⟶ G) (hi : IsCentral i) (hd : IsClosedSubgroup d)
    [QuasiCompact (subgroupMultiplication i d).left]
    [Flat (subgroupMultiplication i d).left]
    [Surjective (subgroupMultiplication i d).left]
    (hD : derivedSubgroup D = ⊤) : IsDerivedSubgroup d := by
  refine ⟨hd, le_antisymm ?_ ?_⟩
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply mem_derivedSubgroup_comp d
    rw [hD]
    exact Subgroup.mem_top _
  · exact derivedSubgroup_le_range d hd
      (containsCommutators_range_of_fpqc_centralProduct i d hi hd)

/-- The actual comparison with any supplied full derived-subgroup
representative of an fpqc central product with a perfect closed factor. -/
def centralProductDerivedIso
    (i : Z ⟶ G) (d : D ⟶ G) (hi : IsCentral i) (hd : IsClosedSubgroup d)
    [QuasiCompact (subgroupMultiplication i d).left]
    [Flat (subgroupMultiplication i d).left]
    [Surjective (subgroupMultiplication i d).left]
    (hD : derivedSubgroup D = ⊤) {e : E ⟶ G} (he : IsDerivedSubgroup e) : D ≅ E :=
  (isDerivedSubgroup_of_fpqc_centralProduct i d hi hd hD).iso he

@[reassoc]
theorem centralProductDerivedIso_hom_comp
    (i : Z ⟶ G) (d : D ⟶ G) (hi : IsCentral i) (hd : IsClosedSubgroup d)
    [QuasiCompact (subgroupMultiplication i d).left]
    [Flat (subgroupMultiplication i d).left]
    [Surjective (subgroupMultiplication i d).left]
    (hD : derivedSubgroup D = ⊤) {e : E ⟶ G} (he : IsDerivedSubgroup e) :
    (centralProductDerivedIso i d hi hd hD he).hom ≫ e = d :=
  (isDerivedSubgroup_of_fpqc_centralProduct i d hi hd hD).iso_hom_comp he

end Langlands.GroupScheme
