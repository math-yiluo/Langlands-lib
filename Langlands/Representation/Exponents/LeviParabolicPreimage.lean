import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Actual inverse images under a supplied Levi retraction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviPreimage

variable {S : Scheme.{u}} {P M U Q : GroupScheme S}
    (l : M ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)]
    (hn : (SubgroupFunctor.range r).IsNormal) (q : Q ⟶ M)

/-- The actual inverse image of the original inner subgroup. -/
abbrev group : GroupScheme S := SubgroupPreimage.groupScheme (leviRetraction l r hn) q

/-- Its original inclusion into the outer group. -/
abbrev inclusion : group l r hn q ⟶ P :=
  SubgroupPreimage.inclusion (leviRetraction l r hn) q

/-- The projection onto the original inner subgroup. -/
abbrev projection : group l r hn q ⟶ Q :=
  SubgroupPreimage.projection (leviRetraction l r hn) q

/-- The section induced by the original outer Levi inclusion. -/
def leviSection : Q ⟶ group l r hn q :=
  pullback.lift (q ≫ l) (𝟙 Q) (by
    rw [Category.assoc, levi_comp_leviRetraction, Category.comp_id, Category.id_comp])

@[simp] theorem section_inclusion :
    leviSection l r hn q ≫ inclusion l r hn q = q ≫ l :=
  pullback.lift_fst _ _ _

@[simp] theorem section_projection :
    leviSection l r hn q ≫ projection l r hn q = 𝟙 Q :=
  pullback.lift_snd _ _ _

/-- The original radical, included into this inverse image. -/
abbrev radicalLift : U ⟶ group l r hn q := leviPreimageRadicalLift l r hn q

@[simp] theorem radicalLift_inclusion :
    radicalLift l r hn q ≫ inclusion l r hn q = r :=
  leviPreimageRadicalLift_comp_inclusion l r hn q

@[simp] theorem radicalLift_projection :
    radicalLift l r hn q ≫ projection l r hn q = 0 :=
  leviPreimageRadicalLift_comp_projection l r hn q

/-- The new projection has exactly the original radical as its all-test kernel. -/
theorem range_kernel_projection :
    SubgroupFunctor.range (kernelι (projection l r hn q)) =
      SubgroupFunctor.range (radicalLift l r hn q) := by
  ext T x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_range]
  constructor
  · intro hx
    have hx' : (x ≫ (inclusion l r hn q).hom.hom) ≫
        (leviRetraction l r hn).hom.hom = 1 := by
      rw [Category.assoc, (SubgroupPreimage.isPullback _ q).w,
        ← Category.assoc, hx, MonObj.one_comp]
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
      ((comp_leviRetraction_eq_one_iff l r hn _).mp hx')
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    apply (SubgroupPreimage.isPullback (leviRetraction l r hn) q).hom_ext
    · rw [Category.assoc, ← Grp.comp_hom_hom, radicalLift_inclusion]
      exact hy
    · rw [Category.assoc, ← Grp.comp_hom_hom, radicalLift_projection, hx]
      simp only [Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]
  · rintro ⟨y, rfl⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, radicalLift_projection]
    simp only [Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]

/-- A monic original radical remains monic in the inverse image. -/
theorem mono_radicalLift [Mono r.hom.hom] :
    Mono (radicalLift l r hn q).hom.hom := by
  constructor
  intro T x y h
  apply (cancel_mono r.hom.hom).mp
  have h' := congrArg (fun z => z ≫ (inclusion l r hn q).hom.hom) h
  simpa only [Category.assoc, ← Grp.comp_hom_hom, radicalLift_inclusion] using h'

/-- The pullback has its canonical inner-group-times-original-radical decomposition. -/
theorem multiplication_isIso [Mono r.hom.hom] :
    IsIso (subgroupMultiplication (leviSection l r hn q) (radicalLift l r hn q)) := by
  have : IsIso (leviSection l r hn q ≫ projection l r hn q) := by
    rw [section_projection]
    infer_instance
  exact isIso_subgroupMultiplication_of_isIso_comp
    (mono_radicalLift l r hn q) (range_kernel_projection l r hn q)

/-- Intersecting the inverse image with the original Levi recovers the original
inner subgroup, on every test scheme. -/
theorem range_section_intersection [Mono l.hom.hom] :
    SubgroupFunctor.range (q ≫ l) =
      SubgroupFunctor.range l ⊓ SubgroupFunctor.range (inclusion l r hn q) := by
  ext T x
  change (∃ y : T ⟶ Q.X, y ≫ (q ≫ l).hom.hom = x) ↔
    (∃ a : T ⟶ M.X, a ≫ l.hom.hom = x) ∧
      ∃ b : T ⟶ (group l r hn q).X, b ≫ (inclusion l r hn q).hom.hom = x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨⟨y ≫ q.hom.hom, rfl⟩, ?_⟩
    exact ⟨y ≫ (leviSection l r hn q).hom.hom,
      by rw [Category.assoc, ← Grp.comp_hom_hom, section_inclusion]⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hx : x ∈ (SubgroupFunctor.range (inclusion l r hn q)).carrier T := ⟨b, hb⟩
    rw [SubgroupPreimage.range_inclusion, SubgroupFunctor.mem_comap] at hx
    obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp hx
    have hla : a = c ≫ q.hom.hom := by
      have he := congrArg (fun z => z ≫ (leviRetraction l r hn).hom.hom) ha
      rw [Category.assoc, ← Grp.comp_hom_hom, levi_comp_leviRetraction,
        Grp.id_hom_hom, Category.comp_id] at he
      exact he.trans hc.symm
    exact ⟨c, by rw [Grp.comp_hom_hom, ← Category.assoc, ← hla, ha]⟩

variable {G : GroupScheme S} (p : P ⟶ G)

/-- The exact extension is contained in the supplied outer subgroup. -/
theorem range_ambient_le :
    SubgroupFunctor.range (inclusion l r hn q ≫ p) ≤ SubgroupFunctor.range p :=
  SubgroupFunctor.range_le_of_factor (inclusion l r hn q) rfl

/-- The intersection identity after the original ambient closed embedding. -/
theorem range_ambient_intersection [Mono p.hom.hom] [Mono l.hom.hom] :
    SubgroupFunctor.range (q ≫ l ≫ p) =
      SubgroupFunctor.range (l ≫ p) ⊓
        SubgroupFunctor.range (inclusion l r hn q ≫ p) := by
  ext T x
  change (∃ y : T ⟶ Q.X, y ≫ (q ≫ l ≫ p).hom.hom = x) ↔
    (∃ a : T ⟶ M.X, a ≫ (l ≫ p).hom.hom = x) ∧
      ∃ b : T ⟶ (group l r hn q).X, b ≫ (inclusion l r hn q ≫ p).hom.hom = x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨⟨y ≫ q.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩, ?_⟩
    refine ⟨y ≫ (leviSection l r hn q).hom.hom, ?_⟩
    have he : leviSection l r hn q ≫ inclusion l r hn q ≫ p = q ≫ l ≫ p := by
      rw [← Category.assoc, section_inclusion, Category.assoc]
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f => y ≫ f.hom.hom) he
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hab : a ≫ l.hom.hom = b ≫ (inclusion l r hn q).hom.hom := by
      apply (cancel_mono p.hom.hom).mp
      simpa only [Grp.comp_hom_hom, Category.assoc] using ha.trans hb.symm
    have hmem : a ≫ l.hom.hom ∈
        (SubgroupFunctor.range l ⊓ SubgroupFunctor.range (inclusion l r hn q)).carrier T :=
      ⟨⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
    rw [← range_section_intersection l r hn q] at hmem
    obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp hmem
    refine ⟨c, ?_⟩
    calc
      c ≫ (q ≫ l ≫ p).hom.hom =
          (a ≫ l.hom.hom) ≫ p.hom.hom := by
        simpa only [Grp.comp_hom_hom, Category.assoc] using
          congrArg (fun z => z ≫ p.hom.hom) hc
      _ = x := by simpa only [Grp.comp_hom_hom, Category.assoc] using ha

end Langlands.GroupScheme.LeviPreimage
