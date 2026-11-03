import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Limits in a closed normalized subgroup -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A subgroup contains every limit of each of its points under the given
cocharacter, on every test scheme. -/
def IsLimitStable (F : SubgroupFunctor G) (χ : (Gm S).toGrp ⟶ G) : Prop :=
  ∀ (T : Over S) (g l : T ⟶ G.X),
    g ∈ F.carrier T → Dynamic.HasLimit χ g l → l ∈ F.carrier T

/-- The orbit of a point of a normalized subgroup remains in that subgroup. -/
theorem orbit_mem_of_isNormalizedBy_range (F : SubgroupFunctor G)
    (χ : (Gm S).toGrp ⟶ G) (hn : F.IsNormalizedBy (range χ))
    {T : Over S} {g : T ⟶ G.X} (hg : g ∈ F.carrier T) :
    Dynamic.orbit χ g ∈ F.carrier (T ⊗ (Gm S).X) :=
  hn _ _ _ (mem_range.mpr ⟨snd T (Gm S).X, rfl⟩)
    (F.comp_mem (fst T (Gm S).X) hg)

/-- Every orbit extension of a point of a closed normalized subgroup factors
through that subgroup. -/
theorem IsRepresentedBy.exists_lift_of_isOrbitExtension
    {F : SubgroupFunctor G} {f : H ⟶ G} (hf : F.IsRepresentedBy f)
    (hc : IsClosedSubgroup f) (χ : (Gm S).toGrp ⟶ G)
    (hn : F.IsNormalizedBy (range χ)) {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ F.carrier T) {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : Dynamic.IsOrbitExtension χ g e) :
    ∃ e' : T ⊗ AffineLine.scheme S ⟶ H.X, e' ≫ f.hom.hom = e := by
  have : IsClosedImmersion f.hom.hom.left := hc
  have horbit : Dynamic.orbit χ g ∈ (range f).carrier (T ⊗ (Gm S).X) := by
    rw [hf.2]
    exact orbit_mem_of_isNormalizedBy_range F χ hn hg
  obtain ⟨a, ha⟩ := mem_range.mp horbit
  exact AffineLine.exists_lift_of_unitInclusion f.hom.hom e a (ha.trans he.symm)

/-- A closed subgroup normalized by a cocharacter contains all limits under
that cocharacter. The cocharacter need not factor through the subgroup. -/
theorem IsRepresentedBy.isLimitStable_of_isClosedSubgroup
    {F : SubgroupFunctor G} {f : H ⟶ G} (hf : F.IsRepresentedBy f)
    (hc : IsClosedSubgroup f) (χ : (Gm S).toGrp ⟶ G)
    (hn : F.IsNormalizedBy (range χ)) : F.IsLimitStable χ := by
  rintro T g l hg ⟨e, he, rfl⟩
  obtain ⟨e', he'⟩ := hf.exists_lift_of_isOrbitExtension hc χ hn hg he
  rw [← hf.2]
  refine mem_range.mpr ⟨Dynamic.evalZero e', ?_⟩
  rw [← Dynamic.evalZero_comp, he']

end SubgroupFunctor

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The image of a cocharacter lies in its dynamic centralizer on every test. -/
theorem range_le_centralizer (χ : (Gm S).toGrp ⟶ G) :
    SubgroupFunctor.range χ ≤ centralizer χ := by
  intro T g hg
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have h := (Commute.all (snd T (Gm S).X) (fst T (Gm S).X ≫ t)).map
    (((yonedaGrp.map χ).app (op (T ⊗ (Gm S).X))).hom)
  change Commute (snd T (Gm S).X ≫ χ.hom.hom)
    ((fst T (Gm S).X ≫ t) ≫ χ.hom.hom) at h
  rw [mem_centralizer, orbit, ← Category.assoc, h.eq, mul_inv_cancel_right]

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ ψ : (Gm (Spec R)).toGrp ⟶ G)

/-- In an affine group, every normalized dynamic unipotent subgroup contains
all limits under the normalizing cocharacter. -/
theorem unipotent_isLimitStable_of_isNormalizedBy
    (hn : (unipotent χ).IsNormalizedBy (SubgroupFunctor.range ψ)) :
    (unipotent χ).IsLimitStable ψ :=
  (Affine.isRepresentedBy_unipotentHom χ).isLimitStable_of_isClosedSubgroup
    (Affine.isClosedSubgroup_unipotentHom χ) ψ hn

/-- Commuting cocharacters preserve each other's unipotent subgroups under
limits, in the all-test range-centralizer formulation. -/
theorem unipotent_isLimitStable_of_range_le_centralizer
    (hcomm : SubgroupFunctor.range ψ ≤ centralizer χ) :
    (unipotent χ).IsLimitStable ψ := by
  apply unipotent_isLimitStable_of_isNormalizedBy χ ψ
  intro T a b ha hb
  exact conj_mem_unipotent χ (centralizer_le_parabolic χ T (hcomm T ha)) hb

/-- Centralizer containment ensures that a point contracting under `χ` and
having a `ψ`-limit also contracts under `ψ`. -/
theorem mem_unipotent_of_mem_unipotent_of_mem_parabolic
    (hZ : centralizer ψ ≤ centralizer χ) {T : Over (Spec R)} {g : T ⟶ G.X}
    (hg : g ∈ (unipotent χ).carrier T) (hp : g ∈ (parabolic ψ).carrier T) :
    g ∈ (unipotent ψ).carrier T := by
  obtain ⟨l, hl⟩ := exists_hasLimit ψ hp
  have hlU : l ∈ (unipotent χ).carrier T :=
    unipotent_isLimitStable_of_range_le_centralizer χ ψ
      ((range_le_centralizer ψ).trans hZ) T g l hg hl
  have hlone : l = 1 :=
    eq_one_of_mem_centralizer_of_mem_unipotent χ
      (fun _ _ _ _ ha hb => ha.unique χ hb) (hZ T (hl.mem_centralizer ψ)) hlU
  rwa [hlone] at hl

/-- With nested centralizers, the intersection of one unipotent subgroup with
the other's parabolic is already an intersection of unipotent subgroups. -/
theorem unipotent_inf_parabolic_eq_unipotent_inf_unipotent
    (hZ : centralizer ψ ≤ centralizer χ) :
    unipotent χ ⊓ parabolic ψ = unipotent χ ⊓ unipotent ψ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  exact ⟨fun ⟨hg, hp⟩ =>
    ⟨hg, mem_unipotent_of_mem_unipotent_of_mem_parabolic χ ψ hZ hg hp⟩,
    fun ⟨hg, hu⟩ => ⟨hg, unipotent_le_parabolic ψ T hu⟩⟩

end Dynamic

end Langlands.GroupScheme
