import Langlands.GroupScheme.Rational.AffineCommutatorImageStability
import Langlands.GroupScheme.Rational.SplitTorusImageDominant
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Closed containment and centralizers of a dominant torus image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- A schematically dominant factor does not change containment in a closed subgroup. -/
theorem SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
    {D E G B : GroupScheme S} (p : D ⟶ E) (i : E ⟶ G) (b : B ⟶ G)
    [IsSchemeTheoreticallyDominant p.hom.hom.left] (hb : IsClosedSubgroup b) :
    range (p ≫ i) ≤ range b ↔ range i ≤ range b := by
  constructor
  · intro h
    have : IsClosedImmersion b.hom.hom.left := hb
    obtain ⟨a, ha⟩ := mem_range.mp
      (h D.X (show (p ≫ i).hom.hom ∈ (range (p ≫ i)).carrier D.X from
        mem_range.mpr ⟨𝟙 D.X, Category.id_comp _⟩))
    obtain ⟨f, hf⟩ := exists_lift_of_isSchemeTheoreticallyDominant
      b.hom.hom.left i.hom.hom.left p.hom.hom.left a.left
      (congrArg Over.Hom.left ha)
    let fOver : E.X ⟶ B.X := Over.homMk f (by
      rw [← Over.w b.hom.hom, ← Category.assoc, hf, Over.w i.hom.hom])
    have hfOver : fOver ≫ b.hom.hom = i.hom.hom := Over.OverMorphism.ext hf
    intro U g hg
    obtain ⟨x, rfl⟩ := mem_range.mp hg
    exact mem_range.mpr ⟨x ≫ fOver, by rw [Category.assoc, hfOver]⟩
  · intro h U g hg
    obtain ⟨x, rfl⟩ := mem_range.mp hg
    apply h U
    exact mem_range.mpr ⟨x ≫ p.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩

section Field

variable {k : Type u} [Field k]
    {D E : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A dominant quasi-compact parametrization has the same centralizer on every test scheme. -/
theorem torusCentralizer_comp_eq_of_isSchemeTheoreticallyDominant
    [IsSeparated G.X.hom] (p : D.toGrp ⟶ E.toGrp) (i : E.toGrp ⟶ G)
    [QuasiCompact p.hom.hom.left] [IsSchemeTheoreticallyDominant p.hom.hom.left] :
    torusCentralizer (p ≫ i) = torusCentralizer i := by
  apply SubgroupFunctor.ext
  intro U
  ext g
  rw [mem_torusCentralizer_iff_universal, mem_torusCentralizer_iff_universal]
  constructor
  · intro h
    change (fst U E.X ≫ g) * (snd U E.X ≫ i.hom.hom) =
      (snd U E.X ≫ i.hom.hom) * (fst U E.X ≫ g)
    apply Over.OverMorphism.ext
    have : IsSchemeTheoreticallyDominant (U ◁ p.hom.hom).left :=
      RelativeRoot.CommutatorCoordinates.whiskerLeft_schematic U p.hom.hom
    apply ext_of_isSchemeTheoreticallyDominant G.X.hom
      (by rw [Over.w, Over.w]) (U ◁ p.hom.hom).left
    have hh := h.eq
    simpa only [← Over.comp_left, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, Grp.comp_hom_hom, Category.assoc] using
      congrArg Over.Hom.left hh
  · intro h
    have hh := congrArg (fun f => (U ◁ p.hom.hom) ≫ f) h.eq
    exact (commute_iff_eq _ _).mpr (by
      simpa only [MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
        Grp.comp_hom_hom, Category.assoc] using hh)

namespace SplitTorusImage.DominantFactorization

variable {φ : D.toGrp ⟶ G} (d : DominantFactorization φ)

/-- The torus image lies in exactly the closed subgroups that contain the original map. -/
theorem range_le_iff {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsClosedSubgroup b) :
    SubgroupFunctor.range φ ≤ SubgroupFunctor.range b ↔
      SubgroupFunctor.range d.inclusion ≤ SubgroupFunctor.range b := by
  have : IsSchemeTheoreticallyDominant d.factor.hom.hom.left := d.dominant
  simpa only [d.factor_comp] using
    (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant d.factor d.inclusion b hb)

/-- Factor the torus image through any closed subgroup containing the original map. -/
def closedFactor {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hφ : SubgroupFunctor.range φ ≤ SubgroupFunctor.range b) :
    d.image.toGrp ⟶ B := by
  have : IsClosedImmersion b.hom.hom.left := hb
  have hr : (SubgroupFunctor.range b).IsRepresentedBy b :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact hr.factorHom d.inclusion ((d.range_le_iff b hb).mp hφ)

theorem closedFactor_comp {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hφ : SubgroupFunctor.range φ ≤ SubgroupFunctor.range b) :
    d.closedFactor b hb hφ ≫ b = d.inclusion := by
  unfold closedFactor
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The factor remains a closed split subtorus of the containing subgroup. -/
theorem isSplitSubtorus_closedFactor {B : GroupScheme (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hφ : SubgroupFunctor.range φ ≤ SubgroupFunctor.range b) :
    IsSplitSubtorus (d.closedFactor b hb hφ) := by
  refine ⟨d.isSplitSubtorus.1, IsClosedSubgroup.of_comp hb ?_⟩
  rw [d.closedFactor_comp]
  exact d.isSplitSubtorus.2

/-- A split source and its dominant torus image have the same all-test centralizer. -/
theorem torusCentralizer_eq (hD : IsSplitTorus D.toGrp) [IsSeparated G.X.hom] :
    torusCentralizer d.inclusion = torusCentralizer φ := by
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : IsAffineHom d.image.X.hom := d.isSplitSubtorus.1.isAffineHom
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  have : IsAffine d.image.X.left := isAffine_of_isAffineHom d.image.X.hom
  have : IsSchemeTheoreticallyDominant d.factor.hom.hom.left := d.dominant
  simpa only [d.factor_comp] using
    (torusCentralizer_comp_eq_of_isSchemeTheoreticallyDominant d.factor d.inclusion).symm

end SplitTorusImage.DominantFactorization

/-- The centralizer of any cocharacter equals that of its dominant closed torus image. -/
theorem dynamicCentralizer_eq_torusCentralizer_image
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (d : SplitTorusImage.DominantFactorization χ) [IsSeparated G.X.hom] :
    Dynamic.centralizer χ = torusCentralizer d.inclusion := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer, ← d.torusCentralizer_eq isSplitTorus_gm]

end Field

end Langlands.GroupScheme
