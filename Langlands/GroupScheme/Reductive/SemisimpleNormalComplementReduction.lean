import Langlands.GroupScheme.Reductive.AlmostSimpleGenerationStatement
import Langlands.GroupScheme.Reductive.SemisimpleNormalComplementStatement
import Langlands.GroupScheme.DominantHomFaithfullyFlat

/-! # Reduction of normal complements to almost-simple generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Actual data for a commuting closed normal complement whose multiplication
is flat and surjective. No smoothness of the complement is part of the data. -/
structure CommutingNormalComplement {S : Scheme.{u}} {G H : GroupScheme S}
    (j : H ⟶ G) where
  group : GroupScheme S
  inclusion : group ⟶ G
  closed : IsClosedSubgroup inclusion
  normal : (SubgroupFunctor.range inclusion).IsNormal
  commutes : ∀ (T : Over S) (x : T ⟶ H.X) (y : T ⟶ group.X),
    Commute (x ≫ j.hom.hom) (y ≫ inclusion.hom.hom)
  flat : Flat (subgroupMultiplication j inclusion).left
  surjective : Surjective (subgroupMultiplication j inclusion).left

/-- Forget the chosen data to the corresponding existence assertion. -/
theorem CommutingNormalComplement.exists {S : Scheme.{u}} {G H : GroupScheme S}
    {j : H ⟶ G} (C : CommutingNormalComplement j) :
    ∃ (K : GroupScheme S) (i : K ⟶ G),
      IsClosedSubgroup i ∧ (SubgroupFunctor.range i).IsNormal ∧
      (∀ (T : Over S) (x : T ⟶ H.X) (y : T ⟶ K.X),
        Commute (x ≫ j.hom.hom) (y ≫ i.hom.hom)) ∧
      Flat (subgroupMultiplication j i).left ∧
      Surjective (subgroupMultiplication j i).left :=
  ⟨C.group, C.inclusion, C.closed, C.normal, C.commutes, C.flat, C.surjective⟩

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- If the image of a finite type affine homomorphism contains every normal
almost-simple factor of a semisimple target, generation makes it faithfully
flat. The hypothesis here is the independent generation statement. -/
theorem flat_surjective_of_contains_almostSimple_factors
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u})
    (hG : IsSemisimple G)
    [IsAffineHom P.X.hom] [LocallyOfFiniteType P.X.hom]
    (f : P ⟶ G)
    (hf : ∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
      IsAlmostSimple A → IsClosedSubgroup a →
      (SubgroupFunctor.range a).IsNormal →
      SubgroupFunctor.range a ≤ SubgroupFunctor.range f) :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : Mono (AffineHomImage.inclusion f).hom.hom := Over.mono_of_mono_left _
  have hfull : SubgroupFunctor.range (AffineHomImage.inclusion f) = ⊤ := by
    apply hgen k G hG (AffineHomImage.image f) (AffineHomImage.inclusion f)
      (show IsClosedImmersion (AffineHomImage.inclusion f).hom.hom.left from inferInstance)
    intro A a hA ha han T x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hf A a hA ha han T hx)
    refine SubgroupFunctor.mem_range.mpr
      ⟨y ≫ (AffineHomImage.projection f).hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, AffineHomImage.projection_inclusion]
    exact hy
  have hmem : 𝟙 G.X ∈
      (SubgroupFunctor.range (AffineHomImage.inclusion f)).carrier G.X := by
    rw [hfull]
    exact Subgroup.mem_top _
  obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp hmem
  let : IsSplitEpi (AffineHomImage.inclusion f).hom.hom := ⟨⟨s, hs⟩⟩
  have : IsIso (AffineHomImage.inclusion f).hom.hom :=
    isIso_of_mono_of_isSplitEpi _
  have : IsIso (AffineHomImage.inclusion f).hom.hom.left :=
    (Over.forget _).map_isIso (AffineHomImage.inclusion f).hom.hom
  have : IsSchemeTheoreticallyDominant f.hom.hom.left := by
    rw [← AffineHomImage.projection_inclusion f, Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  exact DominantHom.flat_surjective f

end Langlands.GroupScheme
