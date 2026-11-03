import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Rational.MinimalParabolicContainment
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.BruhatCoveringReduction
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Borel subgroups through a maximal torus over an algebraically closed field

Over an algebraically closed field, if one Borel subgroup through a maximal torus `j : T ⟶ G`
represents `P(ν₀ ≫ j)`, then every Borel subgroup through `j` represents `P((ν₀ ≫ σ) ≫ j)` for
an automorphism `σ` of `T` (conditional on the conjugacy theorems). The predicate
`IsTorusDynamicParabolic j i` records that `i` represents `P(ν ≫ j)` for some cocharacter `ν`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Transport

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- If `i : H ⟶ G` is a monomorphism with points `P(χ)`, then `i ≫ e` has points `P(χ ≫ e)` for
every automorphism `e` of `G`. -/
theorem range_comp_iso_eq_parabolic {i : H ⟶ G} [Mono i.hom.hom]
    {χ : (Gm S).toGrp ⟶ G} (h : SubgroupFunctor.range i = Dynamic.parabolic χ) (e : G ≅ G) :
    SubgroupFunctor.range (i ≫ e.hom) = Dynamic.parabolic (χ ≫ e.hom) := by
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy i := ⟨inferInstance, h⟩
  rw [(hrep.comp_iso e).2, Dynamic.parabolic_eq_comap_of_iso (χ ≫ e.hom) e.symm, Iso.symm_hom,
    Dynamic.comp_hom_comp_inv]

end Transport

/-! ### Dynamic parabolics of a torus -/

section TorusParabolic

variable {S : Scheme.{u}} {G B : GroupScheme S} {T : CommGroupScheme S}

/-- A subgroup `i : B ⟶ G` is a *dynamic parabolic of the torus* `j : T ⟶ G` if it represents
the dynamic parabolic subgroup functor `P_G(ν ≫ j)` of some cocharacter `ν` of `T`. -/
def IsTorusDynamicParabolic (j : T.toGrp ⟶ G) (i : B ⟶ G) : Prop :=
  ∃ ν : cocharacterLattice T,
    (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i

/-- The torus `j` factors through every dynamic parabolic of `j`. -/
theorem IsTorusDynamicParabolic.exists_comp_eq {j : T.toGrp ⟶ G} {i : B ⟶ G}
    (h : IsTorusDynamicParabolic j i) : ∃ f : T.toGrp ⟶ B, f ≫ i = j := by
  obtain ⟨ν, hrep⟩ := h
  exact ⟨_, hrep.factorHom_comp j (range_le_dynamicParabolic j (CommGroupScheme.groupHom ν))⟩

end TorusParabolic

/-! ### Borel subgroups through a maximal torus -/

section Conjugacy

variable {K : Type u} [Field K] [IsAlgClosed K] {G : GroupScheme (Spec (CommRingCat.of K))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- **Borel subgroups through a maximal torus are dynamic parabolics (conditional on the
conjugacy theorems).** Let `G` be a smooth affine connected group over an algebraically closed
field, `j : T ⟶ G` a maximal torus, and `ν₀` a cocharacter of `T` such that a Borel subgroup
`i₀` represents `P(ν₀ ≫ j)`. Assume `BorelConjugacyStatement` and
`MaximalTorusConjugacyStatement`. Then for every Borel subgroup `i : B ⟶ G` through which `j`
factors there is an automorphism `σ` of `T` such that `i` represents `P((ν₀ ≫ σ) ≫ j)`. -/
theorem exists_isRepresentedBy_parabolic_of_isBorelSubgroup
    (hBC : BorelConjugacyStatement.{u}) (hTC : MaximalTorusConjugacyStatement.{u})
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j) (ν₀ : cocharacterLattice T)
    {P₀ : GroupScheme (Spec (CommRingCat.of K))} (i₀ : P₀ ⟶ G) (hP₀ : IsBorelSubgroup i₀)
    (hrep₀ : (Dynamic.parabolic (CommGroupScheme.groupHom ν₀ ≫ j)).IsRepresentedBy i₀)
    {B : GroupScheme (Spec (CommRingCat.of K))} (i : B ⟶ G) (f : T.toGrp ⟶ B)
    (hB : IsBorelSubgroup i) (hf : f ≫ i = j) :
    ∃ σ : T ≅ T,
      (Dynamic.parabolic (CommGroupScheme.groupHom (ν₀ ≫ σ.hom) ≫ j)).IsRepresentedBy i := by
  have : IsClosedImmersion i.hom.hom.left := hB.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i₀.hom.hom := hrep₀.1
  have : Smooth B.X.hom := hB.smooth
  have : ConnectedSpace B.X.left := hB.connectedSpace
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  -- Conjugate `P₀` onto `B`.
  obtain ⟨g, φ, hg⟩ := (hBC K G).2 P₀ B i₀ i hP₀ hB
  have hrange₁ : SubgroupFunctor.range i =
      Dynamic.parabolic ((CommGroupScheme.groupHom ν₀ ≫ j) ≫ (G.innerIso g).hom) := by
    rw [← SubgroupFunctor.range_iso_comp φ i, ← hg]
    exact range_comp_iso_eq_parabolic hrep₀.2 _
  -- The torus `j` factors through `P₀`, hence `j ≫ int(g)` factors through `B`.
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : T.toGrp ⟶ P₀, f₀ ≫ i₀ = j :=
    ⟨_, hrep₀.factorHom_comp j (range_le_dynamicParabolic j (CommGroupScheme.groupHom ν₀))⟩
  have hf' : (f₀ ≫ φ.hom) ≫ i = j ≫ (G.innerIso g).hom := by
    rw [Category.assoc, ← hg, ← Category.assoc, hf₀]
  -- Conjugate the two maximal tori of `B`.
  have hfmax : IsMaximalTorus f := IsMaximalTorus.of_comp hB.isClosedSubgroup (by rwa [hf])
  have hf'max : IsMaximalTorus (f₀ ≫ φ.hom) :=
    IsMaximalTorus.of_comp hB.isClosedSubgroup (by rw [hf']; exact hj.comp_iso _)
  obtain ⟨b, σ, hb⟩ := hTC K B T T (f₀ ≫ φ.hom) f hf'max hfmax
  have hnorm : (j ≫ (G.innerIso g).hom) ≫ (G.innerIso (b ≫ i.hom.hom)).hom =
      CommGroupScheme.groupHom σ.hom ≫ j := by
    rw [← hf', Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hb, Category.assoc, hf]
  -- Conjugation by `b ∈ B` preserves `B`.
  have hrange₂ : SubgroupFunctor.range i =
      SubgroupFunctor.range (i ≫ (G.innerIso (b ≫ i.hom.hom)).hom) := by
    rw [← innerIso_hom_comp, SubgroupFunctor.range_iso_comp]
  refine ⟨σ, inferInstance, ?_⟩
  rw [hrange₂, range_comp_iso_eq_parabolic hrange₁, Category.assoc, Category.assoc,
    ← Category.assoc j, hnorm, ← Category.assoc]
  rfl

/-- **If one Borel subgroup through a maximal torus is a dynamic parabolic of the torus, all are
(conditional on the conjugacy theorems).** Let `G` be a smooth affine connected group over an
algebraically closed field and `j : T ⟶ G` a maximal torus. Assume `BorelConjugacyStatement` and
`MaximalTorusConjugacyStatement`. If some Borel subgroup `i₀` is a dynamic parabolic of `j`, then
so is every Borel subgroup `i` through which `j` factors. -/
theorem IsTorusDynamicParabolic.of_isBorelSubgroup
    (hBC : BorelConjugacyStatement.{u}) (hTC : MaximalTorusConjugacyStatement.{u})
    {j : T.toGrp ⟶ G} (hj : IsMaximalTorus j)
    {P₀ : GroupScheme (Spec (CommRingCat.of K))} {i₀ : P₀ ⟶ G} (hP₀ : IsBorelSubgroup i₀)
    (h₀ : IsTorusDynamicParabolic j i₀)
    {B : GroupScheme (Spec (CommRingCat.of K))} {i : B ⟶ G} (hB : IsBorelSubgroup i)
    {f : T.toGrp ⟶ B} (hf : f ≫ i = j) : IsTorusDynamicParabolic j i := by
  obtain ⟨ν₀, hrep₀⟩ := h₀
  obtain ⟨σ, hσ⟩ :=
    exists_isRepresentedBy_parabolic_of_isBorelSubgroup hBC hTC j hj ν₀ i₀ hP₀ hrep₀ i f hB hf
  exact ⟨ν₀ ≫ σ.hom, hσ⟩

end Conjugacy

end Langlands.GroupScheme
