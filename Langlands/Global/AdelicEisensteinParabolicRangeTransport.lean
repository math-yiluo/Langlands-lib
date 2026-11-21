import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.EisensteinConstantTerm.Points

/-! # Transport of the Eisenstein formulas between represented parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G H H' : GroupScheme (Spec (CommRingCat.of F))}

/-- Inclusion of all-test images implies inclusion of the intrinsic principal images. -/
theorem rationalImage_le_of_range_le (j : H ⟶ G) (j' : H' ⟶ G)
    (h : SubgroupFunctor.range j ≤ SubgroupFunctor.range j') :
    rationalImage F j ≤ rationalImage F j' := by
  rintro _ ⟨x, rfl⟩
  have hx := h _ (show H.affinePointsTarget j _ x ∈ (SubgroupFunctor.range j).carrier _ from ⟨x, rfl⟩)
  obtain ⟨y, hy⟩ : ∃ y : RationalGroupPoints F H',
      H'.affinePointsTarget j' _ y = H.affinePointsTarget j _ x := hx
  exact ⟨y, (map_rational j' y).trans ((congrArg (rational F G) hy).trans (map_rational j x).symm)⟩

theorem rationalImage_eq_of_range_eq (j : H ⟶ G) (j' : H' ⟶ G)
    (h : SubgroupFunctor.range j = SubgroupFunctor.range j') :
    rationalImage F j = rationalImage F j' :=
  le_antisymm (rationalImage_le_of_range_le j j' h.le) (rationalImage_le_of_range_le j' j h.ge)

/-- Equal all-test images of parabolics give the same Iwasawa coverage. -/
theorem IsIwasawaCompact.of_range_eq {p : H ⟶ G} {p' : H' ⟶ G}
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (h : SubgroupFunctor.range p = SubgroupFunctor.range p') :
    IsIwasawaCompact p' K := by
  have hRange : Set.range (map F H G p) = Set.range (map F H' G p') := by
    change (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range p) :
      Set (AdelicGroupPoints F G)) =
      (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range p') : Set (AdelicGroupPoints F G))
    rw [h]
  exact ⟨hK.isCompact, hRange ▸ hK.range_mul⟩

/-- The left invariance subgroup of an inducing space depends only on
the represented radical and Levi images. -/
theorem parabolicQuotientSubgroup_eq_of_range_eq
    {P P' U U' M M' : GroupScheme (Spec (CommRingCat.of F))}
    {p : P ⟶ G} {p' : P' ⟶ G} {iU : U ⟶ P} {iU' : U' ⟶ P'}
    {l : M ⟶ P} {l' : M' ⟶ P'}
    (hU : SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (iU' ≫ p'))
    (hM : SubgroupFunctor.range (l ≫ p) = SubgroupFunctor.range (l' ≫ p')) :
    parabolicQuotientSubgroup F p iU l = parabolicQuotientSubgroup F p' iU' l' := by
  change AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)) ⊔
      rationalImage F (l ≫ p) =
    AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ p')) ⊔
      rationalImage F (l' ≫ p')
  rw [hU, rationalImage_eq_of_range_eq _ _ hM]

section Series

variable {P P' : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G} {p' : P' ⟶ G}
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact p' K)

/-- Equal represented parabolics have the same rational coset space.
Equal twists therefore give equal Eisenstein sums, including their
unconditional-sum values. -/
theorem IsIwasawaCompact.eisensteinSeries_eq_of_range_eq_of_twist
    (h : SubgroupFunctor.range p = SubgroupFunctor.range p')
    (phi : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) (lam' : ComplexCharacterParameter F P')
    (hTwist : hK.parameterTwist phi lam = hK'.parameterTwist phi lam')
    (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries phi lam g = hK'.eisensteinSeries phi lam' g := by
  have hRat : parabolicRationalSubgroup F p = parabolicRationalSubgroup F p' := by
    unfold parabolicRationalSubgroup
    rw [← rationalImage_eq_map, ← rationalImage_eq_map, rationalImage_eq_of_range_eq _ _ h]
  let series (A : Subgroup (rationalSubgroup F G)) (f : AdelicGroupPoints F G → ℂ) :=
    ∑' x : LeftCosetSpace A, f ((Quotient.out x : rationalSubgroup F G).val * g)
  change series (parabolicRationalSubgroup F p) (hK.parameterTwist phi lam) =
    series (parabolicRationalSubgroup F p') (hK'.parameterTwist phi lam')
  rw [hRat, hTwist]

variable [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine P'.X.left]
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion p'.hom.hom.left]

/-- Restricting the parameter along a comparison over the inclusions gives
pointwise equality of the two Iwasawa twists. -/
theorem IsIwasawaCompact.parameterTwist_restrict_of_comp_eq
    (f : P' ⟶ P) (hf : f ≫ p = p') (phi : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) :
    hK.parameterTwist phi lam = hK'.parameterTwist phi (parameterRestrict f lam) := by
  funext y
  unfold parameterTwist
  subst p'
  rw [hK.heightPower_restrict f hK']

/-- The same Eisenstein sum in two presentations of one parabolic,
with parameters related by restriction. -/
theorem IsIwasawaCompact.eisensteinSeries_eq_of_range_eq
    (f : P' ⟶ P) (hf : f ≫ p = p') (h : SubgroupFunctor.range p = SubgroupFunctor.range p')
    (phi : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries phi lam g = hK'.eisensteinSeries phi (parameterRestrict f lam) g :=
  hK.eisensteinSeries_eq_of_range_eq_of_twist hK' h phi lam (parameterRestrict f lam)
    (hK.parameterTwist_restrict_of_comp_eq hK' f hf phi lam) g

end Series

section Integral

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The normalized subgroup constant term depends on the represented
all-test radical image. -/
theorem subgroupConstantTerm_eq_of_range_eq
    (j : H ⟶ G) (j' : H' ⟶ G) [IsAffine H.X.left] [IsAffine H'.X.left]
    [IsClosedImmersion j.hom.hom.left] [IsClosedImmersion j'.hom.hom.left]
    (h : SubgroupFunctor.range j = SubgroupFunctor.range j')
    (f : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    subgroupConstantTerm F j f g = subgroupConstantTerm F j' f g := by
  let average (A : G.SubgroupFunctor)
      (hA : IsClosed (AdelicSubgroupPoints.adelicPoints F G A : Set (AdelicGroupPoints F G))) : ℂ :=
    let : IsClosed (AdelicSubgroupPoints.adelicPoints F G A : Set (AdelicGroupPoints F G)) := hA
    ∫ x, f ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G A).val * g)
      ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G A
  have hAvg {A B : G.SubgroupFunctor} (hAB : A = B)
      (hA : IsClosed (AdelicSubgroupPoints.adelicPoints F G A : Set (AdelicGroupPoints F G)))
      (hB : IsClosed (AdelicSubgroupPoints.adelicPoints F G B : Set (AdelicGroupPoints F G))) :
      average A hA = average B hB := by
    subst B
    rfl
  exact hAvg h (AdelicSubgroupPoints.isClosed_adelicPoints_range F G j)
    (AdelicSubgroupPoints.isClosed_adelicPoints_range F G j')

variable {P P' U U' V V' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine V.X.left] [IsAffine V'.X.left] {p : P ⟶ G} {p' : P' ⟶ G}
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact p' K)

/-- Equal represented radical images identify both the stabilizer and
measure of the actual intertwining integral. The twists are then integrated
on the same quotient with the same representatives. -/
theorem IsIwasawaCompact.intertwiningIntegral_eq_of_range_eq_of_twist
    (iU : U ⟶ P) (iU' : U' ⟶ P') (j : V ⟶ G) (j' : V' ⟶ G)
    [IsClosedImmersion j.hom.hom.left] [IsClosedImmersion j'.hom.hom.left]
    (hU : SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (iU' ≫ p'))
    (hV : SubgroupFunctor.range j = SubgroupFunctor.range j')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (phi : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) (lam' : ComplexCharacterParameter F P')
    (hTwist : hK.parameterTwist phi lam = hK'.parameterTwist phi lam')
    (g : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU j w phi lam g = hK'.intertwiningIntegral iU' j' w phi lam' g := by
  let wA := innerAdelicPoint F G w
  let integrate (A B : G.SubgroupFunctor)
      (hB : IsClosed (AdelicSubgroupPoints.adelicPoints F G B : Set (AdelicGroupPoints F G)))
      (f : AdelicGroupPoints F G → ℂ) : ℂ :=
    let : IsClosed (AdelicSubgroupPoints.adelicPoints F G B : Set (AdelicGroupPoints F G)) := hB
    let S := AdelicSubgroupPoints.rationalSubgroup F G B ⊓
      (AdelicSubgroupPoints.adelicPoints F G A).comap
        ((MulAut.conj wA⁻¹).toMonoidHom.comp (AdelicSubgroupPoints.adelicPoints F G B).subtype)
    let hS : _root_.IsDiscrete (S : Set (AdelicSubgroupPoints.adelicPoints F G B)) :=
      (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G B).mono inf_le_left
    ∫ x : LeftCosetSpace S, f (wA⁻¹ * (Quotient.out x :
      AdelicSubgroupPoints.adelicPoints F G B).val * g)
      ∂LeftCosetSpace.discreteQuotientMeasure S hS (AdelicSubgroupPoints.normalizedHaarMeasure F G B)
  have hEq {A A' B B' : G.SubgroupFunctor} (hA : A = A') (hB : B = B')
      (hClosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G B : Set (AdelicGroupPoints F G)))
      (hClosed' : IsClosed (AdelicSubgroupPoints.adelicPoints F G B' : Set (AdelicGroupPoints F G)))
      {f f' : AdelicGroupPoints F G → ℂ} (hf : f = f') :
      integrate A B hClosed f = integrate A' B' hClosed' f' := by
    subst A' B' f'
    rfl
  exact hEq hU hV (AdelicSubgroupPoints.isClosed_adelicPoints_range F G j)
    (AdelicSubgroupPoints.isClosed_adelicPoints_range F G j') hTwist

end Integral

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- Equal represented parabolic inclusions give the same Eisenstein series
at the parameters identified by the inclusion-compatible comparison. -/
def EisensteinParabolicRangeTransportStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F]
    {G P P' : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine P'.X.left]
    {p : P ⟶ G} {p' : P' ⟶ G} [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion p'.hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact p' K) (f : P' ⟶ P),
    f ≫ p = p' → SubgroupFunctor.range p = SubgroupFunctor.range p' →
    ∀ (phi : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
      (g : AdelicGroupPoints F G),
      hK.eisensteinSeries phi lam g = hK'.eisensteinSeries phi (parameterRestrict f lam) g

theorem eisensteinParabolicRangeTransport : EisensteinParabolicRangeTransportStatement.{u} := by
  intro F _ _ G P P' _ _ _ p p' _ _ K hK hK' f hf h phi lam g
  exact hK.eisensteinSeries_eq_of_range_eq hK' f hf h phi lam g

end Langlands.Global
