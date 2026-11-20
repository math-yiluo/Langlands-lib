import Langlands.Global.AdelicEisensteinConstantTermStatement

/-! # The integration identity of the geometric lemma (statement)

Bernstein–Lapid, proof of Lemma 6.10 (6.17), pp. 208–209: for parabolics `P = MU`, `Q = M_Q V`,
a rational point `w` and the groups `P_w = (P ∩ w⁻¹Qw)U`, `Q_w = (Q ∩ wPw⁻¹)V` with unipotent
radicals `U_w`, `V_w`, and a function `h` on `G(𝔸)` left invariant under `U(𝔸)` and `P(F)`,
`∫_{(V ∩ wPw⁻¹)(F) \ V(𝔸)} h(w⁻¹ v y) dv = ∫_{(V_w(F) ∩ wU_w(𝔸)w⁻¹) \ V_w(𝔸)} (C_{U_w} h)(w⁻¹ v y) dv`,
both Haar measures normalized by `vol(V(F) \ V(𝔸)) = vol(V_w(F) \ V_w(𝔸)) = 1`. These rational
quotients of the unipotent groups `V` and `V_w` are compact, so the Library's mass normalization
(Haar measure divided by the total mass of the rational quotient) gives mass one there. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F]
variable {G P V : GroupScheme (Spec (CommRingCat.of F))}

/-- The discrete subgroup `V(F) ∩ w P(F) w⁻¹` of `V(𝔸)`, for `p : P → G`, a subgroup
`j : V → G` and an adelic point `w`. -/
def stabilizerRationalSubgroup (p : P ⟶ G) (j : V ⟶ G) (w : AdelicGroupPoints F G) :
    Subgroup (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
  AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j) ⊓
    (rationalImage F p).comap
      ((MulAut.conj w⁻¹).toMonoidHom.comp
        (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)).subtype)

theorem mem_stabilizerRationalSubgroup_iff (p : P ⟶ G) (j : V ⟶ G) (w : AdelicGroupPoints F G)
    (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
    v ∈ stabilizerRationalSubgroup F p j w ↔
      v ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j) ∧
        w⁻¹ * (v : AdelicGroupPoints F G) * w ∈ rationalImage F p := by
  simp [stabilizerRationalSubgroup]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

theorem isDiscrete_stabilizerRationalSubgroup (p : P ⟶ G) (j : V ⟶ G)
    (w : AdelicGroupPoints F G) :
    IsDiscrete (stabilizerRationalSubgroup F p j w :
      Set (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))) :=
  (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range j)).mono
    inf_le_left

variable [IsAffine V.X.left] in
/-- The measure on `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)`, for a closed immersion `j : V → G`: the discrete
quotient measure induced by the Library's `normalizedHaarMeasure` of `V(𝔸)`, which is Haar measure
multiplied by the reciprocal of the total mass of the unrestricted rational quotient
`V(F) \ V(𝔸)`. When that mass is finite (it is always nonzero), the normalized Haar measure gives
`V(F) \ V(𝔸)` mass one; when it is infinite, the factor is `0` and so is this measure. In
`GeometricLemmaUnfoldingStatement`, `V` is a unipotent radical, whose rational quotient is
compact, so there the normalization is `vol(V(F) \ V(𝔸)) = 1`. -/
def stabilizerMeasure (p : P ⟶ G) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (w : AdelicGroupPoints F G) :
    Measure (LeftCosetSpace (stabilizerRationalSubgroup F p j w)) :=
  haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  LeftCosetSpace.discreteQuotientMeasure (stabilizerRationalSubgroup F p j w)
    (isDiscrete_stabilizerRationalSubgroup F p j w)
    (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j))

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- **The integration identity of the geometric lemma** (Bernstein–Lapid, proof of (6.17)).
Let `G` be connected reductive over a number field, `p : P → G` and `q : Q → G` parabolics with
geometric unipotent radicals `iU : U → P` and `iV : V → Q`, `w` a rational point, and
`f : P' → P`, `g' : Q' → Q` parabolics with geometric unipotent radicals `iU'`, `iV'` such that
`P'(F) = (P(F) ∩ w⁻¹Q(F)w) U(F)` and `Q'(F) = (Q(F) ∩ wP(F)w⁻¹) V(F)`
(`IsGeometricLemmaDatum`). Let `h : G(𝔸) → ℂ` be measurable and left invariant under `U(𝔸)` and
under `P(F)`, and `y ∈ G(𝔸)`. If `∫ |h(w⁻¹ v y)| dv` over `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)` is finite,
then `v ↦ C_{U'} h(w⁻¹ v y)` is integrable over `(V'(F) ∩ wU'(𝔸)w⁻¹) \ V'(𝔸)` and
`∫ C_{U'} h(w⁻¹ v y) dv = ∫ h(w⁻¹ v y) dv`. Here `C_{U'} = subgroupConstantTerm` along `U'`, and
both Haar measures are normalized by `vol(V(F) \ V(𝔸)) = vol(V'(F) \ V'(𝔸)) = 1` (these quotients
of unipotent radicals are compact, so the Library's mass normalization gives mass one); functions on
the quotients are evaluated at the chosen representatives. -/
def GeometricLemmaUnfoldingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P U Q V P' U' Q' V' : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine V.X.left] [IsAffine P'.X.left] [IsAffine U'.X.left]
    [IsAffine V'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
    (q : Q ⟶ G) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (f : P' ⟶ P) (iU' : U' ⟶ P') (g' : Q' ⟶ Q) (iV' : V' ⟶ Q')
    [IsClosedImmersion (f ≫ p).hom.hom.left] [IsClosedImmersion (iU' ≫ f ≫ p).hom.hom.left]
    [IsClosedImmersion (iV' ≫ g' ≫ q).hom.hom.left],
    IsConnectedReductive G → IsParabolicSubgroup p →
    LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsParabolicSubgroup (f ≫ p) → LeviSubgroup.IsGeometricUnipotentRadical iU' →
    IsParabolicSubgroup (g' ≫ q) → LeviSubgroup.IsGeometricUnipotentRadical iV' →
    IsGeometricLemmaDatum p iU q iV f g' w →
    ∀ h : AdelicGroupPoints F G → ℂ, Measurable h →
      (∀ u ∈ parabolicUnipotentImage F p iU, ∀ x, h (u * x) = h x) →
      (∀ z ∈ rationalImage F p, ∀ x, h (z * x) = h x) →
      ∀ y : AdelicGroupPoints F G,
        ∫⁻ x, ‖h ((innerAdelicPoint F G w)⁻¹ *
            ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
              (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * y)‖ₑ
          ∂stabilizerMeasure F p (iV ≫ q) (innerAdelicPoint F G w) < ∞ →
        Integrable (fun x => subgroupConstantTerm F (iU' ≫ f ≫ p) h
            ((innerAdelicPoint F G w)⁻¹ *
              ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
                (SubgroupFunctor.range (iV' ≫ g' ≫ q))) : AdelicGroupPoints F G) * y))
          (intertwiningMeasure F (f ≫ p) iU' (iV' ≫ g' ≫ q) (innerAdelicPoint F G w)) ∧
        ∫ x, subgroupConstantTerm F (iU' ≫ f ≫ p) h
            ((innerAdelicPoint F G w)⁻¹ *
              ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
                (SubgroupFunctor.range (iV' ≫ g' ≫ q))) : AdelicGroupPoints F G) * y)
          ∂intertwiningMeasure F (f ≫ p) iU' (iV' ≫ g' ≫ q) (innerAdelicPoint F G w) =
        ∫ x, h ((innerAdelicPoint F G w)⁻¹ *
            ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
              (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * y)
          ∂stabilizerMeasure F p (iV ≫ q) (innerAdelicPoint F G w)

end Langlands.Global
