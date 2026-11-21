import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.Global.AdelicExponentPolynomials
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicNormOneDecomposition
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralProduct

/-! # Central covariance of Eisenstein series and their pointwise continuations

Left translation by a central point of `P(𝔸)` that acts on the inducing function by a scalar
multiplies each term of the actual Eisenstein series by the same scalar. Scalar meromorphic
uniqueness then gives the same covariance on the whole holomorphy domain of a pointwise
continuation. This is the input on Eisenstein series for the Fourier transform in the split
central direction in Lapid 2011, §8.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)

/-- Left translation by a point of `P(𝔸)` multiplies `m_P(g)^λ` by `q^λ`. -/
theorem IsIwasawaCompact.heightPower_map_mul (lam : ComplexCharacterParameter F P)
    (q : AdelicGroupPoints F P) (g : AdelicGroupPoints F G) :
    hK.heightPower lam (map F P G p q * g) = parameterPower F P lam q * hK.heightPower lam g := by
  rw [IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, parameterPower,
    hK.height_map_mul, map_add, Complex.exp_add]

/-- If `p(q)` is central in `G(𝔸)` and `φ(p(q) x) = s φ(x)`, then the Eisenstein series of `φ`
satisfies `E(p(q) g, φ, λ) = s q^λ E(g, φ, λ)`. This holds for the defining sum at every `λ`,
including the nonsummable case, where both sides are zero. -/
theorem IsIwasawaCompact.eisensteinSeries_central_mul {φ : AdelicGroupPoints F G → ℂ}
    {q : AdelicGroupPoints F P} {s : ℂ}
    (hz : ∀ x : AdelicGroupPoints F G, map F P G p q * x = x * map F P G p q)
    (hφ : ∀ x : AdelicGroupPoints F G, φ (map F P G p q * x) = s * φ x)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries φ lam (map F P G p q * g) =
      s * parameterPower F P lam q * hK.eisensteinSeries φ lam g := by
  unfold IsIwasawaCompact.eisensteinSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun c => ?_
  let d : AdelicGroupPoints F G := ((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G)
  have hd : d * (map F P G p q * g) = map F P G p q * (d * g) := by
    rw [← mul_assoc, ← hz d, mul_assoc]
  change hK.parameterTwist φ lam (d * (map F P G p q * g)) =
    s * parameterPower F P lam q * hK.parameterTwist φ lam (d * g)
  rw [hd, IsIwasawaCompact.parameterTwist, IsIwasawaCompact.parameterTwist, hφ,
    hK.heightPower_map_mul]
  ring

end AdelicGroupPoints

section Continuation

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hG : IsConnectedReductive G)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine G.X.left]
  [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- At a fixed point of `P(𝔸)`, `λ ↦ q^λ` is entire, hence meromorphic in coordinates on the
whole parameter space. -/
theorem isMeromorphicInCoordinatesOn_parameterPower [FiniteDimensional ℂ (ComplexCharacterParameter F P)]
    (q : AdelicGroupPoints F P) :
    IsMeromorphicInCoordinatesOn (fun lam => parameterPower F P lam q) univ :=
  isMeromorphicInCoordinatesOn_univ fun n e => by
    have h := differentiable_parameterPower_affine e.toLinearMap 0 q
    simp only [add_zero] at h
    exact h

include hG in
/-- A pointwise continuation of the Eisenstein series of `φ` satisfies the covariance of
`IsIwasawaCompact.eisensteinSeries_central_mul` at every parameter of its holomorphy domain. -/
theorem eisensteinContinuation_central_mul {φ : AdelicGroupPoints F G → ℂ}
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ x, IsMeromorphicInCoordinatesOn (fun lam => E lam x) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {q : AdelicGroupPoints F P} {s : ℂ}
    (hz : ∀ x : AdelicGroupPoints F G, map F P G p q * x = x * map F P G p q)
    (hφ : ∀ x : AdelicGroupPoints F G, φ (map F P G p q * x) = s * φ x)
    {lam : ComplexCharacterParameter F P} (hlam : lam ∈ D) (g : AdelicGroupPoints F G) :
    E lam (map F P G p q * g) = s * parameterPower F P lam q * E lam g := by
  obtain ⟨R, hR⟩ := hreg
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hE g).1
  have hrhs : IsMeromorphicInCoordinatesOn
      (fun lam => s * parameterPower F P lam q * E lam g) ((univ ∩ univ) ∩ D) :=
    ((isMeromorphicInCoordinatesOn_const s).mul
      (isMeromorphicInCoordinatesOn_parameterPower q)).mul (hE g)
  refine r.eqOn_of_regularParameter hA hT hG (hE (map F P G p q * g)) hrhs R ?_
    ⟨hlam, ⟨mem_univ _, mem_univ _⟩, hlam⟩
  intro lam' hlam'
  rw [hR lam' hlam']
  exact hK.eisensteinSeries_central_mul hz hφ lam' g

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- A finite packet inherits a covariance `E_j(λ)(z g) = κ(λ) E_j(λ)(g)` that holds on the part of
parameter space where its coefficients are nonzero. The identity is between the integrals as
written, with no integrability assumption. -/
theorem packetIntegral_central_mul {X : Type*} [MeasurableSpace X] (m : Measure X)
    {J : Type*} [Fintype J] {D : Set (ComplexCharacterParameter F P)}
    (e : X → ComplexCharacterParameter F P) (c : J → X → ℂ)
    (E : J → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (κ : ComplexCharacterParameter F P → ℂ) (z : AdelicGroupPoints F G)
    (hsupp : ∀ j x, c j x ≠ 0 → e x ∈ D)
    (hE : ∀ j lam, lam ∈ D → ∀ g, E j lam (z * g) = κ lam * E j lam g)
    (g : AdelicGroupPoints F G) :
    ∫ x, ∑ j, c j x * E j (e x) (z * g) ∂m = ∫ x, κ (e x) * ∑ j, c j x * E j (e x) g ∂m := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : c j x = 0
  · simp only [hc, zero_mul, mul_zero]
  · rw [hE j _ (hsupp j x hc) g]
    ring

end Continuation

namespace AdelicGroupPoints

section SplitComponent

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hG : IsConnectedReductive G)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- For `φ` in `A^n_P` and `b ∈ A_M` with `p(l(b))` central, the Eisenstein series satisfies
`E(p(l(b)) g, φ, λ) = l(b)^{λ + ρ_P} E(g, φ, λ)` at every `λ`. -/
theorem IsIwasawaCompact.eisensteinSeries_splitComponent_mul {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant p l φ) {b : AdelicGroupPoints F M}
    (hb : b ∈ RestrictionSplitCentre.canonicalSubgroup F M)
    (hz : ∀ x : AdelicGroupPoints F G,
      map F P G p (map F M P l b) * x = x * map F P G p (map F M P l b))
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries φ lam (map F P G p (map F M P l b) * g) =
      parameterPower F P (lam + halfModulusParameter F P) (map F M P l b) *
        hK.eisensteinSeries φ lam g := by
  rw [hK.eisensteinSeries_central_mul hz (hφ b hb) lam g, parameterPower, parameterPower,
    parameterPower, map_add, LinearMap.add_apply, Complex.exp_add, mul_comm (Complex.exp _)]

include hG in
/-- The covariance of `IsIwasawaCompact.eisensteinSeries_splitComponent_mul` holds at every
parameter of the holomorphy domain of a pointwise continuation. -/
theorem eisensteinContinuation_splitComponent_mul {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant p l φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ x, IsMeromorphicInCoordinatesOn (fun lam => E lam x) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {b : AdelicGroupPoints F M} (hb : b ∈ RestrictionSplitCentre.canonicalSubgroup F M)
    (hz : ∀ x : AdelicGroupPoints F G,
      map F P G p (map F M P l b) * x = x * map F P G p (map F M P l b))
    {lam : ComplexCharacterParameter F P} (hlam : lam ∈ D) (g : AdelicGroupPoints F G) :
    E lam (map F P G p (map F M P l b) * g) =
      parameterPower F P (lam + halfModulusParameter F P) (map F M P l b) * E lam g := by
  rw [eisensteinContinuation_central_mul hK r hA hT hG hE hreg hz (hφ b hb) hlam g, parameterPower,
    parameterPower, parameterPower, map_add, LinearMap.add_apply, Complex.exp_add,
    mul_comm (Complex.exp _)]

end SplitComponent

end AdelicGroupPoints

section SplitCentre

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A Z : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hG : IsConnectedReductive G)

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsClosedImmersion p.hom.hom.left] in
/-- The half-modulus character `m ↦ m^{ρ_P}` is trivial on the points of a commutative group
scheme mapping centrally into `G` through `P`. -/
theorem parameterPower_halfModulus_map_of_isCentral [IsAffine Z.toGrp.X.left] [Mono p.hom.hom]
    {j : Z.toGrp ⟶ P}
    (hj : IsCentral (j ≫ p)) (x : AdelicGroupPoints F Z.toGrp) :
    parameterPower F P (halfModulusParameter F P) (map F Z.toGrp P j x) = 1 := by
  have h0 : characterRestrict j (Lie.adjointDeterminantCharacter P) = 0 :=
    Lie.adjointDeterminantCharacter_restrict_eq_zero_of_isCentral P j
      (CoverPreimage.isCentral_of_comp_mono hj p j rfl)
  have hres : parameterRestrict j (halfModulusParameter F P) = 0 := by
    change (1 / 2 : ℂ) ⊗ₜ[ℤ] characterRestrict j (Lie.adjointDeterminantCharacter P) = 0
    rw [h0, TensorProduct.tmul_zero]
  rw [← parameterPower_parameterRestrict, hres, parameterPower, map_zero, LinearMap.zero_apply,
    Complex.exp_zero]

include hG in
/-- **Split-centre covariance.** Let `i : Z → G` be a central split torus factoring through the
Levi as `j ≫ l ≫ p`. Every pointwise continuation of the Eisenstein series of an `A^n_P` form
satisfies `E(λ)(i(x) g) = x^{λ|_Z} E(λ)(g)` at each positive point `x` of `Z` and each `λ ∈ D`.
Here `x^{λ|_Z}` is the parameter power of the restriction of `λ` along `j ≫ l`. -/
theorem eisensteinContinuation_splitCentre_mul {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant p l φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ x, IsMeromorphicInCoordinatesOn (fun lam => E lam x) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    (hZ : IsSplitTorus Z.toGrp) {i : Z.toGrp ⟶ G} (hi : IsCentral i) (j : Z.toGrp ⟶ M)
    (hji : j ≫ l ≫ p = i) (x : PositiveRealTorus.intrinsicSubgroup F Z)
    {lam : ComplexCharacterParameter F P} (hlam : lam ∈ D) (g : AdelicGroupPoints F G) :
    E lam (PositiveRealTorus.positivePointMap F G Z i x * g) =
      parameterPower F Z.toGrp (parameterRestrict (j ≫ l) lam) x * E lam g := by
  let : IsAffineHom Z.toGrp.X.hom := hZ.isAffineHom
  let : IsAffine Z.toGrp.X.left := isAffine_of_isAffineHom Z.toGrp.X.hom
  have hcl := r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  let := hcl.mono
  let : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  have hi' : IsCentral (j ≫ l ≫ p) := hji ▸ hi
  have hjc : IsCentral j := CoverPreimage.isCentral_of_comp_mono hi' (l ≫ p) j rfl
  have hcomp (y : AdelicGroupPoints F Z.toGrp) :
      map F Z.toGrp G i y = map F P G p (map F M P l (map F Z.toGrp M j y)) := by
    rw [← hji]
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]
  obtain ⟨f, hf⟩ := r.isCompatible.splitComponent.exists_factor hZ hjc
  have hb : map F Z.toGrp M j x ∈ RestrictionSplitCentre.canonicalSubgroup F M := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup r.isCompatible.splitComponent]
    refine ⟨PositiveRealTorus.pointMap F Z.toGrp A.toGrp (Adeles F) f x,
      PositiveRealTorus.map_intrinsicSubgroup_le F Z A (Additive.ofMul f) ⟨x, x.2, rfl⟩, ?_⟩
    rw [← hf]
    rfl
  have hz (y : AdelicGroupPoints F G) :
      map F P G p (map F M P l (map F Z.toGrp M j x)) * y =
        y * map F P G p (map F M P l (map F Z.toGrp M j x)) := by
    rw [← hcomp]
    exact (PositiveRealTorus.positivePointMap_commute F G Z i hi x y).eq
  have hmap : PositiveRealTorus.positivePointMap F G Z i x =
      map F P G p (map F M P l (map F Z.toGrp M j x)) := hcomp x
  have hjl : map F M P l (map F Z.toGrp M j x) = map F Z.toGrp P (j ≫ l) x := by
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]
  have hadd (y : AdelicGroupPoints F P) :
      parameterPower F P (lam + halfModulusParameter F P) y =
        parameterPower F P lam y * parameterPower F P (halfModulusParameter F P) y := by
    rw [parameterPower, parameterPower, parameterPower, map_add, LinearMap.add_apply,
      Complex.exp_add]
  have hjlc : IsCentral ((j ≫ l) ≫ p) := by
    rw [Category.assoc]
    exact hi'
  rw [hmap, AdelicGroupPoints.eisensteinContinuation_splitComponent_mul hK r hA hT hG hφ hE hreg hb
    hz hlam g, hjl, hadd, parameterPower_halfModulus_map_of_isCentral hjlc, mul_one,
    ← parameterPower_parameterRestrict]

end SplitCentre

/-- **Central covariance of continued Eisenstein series.** Let `φ` satisfy Lapid's `A^n_P`
condition `φ(a g) = a^{ρ_P} φ(g)` for `a ∈ A_M`, and let `E` be a pointwise continuation of its
Eisenstein series that is meromorphic in coordinates on `D` in every adelic variable and agrees
with the defining series for sufficiently regular parameters. Let `i : Z → G` be a central split
torus that factors through the Levi as `j ≫ l ≫ p`. Then for every positive point `x` of `Z`,
every `λ ∈ D` and every `g`, `E(λ)(i(x) g) = x^{λ|_Z} E(λ)(g)`, where `λ|_Z` is the restriction
of `λ` along `j ≫ l`. -/
def EisensteinContinuationCentralCovarianceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (φ : AdelicGroupPoints F G → ℂ), IsSplitComponentEquivariant p l φ →
      ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam) →
        ∀ (Z : CommGroupScheme (Spec (CommRingCat.of F))), IsSplitTorus Z.toGrp →
        ∀ (i : Z.toGrp ⟶ G), IsCentral i → ∀ (j : Z.toGrp ⟶ M), j ≫ l ≫ p = i →
          ∀ (x : PositiveRealTorus.intrinsicSubgroup F Z), ∀ lam ∈ D, ∀ g : AdelicGroupPoints F G,
            E lam (PositiveRealTorus.positivePointMap F G Z i x * g) =
              parameterPower F Z.toGrp (parameterRestrict (j ≫ l) lam) x * E lam g

theorem eisensteinContinuationCentralCovariance :
    EisensteinContinuationCentralCovarianceStatement := by
  intro F _ _ G P M A _ _ _ _ _ _ _ p _ l a r _ _ _ hA hT hG K hK φ hφ E D hE hreg Z hZ i hi j hji
    x lam hlam g
  exact eisensteinContinuation_splitCentre_mul hK r hA hT hG hφ hE hreg hZ hi j hji x hlam g

end Langlands.Global
