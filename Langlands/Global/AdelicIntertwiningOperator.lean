import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicParabolicQuotient
import Langlands.Global.AdelicSubgroupHaarMeasure
import Langlands.Global.LeftCosetFundamentalDomain
import Langlands.Automorphic.GroupSchemeConstantTermConjugation

/-! # Intertwining operators on actual adelic points

Bernstein–Lapid §2.2 and Mœglin–Waldspurger II.1.6: for parabolics `P = MU`, `Q = M'V` of `G`
and a rational point `w` with `w M w⁻¹ = M'`,
`[M(w, λ)φ]_{wλ}(g) = ∫_{(V(F) ∩ wU(F)w⁻¹) \ V(𝔸)} φ_λ(w⁻¹ v g) dv`,
with Haar measure on `V(𝔸)` normalized by `vol(V(F) \ V(𝔸)) = 1`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]

section Parameters

variable {P Q M M' : GroupScheme (Spec (CommRingCat.of F))}

/-- The parameter `wλ ∈ X^*(Q) ⊗ ℂ` of `λ ∈ X^*(P) ⊗ ℂ`, for `l : M → P`, the conjugation
`c : M' → M` (`c(m') = w⁻¹ m' w`) and a projection `π' : Q → M'`: on characters it is
`χ ↦ χ ∘ l ∘ c ∘ π'`. -/
def weylParameter (l : M ⟶ P) (c : M' ⟶ M) (π' : Q ⟶ M') :
    ComplexCharacterParameter F P →ₗ[ℂ] ComplexCharacterParameter F Q :=
  AlgebraTensorModule.map LinearMap.id (characterRestrict (π' ≫ c ≫ l)).toIntLinearMap

omit [NumberField F] in
theorem weylParameter_tmul (l : M ⟶ P) (c : M' ⟶ M) (π' : Q ⟶ M') (s : ℂ)
    (χ : rationalCharacters P) :
    weylParameter l c π' (s ⊗ₜ[ℤ] χ) = s ⊗ₜ[ℤ] characterRestrict (π' ≫ c ≫ l) χ :=
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The pair `(w, c)` presents an element of `W(P, Q)` (Bernstein–Lapid §2.1): the point `w`
over the base satisfies `w M w⁻¹ = M'`, witnessed by an isomorphism `c : M' → M` with
`l(c(m')) = w⁻¹ l'(m') w` in `G`. -/
structure IsWeylConjugation (p : P ⟶ G) (l : M ⟶ P) (q : Q ⟶ G) (l' : M' ⟶ Q)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M) : Prop where
  isIso : IsIso c
  comp_eq : c ≫ l ≫ p = l' ≫ q ≫ (G.innerIso w).inv

end Parameters

section Integral

variable (F)
variable {G P U V : GroupScheme (Spec (CommRingCat.of F))}

/-- The discrete subgroup `V(F) ∩ w U(𝔸) w⁻¹` of `V(𝔸)`, for `p ∘ iU : U → G`, `j : V → G` and
an adelic point `w`. For rational `w` and the unipotent radicals of `P` and `Q` this is
`(V ∩ wUw⁻¹)(F)`. -/
def intertwiningRationalSubgroup (p : P ⟶ G) (iU : U ⟶ P) (j : V ⟶ G)
    (w : AdelicGroupPoints F G) :
    Subgroup (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
  AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j) ⊓
    (parabolicUnipotentImage F p iU).comap
      ((MulAut.conj w⁻¹).toMonoidHom.comp
        (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)).subtype)

theorem mem_intertwiningRationalSubgroup_iff (p : P ⟶ G) (iU : U ⟶ P) (j : V ⟶ G)
    (w : AdelicGroupPoints F G)
    (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
    v ∈ intertwiningRationalSubgroup F p iU j w ↔
      v ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j) ∧
        w⁻¹ * (v : AdelicGroupPoints F G) * w ∈ parabolicUnipotentImage F p iU := by
  simp [intertwiningRationalSubgroup]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

theorem isDiscrete_intertwiningRationalSubgroup (p : P ⟶ G) (iU : U ⟶ P) (j : V ⟶ G)
    (w : AdelicGroupPoints F G) :
    IsDiscrete (intertwiningRationalSubgroup F p iU j w :
      Set (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))) :=
  (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range j)).mono
    inf_le_left

variable [IsAffine V.X.left] in
/-- The measure on `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` induced by the Haar measure of `V(𝔸)` normalized
by `vol(V(F) \ V(𝔸)) = 1`, for a closed immersion `j : V → G`. -/
def intertwiningMeasure (p : P ⟶ G) (iU : U ⟶ P) (j : V ⟶ G)
    [IsClosedImmersion j.hom.hom.left] (w : AdelicGroupPoints F G) :
    Measure (LeftCosetSpace (intertwiningRationalSubgroup F p iU j w)) :=
  haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  LeftCosetSpace.discreteQuotientMeasure (intertwiningRationalSubgroup F p iU j w)
    (isDiscrete_intertwiningRationalSubgroup F p iU j w)
    (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j))

end Integral

section Operator

variable {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The integrand `v ↦ φ_λ(w⁻¹ v g)` of the intertwining integral, evaluated at the chosen
representative `v ∈ V(𝔸)` of each class in `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`. Here `w` is a point
over the base, acting on adelic points through `innerAdelicPoint`. -/
def IsIwasawaCompact.intertwiningIntegrand (hK : IsIwasawaCompact p K) (iU : U ⟶ P)
    (j : V ⟶ G) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G)
    (x : LeftCosetSpace (intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))) : ℂ :=
  hK.parameterTwist φ lam ((innerAdelicPoint F G w)⁻¹ *
    ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
      AdelicGroupPoints F G) * g)

/-- The intertwining integral `∫_{(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)} φ_λ(w⁻¹ v g) dv` for the Haar measure
on `V(𝔸)` with `vol(V(F) \ V(𝔸)) = 1`; it is `0` where the integrand is not integrable. -/
def IsIwasawaCompact.intertwiningIntegral (hK : IsIwasawaCompact p K) (iU : U ⟶ P)
    (j : V ⟶ G) [IsAffine V.X.left] [IsClosedImmersion j.hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) : ℂ :=
  ∫ x, hK.intertwiningIntegrand iU j w φ lam g x
    ∂intertwiningMeasure F p iU j (innerAdelicPoint F G w)

/-- The intertwining operator `M(w, λ)φ (g) = m_Q(g)^{-wλ} ∫ φ_λ(w⁻¹ v g) dv` of
Bernstein–Lapid §2.2, so that `[M(w, λ)φ]_{wλ}` is the intertwining integral over
`(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` for the unipotent radical `iV : V → Q`. The parameter `wλ` is
`weylParameter l c π' λ`. -/
def IsIwasawaCompact.intertwiningOperator [IsAffine Q.X.left] {q : Q ⟶ G}
    [IsClosedImmersion q.hom.hom.left] (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
    (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsAffine V.X.left]
    [IsClosedImmersion (iV ≫ q).hom.hom.left] (c : M' ⟶ M) (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) : ℂ :=
  hK'.heightPower (-weylParameter l c π' lam) g * hK.intertwiningIntegral iU (iV ≫ q) w φ lam g

end Operator

end Langlands.Global.AdelicGroupPoints
