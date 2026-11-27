import Langlands.Global.CuspidalTestExpansion.PieceExpansion
import Langlands.Global.CuspidalTestExpansion.PieceProperties
import Langlands.Global.AdelicConstantTermAutomorphyStatement
import Langlands.Global.AdelicAutomorphicExponentDecompositionStatement

/-! # Bruhat pieces with full target parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

section Congr

variable {P U V H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine V.X.left] [IsAffine H.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}

omit [IsAffineHom G.X.hom] in
/-- Constant terms along equal closed immersions agree. -/
theorem subgroupConstantTerm_congr_hom {j₀ j₁ : H ⟶ G} (e : j₀ = j₁)
    [IsClosedImmersion j₀.hom.hom.left] [IsClosedImmersion j₁.hom.hom.left]
    (f : AdelicGroupPoints F G → ℂ) :
    subgroupConstantTerm F j₀ f = subgroupConstantTerm F j₁ f := by
  subst e
  rfl

omit [IsAffineHom G.X.hom] in
/-- Intertwining integrals, and the integrability of their integrands, along equal parabolic
and target morphisms agree. -/
theorem intertwining_congr_hom {p₀ p₁ : P ⟶ G} (ep : p₀ = p₁) {j₀ j₁ : V ⟶ G} (ej : j₀ = j₁)
    [IsClosedImmersion j₀.hom.hom.left] [IsClosedImmersion j₁.hom.hom.left]
    (hK₀ : IsIwasawaCompact p₀ K) (hK₁ : IsIwasawaCompact p₁ K) (iU : U ⟶ P)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (φ : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) :
    hK₀.intertwiningIntegral iU j₀ w φ lam = hK₁.intertwiningIntegral iU j₁ w φ lam ∧
      ∀ y, Integrable (hK₀.intertwiningIntegrand iU j₀ w φ lam y)
          (intertwiningMeasure F p₀ iU j₀ (innerAdelicPoint F G w)) ↔
        Integrable (hK₁.intertwiningIntegrand iU j₁ w φ lam y)
          (intertwiningMeasure F p₁ iU j₁ (innerAdelicPoint F G w)) := by
  subst ep
  subst ej
  exact ⟨rfl, fun _ => Iff.rfl⟩

end Congr

variable (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν

/-- When the target parabolic of a piece is all of `P_J`, the coset series over
`P_J(F) \ P_J(F)` of a `P_J(F)`-invariant function is that function. -/
theorem fullPiece_series {J₁ J : Idx} (t : NestedLeviParabolic fam J₁ J) (hJ₁ : J = J₁)
    (f : AdelicGroupPoints F G → ℂ)
    (hrat : IsLeftInvariantUnder F G (rationalImage F (t.inclusion ≫ fam.p J)) f)
    (y : AdelicGroupPoints F G) :
    ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
        f ((c.out : AdelicGroupPoints F G) * y) = f y := by
  have hle : rationalImage F (fam.p J) ≤ rationalImage F (t.inclusion ≫ fam.p J) := by
    apply rationalImage_le_of_range_le
    rw [t.inclusion_comp, hJ₁]
  have : Subsingleton (RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J)) :=
    ⟨fun a b => by
      induction a using Quotient.inductionOn with
      | _ x =>
      induction b using Quotient.inductionOn with
      | _ z =>
      apply Quotient.sound
      show QuotientGroup.rightRel _ x z
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
      exact hle (Subgroup.mul_mem _ z.2 (Subgroup.inv_mem _ x.2))⟩
  let c₀ : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J) := Quotient.mk _ 1
  rw [tsum_eq_single c₀ (fun c hc => (hc (Subsingleton.elim _ _)).elim)]
  exact hrat _ (hle (c₀.out).2) y

set_option maxHeartbeats 4000000 in
/-- For a Bruhat piece with full target `P_J`, decompose the constant term `C_{I₁} φ` into
generalized eigenfunctions with exponents `ν ∈ s`. For every parameter at which the piece's
intertwining integrand is integrable, the intertwining integral of `C_{I₁} φ` is the sum of the
intertwining integrals `T ν` of the components; `T ν` has unnormalized exponent
`n(ν + λ|_{P_{I₁}}) + offset` along `J` with polynomial degree at most `k` and lies in the span of
the positive split translates of the piece. The finite set `s`, the offset, the Weyl data and the
degree bound `k` do not depend on the parameter. -/
theorem fullPiece_expansion (hAut : ConstantTermAutomorphyStatement.{u})
    (hDec : AutomorphicExponentDecompositionStatement.{u})
    {I J I₁ J₁ : Idx} {n : normalizerPoints fam.i} [IsClosedImmersion (fam.p I).hom.hom.left]
    (pc : StandardBruhatPiece fam I J I₁ J₁ n) (hJ₁ : J = J₁)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K)
    (hKmax : IsMaximalCompactSubgroup F G K)
    (hK0 : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (fam.M J)
      (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I φ) :
    ∃ (s : Finset (ComplexCharacterParameter F (fam.P I₁)))
      (offset : ComplexCharacterParameter F (fam.P J))
      (c : fam.M J ⟶ fam.M I₁) (π : fam.P J ⟶ fam.M J) (k : ℕ),
      fam.l J ≫ π = 𝟙 (fam.M J) ∧
      IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n.val c ∧
      ∀ lam : ComplexCharacterParameter F (fam.P I),
        (∀ y, Integrable (hK₁.intertwiningIntegrand (fam.iU I₁)
            (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val
            (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
            (parameterRestrict pc.source.inclusion lam) y)
          (intertwiningMeasure F (pc.source.inclusion ≫ fam.p I) (fam.iU I₁)
            (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) (innerAdelicPoint F G n.val))) →
        ∃ T : ComplexCharacterParameter F (fam.P I₁) → AdelicGroupPoints F G → ℂ,
          hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val
              (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
              (parameterRestrict pc.source.inclusion lam) = ∑ ν ∈ s, T ν ∧
          (∀ ν ∈ s, fam.HasPolynomialOrbit J
            (weylParameter (fam.l I₁) c π (ν + parameterRestrict pc.source.inclusion lam) +
              offset) k (T ν)) ∧
          ∀ ν ∈ s, T ν ∈ fam.translateSpan J
            (hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J)
              n.val (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
              (parameterRestrict pc.source.inclusion lam)) := by
  subst hJ₁
  have hincl := pc.source.inclusion_comp
  have : IsClosedImmersion (fam.p I₁).hom.hom.left :=
    (fam.isCompatible I₁).parabolic.isClosedSubgroup
  have hK₁' : IsIwasawaCompact (fam.p I₁) K := hK₁.of_range_eq (by rw [hincl])
  have hI₁I : I₁ ≤ I :=
    (fam.le_iff_range_le I₁ I).mpr (SubgroupFunctor.range_le_of_factor pc.source.inclusion hincl)
  have hφ₁ := hAut F G fam (K.comap (ofInfinite F G).toMonoidHom) rho hsmooth hrho I I₁ hI₁I φ hφ
  obtain ⟨s, comp, hsum, hcomp⟩ :=
    hDec F G fam K hKmax hK0 hKlevi rho hsmooth hrho I₁ (fam.constantTerm I₁ φ) hφ₁
  choose! kν hkν using fun ν (hν : ν ∈ s) =>
    ((hcomp ν hν).2.1 : ∃ k : ℕ, fam.HasPolynomialOrbit I₁ ν k (comp ν))
  have hdeg : ∀ ν ∈ s, fam.HasPolynomialOrbit I₁ ν (s.sup kν) (comp ν) := fun ν hν =>
    HasPolynomialOrbit.mono (hkν ν hν) (Finset.le_sup hν)
  have hoff := fam.exists_offset_hasPolynomialOrbit_intertwiningIntegral
    pc.weylLevi pc.target.section_projection hK₁'
  obtain ⟨offset, hoffset⟩ := hoff
  refine ⟨s, offset, pc.conjugation, pc.target.projection, s.sup kν,
    pc.target.section_projection, pc.weylLevi, fun lam hint => ?_⟩
  set lam' := parameterRestrict pc.source.inclusion lam
  have hCT : subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ =
      fam.constantTerm I₁ φ := subgroupConstantTerm_congr_hom (by rw [hincl]) φ
  have ej : fam.iU J ≫ pc.target.inclusion ≫ fam.p J = fam.iU J ≫ fam.p J := by
    rw [pc.target.inclusion_comp]
  obtain ⟨hIntEq, hIntIff⟩ := intertwining_congr_hom hincl ej hK₁ hK₁' (fam.iU I₁) n.val
    (fam.constantTerm I₁ φ) lam'
  rw [hCT] at hint ⊢
  have hf : ∀ y, Integrable (hK₁'.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n.val
      (fam.constantTerm I₁ φ) lam' y) (intertwiningMeasure F (fam.p I₁) (fam.iU I₁)
        (fam.iU J ≫ fam.p J) (innerAdelicPoint F G n.val)) := fun y => (hIntIff y).mp (hint y)
  have hcont (ψ : AdelicGroupPoints F G → ℂ)
      (hψ : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I₁ ψ) :
      Continuous ψ := hψ.2.1.1
  have hinvU (ψ : AdelicGroupPoints F G → ℂ)
      (hψ : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I₁ ψ) :
      IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) ψ := by
    rintro _ ⟨y, rfl⟩ x
    exact hψ.1 _ (Subgroup.mem_sup_left ⟨y, rfl⟩) x
  obtain ⟨hEq, hRest⟩ := fam.intertwiningIntegral_exponentExpansion pc.weylLevi hK₁'
    offset hoffset (hcont _ hφ₁) (hinvU _ hφ₁) lam' hf s comp hsum
    (fun ν hν => hcont _ (hcomp ν hν).1) (fun ν hν => hinvU _ (hcomp ν hν).1) (s.sup kν) hdeg
  refine ⟨fun ν => hK₁'.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n.val (comp ν)
    lam', ?_, fun ν hν => (hRest ν hν).1, ?_⟩
  · rw [hIntEq, hEq]
  · intro ν hν
    rw [hIntEq]
    exact (hRest ν hν).2

end Langlands.Global.StandardParabolicFamily
