import Langlands.Global.CuspidalTestExpansion.FullPiece

/-! # Exponent expansions of Bruhat piece integrals -/

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

variable (fam : StandardParabolicFamily F G)

/-- A degree-bounded exponent expansion of `C_{I₁} φ` gives an expansion of the Bruhat
piece integral before its rational coset sum. In terms of the raw input label `ν`,
the raw output label along `J₁` is `w(ν - ρ_{I₁} + λ|_{P_{I₁}}) + ρ_{J₁}`.
Each output component belongs to the span of the `J₁` split translates of the piece integral. -/
def PieceIntegralExponentExpansionStatement
    {I J I₁ J₁ : StandardIndex F G fam.i fam.ν} {n : normalizerPoints fam.i}
    (pc : StandardBruhatPiece fam I J I₁ J₁ n)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K)
    (π : fam.P J₁ ⟶ fam.M J₁) : Prop :=
  fam.l J₁ ≫ π = 𝟙 (fam.M J₁) →
  ∀ (φ : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (fam.P I₁)))
    (comp : ComplexCharacterParameter F (fam.P I₁) → AdelicGroupPoints F G → ℂ) (k : ℕ),
    Continuous (fam.constantTerm I₁ φ) →
    IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁))
      (fam.constantTerm I₁ φ) →
    fam.constantTerm I₁ φ = ∑ ν ∈ s, comp ν →
    (∀ ν ∈ s, Continuous (comp ν) ∧
      IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) (comp ν) ∧
      fam.HasPolynomialOrbit I₁ ν k (comp ν)) →
    ∀ lam : ComplexCharacterParameter F (fam.P I),
      let lam' := parameterRestrict pc.source.inclusion lam
      let f := subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ
      (∀ y, Integrable (hK₁.intertwiningIntegrand (fam.iU I₁)
          (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val f lam' y)
        (intertwiningMeasure F (pc.source.inclusion ≫ fam.p I) (fam.iU I₁)
          (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) (innerAdelicPoint F G n.val))) →
      let T := fun ν => hK₁.intertwiningIntegral (fam.iU I₁)
        (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val (comp ν) lam'
      let Pint := hK₁.intertwiningIntegral (fam.iU I₁)
        (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val f lam'
      Pint = ∑ ν ∈ s, T ν ∧
      ∀ ν ∈ s, fam.HasPolynomialOrbit J₁
        (weylParameter (fam.l I₁) pc.conjugation π
          (ν - halfModulusParameter F (fam.P I₁) + lam') + halfModulusParameter F (fam.P J₁))
        k (T ν) ∧ T ν ∈ fam.translateSpan J₁ Pint

set_option maxHeartbeats 4000000 in
/-- The Bruhat piece integral transports all labels with the same degree bound. -/
theorem pieceIntegral_exponentExpansion
    {I J I₁ J₁ : StandardIndex F G fam.i fam.ν} {n : normalizerPoints fam.i}
    (pc : StandardBruhatPiece fam I J I₁ J₁ n)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K)
    (π : fam.P J₁ ⟶ fam.M J₁) : PieceIntegralExponentExpansionStatement fam pc hK₁ π := by
  intro hπ φ s comp k hfc hfU hsum hcomp lam
  dsimp only []
  intro hint
  have hincl := pc.source.inclusion_comp
  have : IsClosedImmersion (fam.p I₁).hom.hom.left :=
    (fam.isCompatible I₁).parabolic.isClosedSubgroup
  have hK₁' : IsIwasawaCompact (fam.p I₁) K := hK₁.of_range_eq (by rw [hincl])
  let lam' := parameterRestrict pc.source.inclusion lam
  have hCT : subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ =
      fam.constantTerm I₁ φ := subgroupConstantTerm_congr_hom (by rw [hincl]) φ
  have ej : fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J = fam.iU J₁ ≫ fam.p J₁ := by
    rw [pc.target.inclusion_comp]
  have hCongr (h : AdelicGroupPoints F G → ℂ) :=
    intertwining_congr_hom hincl ej hK₁ hK₁' (fam.iU I₁) n.val h lam'
  rw [hCT] at hint ⊢
  have hf := fun y => ((hCongr (fam.constantTerm I₁ φ)).2 y).mp (hint y)
  let offset := halfModulusParameter F (fam.P J₁) -
    weylParameter (fam.l I₁) pc.conjugation π (halfModulusParameter F (fam.P I₁))
  have hoffset := fam.hasPolynomialOrbit_intertwiningIntegral_halfModulusOffset pc.weylLevi hπ hK₁'
  obtain ⟨hEq, hRest⟩ := fam.intertwiningIntegral_exponentExpansion pc.weylLevi hK₁'
    offset hoffset hfc hfU lam' hf s comp hsum (fun ν hν => (hcomp ν hν).1)
    (fun ν hν => (hcomp ν hν).2.1) k (fun ν hν => (hcomp ν hν).2.2)
  refine ⟨?_, fun ν hν => ?_⟩
  · rw [(hCongr (fam.constantTerm I₁ φ)).1, hEq]
    apply Finset.sum_congr rfl
    intro ν hν
    exact (hCongr (comp ν)).1.symm
  rw [(hCongr (comp ν)).1, (hCongr (fam.constantTerm I₁ φ)).1]
  refine ⟨?_, (hRest ν hν).2⟩
  have hLabel : weylParameter (fam.l I₁) pc.conjugation π
        (ν - halfModulusParameter F (fam.P I₁) + lam') + halfModulusParameter F (fam.P J₁) =
      weylParameter (fam.l I₁) pc.conjugation π (ν + lam') + offset := by
    dsimp only [offset]
    simp only [map_add, map_sub]
    abel
  rw [hLabel]
  exact (hRest ν hν).1

end Langlands.Global.StandardParabolicFamily
