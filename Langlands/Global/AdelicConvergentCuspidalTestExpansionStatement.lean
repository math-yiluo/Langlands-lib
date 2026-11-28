import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicIntertwiningOperator

/-! # The convergent Eisenstein comparison in Levi cusp tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints
  Langlands.Aubert.General.RationalPointFamily RealTorusSpace

/-- A finite family of affine unnormalized labels for the competing Weyl
terms, with the ambient real linear part of each label specified. -/
structure CompetingWeylExponents
    {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I J : StandardIndex F G fam.i fam.ν)
    (selected : relativeWeylGroup fam.i) where
  size : ℕ
  weyl : Fin size → relativeWeylGroup fam.i
  linear : Fin size → (ComplexCharacterParameter F (fam.P I) →ₗ[ℂ]
    ComplexCharacterParameter F (fam.P J))
  offset : Fin size → ComplexCharacterParameter F (fam.P J)
  competing : ∀ k, weyl k ≠ selected
  positive : ∀ k, ∀ alpha ∈ I.val,
    schemeWeylCharacterAction fam.i (weyl k) alpha ∈ positiveRelativeRoots fam.i fam.ν
  ambient : ∀ k lam, fam.chamberEmbedding J (parameterRealPart F (fam.P J) (linear k lam)) =
    relativeWeylRealCharacterAction fam.i (weyl k)
      (fam.chamberEmbedding I (parameterRealPart F (fam.P I) lam))

/-- The label of a competing term as a function of the inducing parameter. -/
def CompetingWeylExponents.label
    {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {fam : StandardParabolicFamily F G} {I J : StandardIndex F G fam.i fam.ν}
    {selected : relativeWeylGroup fam.i} (data : CompetingWeylExponents fam I J selected)
    (k : Fin data.size) (lam : ComplexCharacterParameter F (fam.P I)) :
    ComplexCharacterParameter F (fam.P J) :=
  data.linear k lam + data.offset k

/-- The scalar form of Bernstein–Lapid (6.20) in the source convergence
region. Subtract the tested constant term of the selected twisted
intertwiner, which is the published intertwining integral. The remaining
tested terms come from finitely many competing unnormalized Weyl labels. -/
def ConvergentCuspidalTestExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I Q : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M I),
    IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) n.val c →
    let w : relativeWeylGroup fam.i := QuotientGroup.mk n
    (∀ alpha ∈ I.val, schemeWeylCharacterAction fam.i w alpha ∈ Q.val) →
    (∀ alpha ∈ Q.val, schemeWeylCharacterAction fam.i w⁻¹ alpha ∈ I.val) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
      IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G fam.i fam.ν,
        IsMaximalCompactSubgroup F (fam.M J)
          (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom),
        IsClosedSubgroup rho →
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
          ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
        let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        let hT := fam.maximalSplit.isSplitSubtorus.1
        ∀ phi : AdelicGroupPoints F G → ℂ, fam.IsAutomorphicOn hsmooth Kinf rho I phi →
          ∀ J : StandardIndex F G fam.i fam.ν,
            ∃ (R : ℝ) (data : CompetingWeylExponents fam I J w),
              ∀ lam : ComplexCharacterParameter F (fam.P I), r.IsRegularParameter hA hT R lam →
                ∃ terms : Fin data.size → AdelicGroupPoints F G → ℂ,
                  (∀ k, fam.HasUnnormalizedExponent J (data.label k lam) (terms k)) ∧
                  ∀ test : AdelicGroupPoints F (fam.M J) → ℂ, fam.IsLeviCuspForm Kinf rho J test →
                    ∀ g : AdelicGroupPoints F G,
                      (∀ k, Integrable (fam.leviPairingIntegrand J (terms k) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J))) ∧
                      fam.leviPairing J (fam.constantTerm J (hK.eisensteinSeries phi lam)) g test -
                          fam.leviPairing J (fam.parabolicConstantTerm Q J
                            (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q)
                              n.val phi lam)) g test =
                        ∑ k, fam.leviPairing J (terms k) g test

namespace CompetingWeylExponents

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G} {I J : StandardIndex F G fam.i fam.ν}
  {selected : relativeWeylGroup fam.i}

/-- The concatenation of finitely many lists of competing Weyl exponents. -/
def sigma {p : ℕ} (data : Fin p → CompetingWeylExponents fam I J selected) :
    CompetingWeylExponents fam I J selected where
  size := ∑ v, (data v).size
  weyl j := (data (finSigmaFinEquiv.symm j).1).weyl (finSigmaFinEquiv.symm j).2
  linear j := (data (finSigmaFinEquiv.symm j).1).linear (finSigmaFinEquiv.symm j).2
  offset j := (data (finSigmaFinEquiv.symm j).1).offset (finSigmaFinEquiv.symm j).2
  competing _ := (data _).competing _
  positive _ := (data _).positive _
  ambient _ := (data _).ambient _

end CompetingWeylExponents

end Langlands.Global
