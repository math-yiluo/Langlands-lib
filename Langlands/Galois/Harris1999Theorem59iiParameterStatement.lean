import Langlands.Weil.Representation.CoefficientExtension
import Langlands.Galois.Harris1999Theorem59Statement
import Mathlib.NumberTheory.Padics.Complex

/-!
# Harris (1999), Theorem 5.9(ii): parameter existence and irreducibility

Two derived, unproved statement definitions about the local behaviour at a
split supercuspidal place of the compatible families of Harris (1999),
Theorem 5.9, printed pp.314-315.

* `Harris1999Theorem59iiParameterStatement`: for each prime `ℓ` and each
  identification `ιΩ : ℚ̄_ℓ ≃+* ℂ` there is a map `Φ ℓ ιΩ` from smooth classes of
  `GL_{r+1}(K_v)` to `ℚ̄_ℓ`-representations of `Gal(K̄_v/K_v)` such that every
  cuspidal `Π` satisfying the hypotheses of Theorem 5.9 has a family as in
  Theorem 5.9(i) whose restriction at `v`, after extending scalars to `ℚ̄_ℓ`
  along any continuous embedding compatible with `ιΩ`, is `Φ ℓ ιΩ (Π_v)`.
  One fixed family serves every coefficient place and every compatible
  identification.
* `HarrisSupercuspidalRestrictionIrreducibleStatement`: every family as in
  Theorem 5.9(i) restricts at `v` to an absolutely irreducible representation,
  for coefficient places of residue characteristic different from that of `v`.

Neither statement uses Harris's parameter `σ(Π_v)` of (5.4)-(5.5), which is
built from the cohomology of the Drinfeld tower. They are consequences of
Theorem 5.9(ii) together with the facts that (5.4)-(5.5) are purely local
(p.314) and that `σ(π_v)` is irreducible (Henniart, cited p.313).
-/

noncomputable section

universe uK uL uV uW uF uΩ uG

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Automorphic
open NumberField (IsTotallyComplex IsCMField)

/-- Extension of scalars of a finite-dimensional representation along a field
homomorphism `j : F →+* Ω`: the representation `g ↦ id_Ω ⊗ A(g)` on the
tensor-product carrier `Ω ⊗[F] A`, where `Ω` is an `F`-algebra through `j`. -/
def scalarExtensionAlong {F : Type uF} [Field F] {Ω : Type uΩ} [Field Ω]
    {G : Type uG} [Monoid G] (j : F →+* Ω) (A : FiniteRepresentation.{uF, uG, uV} F G) :
    FiniteRepresentation.{uΩ, uG, max uΩ uV} Ω G :=
  letI : Algebra F Ω := j.toAlgebra
  FiniteRepresentation.extendCoefficients Ω A

/-- Derived parameter-existence form of Harris (1999), Theorem 5.9(ii).

The setting of Theorem 5.9 is as in `Harris1999Theorem59iStatement`, for a fixed
place `v` of the CM field `K` that differs from its complex conjugate. There
is a map `Φ`, chosen after `K`, `K₀`, `r` and `v` but before the automorphic
representation. For each prime `ℓ` and each
field isomorphism `ιΩ : ℚ̄_ℓ ≃+* ℂ`, it sends a smooth class of
`GL_{r+1}(K_v)` to a `ℚ̄_ℓ`-representation of `Gal(K̄_v/K_v)`. For every
cuspidal realization `S` with spectral presentation `P` that is regular
algebraic and conjugate self-dual, with supercuspidal local component at `v`,
there is a family `R` as in Theorem 5.9(i) with the following property. Let
`ℓ ≠ p_v`, `ιΩ`, a finite place `lam` of `L` and a continuous embedding
`j : L_lam →+* ℚ̄_ℓ` be such that `ιΩ ∘ j` restricts to `ι` on `L`. Then
the restriction of `R_lam` to `Gal(K̄_v/K_v)`, with scalars extended along
`j`, is equivalent to `Φ ℓ ιΩ (Π_v)`. -/
def Harris1999Theorem59iiParameterStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [IsCMField K] [CompactSpace (AdeleQuotient K)]
    (K₀ : IntermediateField ℚ K),
    Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ →
    ∀ (r : ℕ), 1 ≤ r → ∀ (v : FinitePlace K), Harris.conjPlace K v ≠ v →
    ∃ Φ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (PadicAlgCl ℓ ≃+* ℂ) →
        Langlands.SmoothRep.IsoClass.{0, uK, uK} ℂ (FiniteLocalGL K (r + 1) v) →
        FiniteRepresentation.{0, uK, 0} (PadicAlgCl ℓ) (LocalGroup v),
      ∀ (S : CuspidalOperatorRealization K r) (P : CuspidalSpectralPresentation.{uK, uW} S),
        S.isoClass.IsRegularAlgebraic → S.isoClass.IsConjugateSelfDual →
        (P.localComponent v).IsSupercuspidal →
        ∃ (L : Type uL) (fieldL : Field L),
          letI : Field L := fieldL
          ∃ (numberFieldL : NumberField L),
            letI : NumberField L := numberFieldL
            ∃ (ι : L →+* ℂ) (R : Collection.{uK, uL, uV} K L ∅) (m : ℤ),
              IsPureCompatible ∅ R m ∧ HasRank ∅ R (r + 1) ∧
              CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated.{uK, uL, uV, uW}
                S.isoClass ι ∅ R ∧
              ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ residueCharacteristic v →
                ∀ (ιΩ : PadicAlgCl ℓ ≃+* ℂ) (lam : FinitePlace L)
                  (j : FiniteCompletion L lam →+* PadicAlgCl ℓ), Continuous j →
                  (∀ x : L, ιΩ (j (NumberField.FinitePlace.embedding lam x)) = ι x) →
                  Nonempty (FiniteRepresentation.Equiv
                    (scalarExtensionAlong j (atFinitePlace v (R ⟨lam, by simp⟩)).val)
                    (Φ ℓ ιΩ (P.localComponent v).isoClass))

/-- Absolute irreducibility at a split supercuspidal place: in the setting of
Theorem 5.9, for every family `R` as in Theorem 5.9(i) for the class `c` and
every finite place `lam` of `L` whose residue characteristic differs from that
of `v`, the restriction of `R_lam` to `Gal(K̄_v/K_v)`, with scalars extended
to an algebraic closure of `L_lam`, is irreducible. -/
def HarrisSupercuspidalRestrictionIrreducibleStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [IsCMField K] [CompactSpace (AdeleQuotient K)]
    (K₀ : IntermediateField ℚ K),
    Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ →
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (c : CuspidalOperatorRealization.IsoClass K r) (v : FinitePlace K),
      c.IsRegularAlgebraic → c.IsConjugateSelfDual →
      Harris.conjPlace K v ≠ v →
      CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent.{uK, uW} c v →
      ∀ (L : Type uL) [Field L] [NumberField L] (ι : L →+* ℂ)
        (R : Collection.{uK, uL, uV} K L ∅) (m : ℤ),
        IsPureCompatible ∅ R m → HasRank ∅ R (r + 1) →
        CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated.{uK, uL, uV, uW} c ι ∅ R →
        ∀ lam : FinitePlace L, residueCharacteristic v ≠ residueCharacteristic lam →
          Representation.IsIrreducible
            (scalarExtensionAlong
              (algebraMap (FiniteCompletion L lam) (AlgebraicClosure (FiniteCompletion L lam)))
              (atFinitePlace v (R ⟨lam, by simp⟩)).val).representation

end Langlands.GaloisRepresentation
