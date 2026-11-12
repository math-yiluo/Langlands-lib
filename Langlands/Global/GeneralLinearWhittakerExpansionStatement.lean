import Langlands.Automorphic.GeneralLinearCuspidalComparison
import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.GeneralLinearGlobalWhittaker

/-! # The Whittaker expansion of smooth cusp forms on `GL_{r+1}`

Getz–Hahn, Theorem 11.3.6: a smooth cuspidal function `φ` of uniform moderate growth on
`GL_{r+1}(F) \ GL_{r+1}(𝔸)` is the sum of the values of its global Whittaker function
`W_φ(g) = ∫_{N(F) \ N(𝔸)} φ(n g) conj(ψ_N(n)) dn` at `diag(γ, 1) g`, over
`γ ∈ N_r(F) \ GL_r(F)`, absolutely and uniformly on compact sets. The group is the actual
general linear group scheme over `Spec F`, `N` its upper unipotent subgroup functor, and the
measure on `N(F) \ N(𝔸)` the quotient Haar measure of total mass one. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

local instance whittakerExpansionGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance whittakerExpansionGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The Whittaker expansion of smooth cusp forms on `GL_{r+1}` (Getz–Hahn, Theorem 11.3.6;
Cogdell 2004, Theorem 1.1; Shalika 1974, Theorem 5.9). Let `ψ` be a nontrivial continuous
character of `𝔸` trivial on `F`, `m_0, …, m_{r-1} ∈ F` nonzero, and `φ` a function on
`GL_{r+1}(F) \ GL_{r+1}(𝔸)` that is smooth (finite level, smooth in the archimedean variable),
of uniform moderate growth (every derivative is bounded by `C ‖g‖^R` for one `R`) and cuspidal
(its constant terms along the standard maximal parabolics vanish). Let
`W(g) = ∫_{N(F) \ N(𝔸)} φ(n g) conj(ψ(∑ m_i n_{i,i+1})) dn` with `dn` of total mass one. Then
for every `g` the family `γ ↦ W(diag(γ, 1) g)` over `N_r(F) \ GL_r(F)` is absolutely summable
with sum `φ(g)`, and the sums of the absolute values converge uniformly on compact sets. -/
def WhittakerExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ) {N d : ℕ}
    (rho : MatrixRepresentation
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (Fin N))
    (hsmooth : SmoothOfRelativeDimension d
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)).X.hom)
    (hcalc : AdelicDifferentialCommutator F _ hsmooth),
    IsClosedSubgroup rho →
    ∀ (ψ : AddChar (Adeles F) ℂ), Continuous ψ →
      (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) → ψ ≠ 1 →
    ∀ (m : Fin r → F), (∀ i, m i ≠ 0) →
    ∀ (φ : FinitePlotSmoothRationalFunctions F
        (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))),
      HasAdelicUniformModerateGrowth F _ rho hsmooth hcalc φ →
      haveI : CompactSpace (AdeleQuotient F) := compactSpace_adeleQuotient F
      φ.val ∈ (generalLinearStandardBlockVanishingSubrepresentation F (r + 1)).toSubmodule →
      let term : UnipotentRationalCosets F r → AdelicGroupPoints F
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) → ℂ :=
        fun q g => generalLinearWhittakerFunction F r ψ m (evaluate F _ φ.val)
          (cornerAdelicPoint F r q.out * g)
      (∀ g, Summable (fun q => ‖term q g‖) ∧ HasSum (fun q => term q g) (evaluate F _ φ.val g)) ∧
      ∀ C : Set (AdelicGroupPoints F
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))),
        IsCompact C →
        TendstoUniformlyOn (fun (s : Finset (UnipotentRationalCosets F r)) g =>
            ∑ q ∈ s, ‖term q g‖) (fun g => ∑' q, ‖term q g‖) atTop C

end Langlands.Global
