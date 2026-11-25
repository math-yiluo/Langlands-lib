import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Global.Factors.RelativeGammaComparisonStatement
import Langlands.Representation.Whittaker.Spherical

/-! # Factorization of global Whittaker functions at an unramified place

Cogdell 2004, §2.2, p.206 (with Jacquet–Shalika 1981 and Shintani 1976). See the paired
Markdown for sources and normalizations.
-/

noncomputable section
universe u uQ
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance unramifiedWhittakerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unramifiedWhittakerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, §2.2, p.206** (Shintani's formula, applied to the local factor of a
global Whittaker function): factorization of the global Whittaker function of a vector
that is spherical outside `S`, at one finite place `v ∉ S`.

Let `ψ` be a unitary character of `𝔸` trivial on `F`, `T` an actual cuspidal realization
of `GL_(r+1)` with spectral presentation `P`, and `S` a finite set of finite places
containing the exceptional set of `P` outside which every finite component of `ψ` has
conductor `𝒪_v`. Let `x` be fixed by `GL_(r+1)(𝒪_w)` at every finite `w ∉ S`, let `v ∉ S`,
let `ψ_v` be the component of `ψ` at `v`, `ϖ` a uniformizer of `F_v`, `q` the residue
cardinality, and `a` a tuple whose multiset is the Satake parameter of `P` at `v`. Then for
every `g ∈ GL_(r+1)(𝔸)` with `g_v = 1` and every `h ∈ GL_(r+1)(F_v)`, writing `ι_v h` for
the adelic point with `h` at `v` and `1` elsewhere,
`W_x(g · ι_v h) = W_x(g) · W°(h; a)` for the `ψ`-Whittaker function `W_x` and the
spherical Whittaker function `W°` of the standard character of `ψ_v`, and likewise for the
`ψ⁻¹`-Whittaker function with the inverse standard character. -/
def UnramifiedWhittakerFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (x : T.Space), IsSphericalOutside F T S x →
  ∀ (v : FinitePlace F) (hv : v ∉ S)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)),
    ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv →
  ∀ (ϖ : (CompletionPadic.padicField v).Carrierˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) ϖ)
    (a : Fin (r + 1) → ℂˣ),
    Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)) →
  ∀ g : Points F (r + 1), finiteComponent F (r + 1) v g = 1 →
  ∀ h : FiniteLocalGL F (r + 1) v,
    let ιh : Points F (r + 1) := (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
      (AdelicGL.ofFinite F (r + 1) (FiniteAdelicGL.localInclusion F (r + 1) v h))
    let q : ℕ := (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality
    cuspWhittaker F T ψ.complex x (g * ιh) =
        cuspWhittaker F T ψ.complex x g *
          GeneralLinear.Spherical.sphericalWhittaker hϖ
            (@Whittaker.standardCharacter _ _
              (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r) q a h ∧
      cuspWhittaker F T ψ.complex⁻¹ x (g * ιh) =
        cuspWhittaker F T ψ.complex⁻¹ x g *
          GeneralLinear.Spherical.sphericalWhittaker hϖ
            (@Whittaker.inverseStandardCharacter _ _
              (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r) q a h

end Langlands.Global.RankinSelbergGlobal
