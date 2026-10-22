import Langlands.Global.AdelicFunctoriality.Norm

/-! # Exact local/global compatibility obligation for actual adelic norms -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain
open scoped NumberField

universe u v

/-- The canonical completed tensor maps are bijections, at every actual place.
This proposition supplies no comparison map as an assumption. -/
def CompletedTensorComparison : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L],
    (∀ p : HeightOneSpectrum (𝓞 K), Function.Bijective (finiteTensorMap (L := L) p)) ∧
    (∀ p : InfinitePlace K, Function.Bijective (infiniteTensorMap (L := L) p))

/-- On each principal adele, the product of actual local norms equals the
diagonal image of the genuine field norm. -/
def PrincipalNormCompatibility : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (x : L),
    adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x)

/-- Full tensor-decomposition and principal-norm compatibility target, with
independent universes and no unproved arithmetic hypotheses. -/
def NormCompatibility : Prop :=
  CompletedTensorComparison.{u, v} ∧ PrincipalNormCompatibility.{u, v}

end Langlands.Global.AdelicFunctoriality
