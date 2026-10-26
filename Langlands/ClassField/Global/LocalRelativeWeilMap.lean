import Langlands.ClassField.Global.RelativeWeilGroup
import Langlands.Global.CompletionPadicTower
import Langlands.Weil.Local.ExtensionWeil
import Langlands.LocalFactor.RankOne
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement

/-! # Local Weil groups mapped into relative global Weil groups

A property of a continuous homomorphism `W_{F_v} → W_{E/F}` from the actual local
Weil group of a completion into the relative Weil group at a supplied class family.
No such map is constructed and none is asserted to exist.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

universe u

namespace RelativeWeilGroup

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver v.asIdeal]

/-- The completion embedding `F_v → E_w` as a homomorphism of `ℚ_p`-algebras for the
canonical packages, using the published tower compatibility. -/
def completionPadicAlgHom :
    letI := (padicField v).algebra
    letI := (towerPadicField v w).algebra
    (padicField v).Carrier →ₐ[Padic (residuePrime v)] (towerPadicField v w).Carrier :=
  letI := (padicField v).algebra
  letI := (towerPadicField v w).algebra
  haveI := towerPadicField_isScalarTower v w
  IsScalarTower.toAlgHom (Padic (residuePrime v)) (v.adicCompletion F) (w.adicCompletion E)

theorem completionPadicAlgHom_apply (x : v.adicCompletion F) :
    completionPadicAlgHom v w x = algebraMap (v.adicCompletion F) (w.adicCompletion E) x :=
  rfl

/-- The embedding `E_w → \bar{F_v}` through Mathlib's chosen closure isomorphism over the
completion map; it is the embedding along which `completionWeilMap` is formed. -/
def completionClosureEmbedding :
    w.adicCompletion E →+* AlgebraicClosure (v.adicCompletion F) :=
  Weil.Local.extensionFieldEmbedding (padicField v) (towerPadicField v w)
    (completionPadicAlgHom v w)

/-- On `F_v` the embedding is the structure map of the closure. -/
theorem completionClosureEmbedding_algebraMap (x : v.adicCompletion F) :
    completionClosureEmbedding v w (algebraMap (v.adicCompletion F) (w.adicCompletion E) x) =
      algebraMap (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) x :=
  Weil.Local.extensionFieldEmbedding_comp (padicField v) (towerPadicField v w)
    (completionPadicAlgHom v w) x

/-- The actual local Weil map `W_{E_w} → W_{F_v}` along the completion map. -/
abbrev completionWeilMap :
    Weil.Local.localWeilGroup (towerPadicField v w) →ₜ*
      Weil.Local.localWeilGroup (padicField v) :=
  Weil.Local.extensionWeilMap (padicField v) (towerPadicField v w) (completionPadicAlgHom v w)

variable {c : FundamentalClass.ClassFamily.{u}} [IsGalois F E]

/-- `ι : W_{F_v} → W_{E/F}` is the local-to-relative Weil map for the geometric
reciprocity candidate `e` of `E_w`:
`e` satisfies the published geometric normalization; through
`E → E_w → \bar{F_v}`, the image of `ι g` in `Gal(E/F)` acts as the Galois image of `g`;
and on `W_{E_w}`, `ι` is the inverse of `e` followed by `E_wˣ → C_E`. The inverse is
the one compatible with the arithmetic normalization of the class family. -/
def IsLocalRelativeWeilMap
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) : Prop :=
  LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v w)
      (towerPadicField v w).canonicalTopologicalData e ∧
    (∀ (g : Weil.Local.localWeilGroup (padicField v)) (x : E),
      completionClosureEmbedding v w
          (algebraMap E (w.adicCompletion E) (projection c F E (ι g) x)) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField v) g)
          (completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x))) ∧
    ∀ y : Weil.Local.localWeilGroup (towerPadicField v w),
      ι (completionWeilMap v w y) =
        (inclusion c F E (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
          (LocalFactor.RankOne.reciprocityUnits (towerPadicField v w) e y)))⁻¹

end RelativeWeilGroup

end Langlands.ClassField.Global
