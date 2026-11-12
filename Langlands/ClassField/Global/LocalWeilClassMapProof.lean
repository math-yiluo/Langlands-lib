import Langlands.ClassField.Global.LocalWeilClassMapStatement
import Langlands.Weil.Local.FiniteGaloisFundamental
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof

/-! # Existence of local Weil class maps at completions -/

noncomputable section

namespace Langlands.Weil.Local.FiniteGaloisTower

universe u

open LocalClassField LocalFactor.RankOne ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime]

/-- **Weil–Shafarevich for a finite Galois extension of `p`-adic fields.** Given geometric Weil
reciprocity for every `p`-adic field, the actual local Weil group `W_F` maps continuously into
the extension of `Gal(E/F)` by `Eˣ` attached to any normalized cocycle whose class is
fundamental, compatibly with the Galois projections and with inverse reciprocity on `W_E`.
The algebra structure and the topology of `E` are arbitrary instances equal to the ones given
by `f` and by the canonical topological data. -/
theorem exists_weilClassMap (hW : WeilReciprocityExistenceUniqueness.{u})
    (F E : PadicField.{u} p) (f : F.Carrier →ₐ[Padic p] E.Carrier)
    [inst : Algebra F.Carrier E.Carrier] (hinst : inst = extensionAlgebra F E f)
    [hfd : FiniteDimensional F.Carrier E.Carrier] [hgal : IsGalois F.Carrier E.Carrier]
    [τ : TopologicalSpace E.Carrier] (hτ : τ = E.canonicalTopologicalData.topology)
    (J : InvariantFamily.{u,u} p) (hJ : J.RelativeClassFormation)
    (hA : J.ArithmeticNormalization)
    (e : ReciprocityCandidate E)
    (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)
    (z : NormalizedTwoCocycle Gal(E.Carrier/F.Carrier) E.Carrierˣ)
    (hz : IsFundamentalClass F.Carrier E.Carrier (J.relative F E.Carrier)
      (NormalizedTwoCocycle.cohomologyClass z)) :
    ∃ κ : localWeilGroup F →ₜ* z.Extension,
      (∀ (g : localWeilGroup F) (x : E.Carrier),
        extensionFieldEmbedding F E f (NormalizedTwoCocycle.Extension.projection z (κ g) x) =
          AlgEquiv.toAlgHom (localProjection F g) (extensionFieldEmbedding F E f x)) ∧
      ∀ y : localWeilGroup E,
        κ (extensionWeilMap F E f y) =
          (NormalizedTwoCocycle.Extension.inl z (reciprocityUnits E e y))⁻¹ := by
  subst hinst
  subst hτ
  exact ⟨weilClassMap F E f hW hgal J hJ hA e he z hz,
    weilClassMap_projection_apply F E f hW hgal J hJ hA e he z hz,
    weilClassMap_extensionWeilMap F E f hW hgal J hJ hA e he z hz⟩

end Langlands.Weil.Local.FiniteGaloisTower

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

/-- The completion topology of `E_w` is the canonical topology of its `p`-adic package over the
residue prime of `v`. -/
theorem towerPadicField_topology_eq {F E : Type u} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E]
    (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
    [w.asIdeal.LiesOver v.asIdeal] :
    (inferInstance : TopologicalSpace (w.adicCompletion E)) =
      (towerPadicField v w).canonicalTopologicalData.topology := by
  have key : ∀ {q : ℕ} [Fact q.Prime] (h : residuePrime w = q),
      (inferInstance : TopologicalSpace (w.adicCompletion E)) =
        (padicFieldAt w h).canonicalTopologicalData.topology := by
    intro q _ h
    subst h
    exact completion_topology_eq w
  exact key (residuePrime_eq v w)

/-- **Reduction of the local Weil class map to Weil reciprocity existence.** -/
theorem localWeilClassMapExistence_of_weilReciprocity
    (hW : LocalClassField.WeilReciprocityExistenceUniqueness.{u}) :
    LocalWeilClassMapExistenceStatement.{u} := by
  intro F E _ _ _ _ _ v w _ _ J hJ hA e he a ha
  have hfd : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
    FiniteExtension.local_finite
      (show IsDedekindDomain.HeightOneSpectrum (𝓞 F) from v)
      (show IsDedekindDomain.HeightOneSpectrum (𝓞 E) from w)
  exact Weil.Local.FiniteGaloisTower.exists_weilClassMap hW (padicField v) (towerPadicField v w)
    (RelativeWeilGroup.completionPadicAlgHom v w)
    (inst := inferInstanceAs (Algebra (v.adicCompletion F) (w.adicCompletion E)))
    (Algebra.algebra_ext _ _ fun _ => rfl) (hfd := hfd)
    (τ := inferInstanceAs (TopologicalSpace (w.adicCompletion E)))
    (towerPadicField_topology_eq v w) J hJ hA e he (CompletionClassExtension.representative v w a)
    (by
      rw [show NormalizedTwoCocycle.cohomologyClass (CompletionClassExtension.representative v w a) =
        a from CompletionClassExtension.cohomologyClass_representative v w a]
      exact ha)

/-- **Local Weil class maps at completions.** The actual local Weil group of `F_v` maps
continuously into the completed-local class extension at every local fundamental class,
compatibly with the Galois projection and with inverse reciprocity on the Weil group of
`E_w`. -/
theorem localWeilClassMapExistence : LocalWeilClassMapExistenceStatement.{u} :=
  localWeilClassMapExistence_of_weilReciprocity
    LocalClassField.geometricWeilReciprocityExistenceUniqueness

end Langlands.ClassField.Global
