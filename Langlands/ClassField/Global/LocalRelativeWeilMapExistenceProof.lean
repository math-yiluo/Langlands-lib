import Langlands.ClassField.Global.LocalRelativeWeilMapStatement
import Langlands.ClassField.Global.LocalRelativeWeilMapReduction
import Langlands.ClassField.Global.LocalWeilClassMapStatement
import Langlands.ClassField.Global.LocalWeilClassMapProof
import Langlands.ClassFieldTheory.Local.FundamentalConsequencesProof

/-! # Existence of local-to-relative Weil maps at finite places -/

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

/-- **Reduction to local Weil class maps.** A local Weil class map into the completed local
class extension at a local fundamental class, pushed into the relative global Weil group, is a
local-to-relative Weil map. -/
theorem localRelativeWeilMapExistence_of_localWeilClassMapExistence
    (hK : LocalWeilClassMapExistenceStatement.{u}) :
    LocalRelativeWeilMapExistenceStatement.{u} := by
  intro I hI c hc F E _ _ _ _ _ _ v w _ e he
  have : IsGalois (padicField v).Carrier (w.adicCompletion E) :=
    isGalois_adicCompletion v w
  have : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
    FiniteExtension.local_finite
      (show IsDedekindDomain.HeightOneSpectrum (𝓞 F) from v)
      (show IsDedekindDomain.HeightOneSpectrum (𝓞 E) from w)
  obtain ⟨a, ha, -⟩ := ((I (residuePrime v)).fundamentalClasses_of_relativeImages
    (hI (residuePrime v)).1.2.1 (padicField v) (w.adicCompletion E)).1
  obtain ⟨κ, hP, hR⟩ :=
    hK F E v w (I (residuePrime v)) (hI _).1 (hI _).2 e he a ha
  -- `κ` is continuous for the Krull topology on `Gal(E_w/F_v)`; the helper uses the
  -- discrete topology `completionGaloisTopology`, which is the same topology.
  obtain ⟨f, hfκ, hf⟩ : ∃ f : Weil.Local.localWeilGroup (padicField v) →*
      CompletionClassExtension v w a, (∀ g, f g = κ g) ∧ Continuous f :=
    ⟨κ.toMonoidHom, fun _ => rfl, κ.continuous_toFun⟩
  rw [show krullTopology (v.adicCompletion F) (w.adicCompletion E) =
    completionGaloisTopology v w from DiscreteTopology.eq_bot] at hf
  let κ' : (letI := completionGaloisTopology v w
      Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a) :=
    letI := completionGaloisTopology v w
    { toMonoidHom := f
      continuous_toFun := hf }
  have hκ' : ∀ g, κ' g = κ g := hfκ
  exact ⟨RelativeWeilGroup.localWeilToRelative c v w I hc.2.2.2 a ha κ',
    RelativeWeilGroup.isLocalRelativeWeilMap_localWeilToRelative c v w I hc.2.2.2 a ha e he κ'
      (fun g x => by rw [hκ']; exact hP g x) (fun y => by rw [hκ']; exact hR y)⟩

/-- **Local-to-relative Weil maps.** For every local family satisfying the local class
formation laws, every compatible global class family, every finite place `w ∣ v` and every
geometrically normalized reciprocity candidate `e` of `E_w`, the actual local Weil group of
`F_v` maps continuously into the relative Weil group of `E/F`, compatibly with the Galois
projections, and on `W_{E_w}` the map is the inverse of `e` followed by `E_wˣ → C_E`. -/
theorem localRelativeWeilMapExistence : LocalRelativeWeilMapExistenceStatement.{u} :=
  localRelativeWeilMapExistence_of_localWeilClassMapExistence localWeilClassMapExistence

end Langlands.ClassField.Global
