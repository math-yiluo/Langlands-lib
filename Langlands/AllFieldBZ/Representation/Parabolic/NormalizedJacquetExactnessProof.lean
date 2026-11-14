import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.AllFieldBZ.Representation.Parabolic.NormalizedJacquetStatement
import Langlands.AllFieldBZ.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof

/-!
# All-field port of `Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedJacquetExactnessClause ParabolicQuotientCompactClause UnipotentFiniteContainmentClause isSmooth_radical normalizedJacquetExactness radicalCoinvariants_exact unipotentFiniteContainment
universe uF uU uV uW

open Representation
variable (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

section Radical
variable {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- A smooth ambient action stays smooth on the actual block radical. -/
theorem isSmooth_radical (σ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    IsSmooth σ →
      IsSmooth ((σ.comp (B.parabolic F.Carrier).subtype).comp
        (B.unipotentRadical F.Carrier).subtype) := by
  let := T.topology
  intro hσ
  exact isSmooth_comp _ continuous_subtype_val
    (isSmooth_comp _ continuous_subtype_val hσ)

/-- Exactness of the unnormalized radical quotient maps, stated on Mathlib's
coinvariant maps for the actual block unipotent radical. Only the middle term
needs to be smooth. -/
theorem radicalCoinvariants_exact
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) U}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) :
    letI := T.topology
    IsSmooth σ → Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    Function.Injective (Coinvariants.map _ _
        (Jacquet.restrictMap (Jacquet.restrictMap i (B.parabolic F.Carrier))
          (B.unipotentRadical F.Carrier))) ∧
      LinearMap.range (Coinvariants.map _ _
          (Jacquet.restrictMap (Jacquet.restrictMap i (B.parabolic F.Carrier))
            (B.unipotentRadical F.Carrier))) =
        LinearMap.ker (Coinvariants.map _ _
          (Jacquet.restrictMap (Jacquet.restrictMap q (B.parabolic F.Carrier))
            (B.unipotentRadical F.Carrier))) ∧
      Function.Surjective (Coinvariants.map _ _
        (Jacquet.restrictMap (Jacquet.restrictMap q (B.parabolic F.Carrier))
          (B.unipotentRadical F.Carrier))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hσ hi hq hex
  exact ⟨coinvariants_map_injective_of_smooth (unipotentFiniteContainment F T B)
      _ hi (isSmooth_radical F T B σ hσ),
    coinvariants_map_range_eq_ker _ _ hq hex,
    coinvariants_map_surjective _ hq⟩

end Radical
/-- The actual normalized block Jacquet maps are exact on short exact
sequences of smooth complex representations. -/
theorem normalizedJacquetExactness (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    NormalizedJacquetExactnessClause F T B U V W := by
  intro ρ σ τ i q _ hσ _ hi hq hex iN qN
  exact radicalCoinvariants_exact F T B i q hσ hi hq hex

end Langlands.AllFieldBZ.Parabolic
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uU uV uW

open Representation
variable {F : LocalFieldPackage.{uF}}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Both are Mathlib's coinvariant map for the actual block unipotent radical. -/
theorem normalizedJacquetMap_toLinearMap_eq_coinvariantsMap
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedJacquetMap B f).toLinearMap =
      Coinvariants.map _ _ (Jacquet.restrictMap
        (Jacquet.restrictMap f (B.parabolic F.Carrier)) (B.unipotentRadical F.Carrier)) :=
  rfl

/-- Exactness of the actual normalized Jacquet maps, obtained from
`Parabolic.normalizedJacquetExactness`. The outer terms are smooth because they
are a subrepresentation and a quotient of the smooth middle term. -/
theorem normalizedJacquetMap_exact
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) U}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) :
    letI := T.topology
    IsSmooth σ → Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    Function.Injective (T.normalizedJacquetMap B i) ∧
      LinearMap.range (T.normalizedJacquetMap B i).toLinearMap =
        LinearMap.ker (T.normalizedJacquetMap B q).toLinearMap ∧
      Function.Surjective (T.normalizedJacquetMap B q) := by
  let := T.topology
  intro hσ hi hq hex
  exact Parabolic.normalizedJacquetExactness F T B U V W ρ σ τ i q
    (isSmooth_of_injective i hi hσ) hσ (isSmooth_of_surjective q hq hσ) hi hq hex

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
