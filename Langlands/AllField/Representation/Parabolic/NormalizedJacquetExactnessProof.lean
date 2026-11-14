import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Representation.Geometric.RefinementDefinitionsSupplement
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement
import Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment
/-!
# Exactness of the actual normalized block Jacquet maps

The radical quotient is Mathlib's coinvariant quotient for the actual block
unipotent radical, and the normalizing twist and Levi action leave the
underlying linear maps unchanged.  Exactness therefore reduces to the generic
smooth coinvariant exactness of `Langlands.Representation.Jacquet.ExactProof`,
whose finite-containment hypothesis is the published
`unipotentFiniteContainment` for the actual radical.
-/

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedJacquetExactnessClause isSmooth_radical normalizedJacquetExactness radicalCoinvariants_exact unipotentFiniteContainment
open Langlands.AllField.Parabolic

universe uF uU uV uW

open _root_.Representation

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)

section Radical

variable {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- A smooth ambient action stays smooth on the actual block radical. -/
theorem isSmooth_radical (σ : Representation ℂ (GeneralLinear n F) V) :
    letI := T.topology
    IsSmooth σ →
      IsSmooth ((σ.comp (B.parabolic F).subtype).comp
        (B.unipotentRadical F).subtype) := by
  let := T.topology
  intro hσ
  exact isSmooth_comp _ continuous_subtype_val
    (isSmooth_comp _ continuous_subtype_val hσ)

/-- Exactness of the unnormalized radical quotient maps, stated on Mathlib's
coinvariant maps for the actual block unipotent radical. Only the middle term
needs to be smooth. -/
theorem radicalCoinvariants_exact
    {ρ : Representation ℂ (GeneralLinear n F) U}
    {σ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) :
    letI := T.topology
    IsSmooth σ → Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    Function.Injective (Coinvariants.map _ _
        (Jacquet.restrictMap (Jacquet.restrictMap i (B.parabolic F))
          (B.unipotentRadical F))) ∧
      LinearMap.range (Coinvariants.map _ _
          (Jacquet.restrictMap (Jacquet.restrictMap i (B.parabolic F))
            (B.unipotentRadical F))) =
        LinearMap.ker (Coinvariants.map _ _
          (Jacquet.restrictMap (Jacquet.restrictMap q (B.parabolic F))
            (B.unipotentRadical F))) ∧
      Function.Surjective (Coinvariants.map _ _
        (Jacquet.restrictMap (Jacquet.restrictMap q (B.parabolic F))
          (B.unipotentRadical F))) := by
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

end Langlands.AllField.Parabolic

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uU uV uW

open _root_.Representation

variable {F : Type uF} [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Both are Mathlib's coinvariant map for the actual block unipotent radical. -/
theorem normalizedJacquetMap_toLinearMap_eq_coinvariantsMap
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedJacquetMap B f).toLinearMap =
      Coinvariants.map _ _ (Jacquet.restrictMap
        (Jacquet.restrictMap f (B.parabolic F)) (B.unipotentRadical F)) :=
  rfl

/-- Exactness of the actual normalized Jacquet maps, obtained from
`Langlands.AllField.Parabolic.normalizedJacquetExactness`. The outer terms are smooth because they
are a subrepresentation and a quotient of the smooth middle term. -/
theorem normalizedJacquetMap_exact
    {ρ : Representation ℂ (GeneralLinear n F) U}
    {σ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W}
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
  exact Langlands.AllField.Parabolic.normalizedJacquetExactness F T B U V W ρ σ τ i q
    (isSmooth_of_injective i hi hσ) hσ (isSmooth_of_surjective q hq hσ) hi hq hex

end Langlands.LocalFieldData
