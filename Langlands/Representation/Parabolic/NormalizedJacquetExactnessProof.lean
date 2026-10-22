import Langlands.Representation.Parabolic.NormalizedJacquetStatement
import Langlands.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Jacquet.Parabolic

/-!
# Exactness of the actual normalized block Jacquet maps

The radical quotient is Mathlib's coinvariant quotient for the actual block
unipotent radical, and the normalizing twist and Levi action leave the
underlying linear maps unchanged.  Exactness therefore reduces to the generic
smooth coinvariant exactness of `Langlands.Representation.Jacquet.ExactProof`,
whose finite-containment hypothesis is the published
`unipotentFiniteContainment` for the actual radical.
-/

namespace Langlands.Parabolic

universe uF uU uV uW

open Representation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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

end Langlands.Parabolic

namespace Langlands.PadicField.TopologicalData

universe uF uU uV uW

open Representation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- The actual normalized Jacquet map has the underlying linear map of the
normalized quotient intertwiner in `NormalizedJacquetExactnessClause`. -/
theorem normalizedJacquetMap_toLinearMap
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedJacquetMap B f).toLinearMap =
      (twistIntertwining (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (Parabolic.leviCoinvariantsMap B
          (Jacquet.restrictMap f (B.parabolic F.Carrier)))).toLinearMap :=
  rfl

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

/-- The functor's morphism map is the concrete normalized quotient map. -/
theorem normalizedJacquetFunctor_map_hom :
    letI := T.generalLinearTopology n
    letI := T.leviTopology B
    ∀ {A C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ C),
      SmoothRep.hom ((T.normalizedJacquetFunctor B).map f) =
        T.normalizedJacquetMap B (SmoothRep.hom f) := by
  intros
  rfl

/-- Exactness of the normalized Jacquet functor on a short exact sequence of
smooth representations, read on the underlying intertwiners. -/
theorem normalizedJacquetFunctor_map_exact :
    letI := T.generalLinearTopology n
    letI := T.leviTopology B
    ∀ {A₁ A₂ A₃ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
      (i : A₁ ⟶ A₂) (q : A₂ ⟶ A₃),
      Function.Injective (SmoothRep.hom i) → Function.Surjective (SmoothRep.hom q) →
      LinearMap.range (SmoothRep.hom i).toLinearMap =
        LinearMap.ker (SmoothRep.hom q).toLinearMap →
      Function.Injective (SmoothRep.hom ((T.normalizedJacquetFunctor B).map i)) ∧
        LinearMap.range (SmoothRep.hom ((T.normalizedJacquetFunctor B).map i)).toLinearMap =
          LinearMap.ker (SmoothRep.hom ((T.normalizedJacquetFunctor B).map q)).toLinearMap ∧
        Function.Surjective (SmoothRep.hom ((T.normalizedJacquetFunctor B).map q)) := by
  let := T.generalLinearTopology n
  intro A₁ A₂ A₃ i q hi hq hex
  exact T.normalizedJacquetMap_exact B (SmoothRep.hom i) (SmoothRep.hom q)
    A₂.isSmooth hi hq hex

end Langlands.PadicField.TopologicalData
