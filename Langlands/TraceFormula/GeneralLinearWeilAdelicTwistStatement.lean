import Langlands.TraceFormula.AdelicGroupAutomorphism
import Langlands.Global.AdelicGaloisTwistMap
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicGLTransport
import Langlands.GroupScheme.Reductive.GeneralLinear
/-!
# The adelic points of `Res_{L/K} GL_n` as `GL_n(𝔸_L)`: Galois twist and rational points

Let `L/K` be a finite extension of number fields and `W = Res_{L/K} GL_n` the Library's Weil
restriction of the base change of `GL_n` (`weilGroup K L GLₙ`). The simple twisted trace
formula for `W` (`GeneralLinearSimpleTwistedTraceFormulaStatement`) and its per-class facts
(`GeneralLinearTwistedEllipticCentralizerStatement`) identify `W(𝔸_K)` with `GL_n(𝔸_L)` through
the composite map `Φ` of

* the Library's identification `weilAdelicEquiv` of `W(𝔸_K)` with the adelic points over `L`
  of the base change of `GL_n` to `L`,
* the base-change isomorphism of `GL_n` group schemes, and
* the Library's identification `adelicHomeomorph` of the adelic points of the `GL_n` group
  scheme over `L` with the matrix group `GL_n(𝔸_L)`.

This file states the three compatibilities of `Φ` with the structures used on the
`GL_n(𝔸_L)` side, for example by `TwistedEllipticClassFinitenessStatement`:

* `Φ` is a topological group isomorphism;
* for every `σ ∈ Aut(L/K)`, `Φ` carries the automorphism of `W(𝔸_K)` induced by the algebraic
  automorphism `unitGaloisAut σ` of `W` to the entrywise action of `σ` on `GL_n(𝔸_L)`
  (`AdelicGLTransport.adelicEquiv n σ`);
* `Φ` carries the rational subgroup `W(K)` of `W(𝔸_K)` onto the image of `GL_n(L)`.

See `GeneralLinearWeilAdelicTwistStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance generalLinearWeilAdelicTwistIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearWeilAdelicTwistSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

/-- The identification `Φ : W(𝔸_K) → GL_n(𝔸_L)` for `W = Res_{L/K} GL_n`, built from the
Library maps `weilAdelicEquiv`, the base-change isomorphism of `GL_n` and `adelicHomeomorph`,
has the following three properties, for every finite extension `L/K` of number fields and
every `n`:

* `Φ` is the underlying function of a topological group isomorphism
  `W(𝔸_K) ≃ₜ* GL_n(𝔸_L)`;
* for every `σ ∈ Aut(L/K)` and every `g ∈ W(𝔸_K)`, the image under `Φ` of the automorphism
  `adelicAut K (unitGaloisAut K L GLₙ σ)` applied to `g` is the matrix obtained from `Φ(g)` by
  applying to every entry the action of `σ` on `𝔸_L`
  (`Langlands.Global.AdelicGLTransport.adelicEquiv n σ`);
* `g ∈ W(𝔸_K)` lies in the rational subgroup `W(K)` exactly when `Φ(g)` lies in the image of
  `GL_n(L)` under the diagonal embedding `AdelicGL.rational L n`. -/
def GeneralLinearWeilAdelicTwistStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ),
    let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
    (∃ e : AdelicGroupPoints K Wₙ ≃ₜ* AdelicGL L n, ⇑e = Φ) ∧
    (∀ (σ : L ≃ₐ[K] L) (g : AdelicGroupPoints K Wₙ),
      Φ (adelicAut K (unitGaloisAut K L GLₙ σ) g) =
        Langlands.Global.AdelicGLTransport.adelicEquiv n (σ : L ≃+* L) (Φ g)) ∧
    ∀ g : AdelicGroupPoints K Wₙ,
      g ∈ AdelicGroupPoints.rationalSubgroup K Wₙ ↔ Φ g ∈ (AdelicGL.rational L n).range

end Langlands.TraceFormula
