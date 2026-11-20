import Langlands.Global.RankinSelberg.EqualAnalyticResidue
import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.CuspidalSpectralPresentation

/-!
# The residue pairing of two cusp forms detects the contragredient

The residue clause of Cogdell (2004), Theorem 2.2 (printed pp.210–211), for cuspidal
realizations `T`, `T'` of `GL_(r+1)` with central characters `ω`, `ω'`.
The residues of the global integral `I(s; φ, φ', Φ)` at `s = 0` and `s = 1` are multiples of
the slab pairing `C(φ, φ') = ∫_(D ∩ S) φ(g) φ'(g) dg` (`residueConstant` at `w = 0`), where
`D` is the Library fundamental domain of `GL_(r+1)(F)` in `GL_(r+1)(𝔸)` and `S` the slab
`1 ≤ |det g| < e^(r+1)`. The statement: if `ω ω' = 1` and `C(φ, φ') ≠ 0` for some vectors,
then `T` realizes the contragredient of `T'`; conversely, if `T` realizes the contragredient
of `T'`, then `ω ω' = 1` and for
every finite set `S` of finite places containing the exceptional sets of spectral
presentations of `T` and `T'` there are vectors fixed by `GL_(r+1)(𝒪_v)` at every finite
`v ∉ S` with `C(φ, φ') ≠ 0`. See the paired Markdown for sources and conventions.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

/-- The slab pairing `C(φ, φ') = ∫_(D ∩ S) φ(g) φ'(g) dg` of two cusp forms of `GL_(r+1)`:
the constant `residueConstant` at `w = 0` of the product of their functions. -/
def slabPairing {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (T T' : CuspidalOperatorRealization F r) (x : T.Space) (x' : T'.Space) : ℂ :=
  EqualAnalytic.residueConstant F r (fun g => cuspFunction F T x g * cuspFunction F T' x' g) 0

/-- **Cogdell (2004), Theorem 2.2, residue clause** (printed pp.210–211), at `ω ω' = 1`.

Let `T`, `T'` be actual cuspidal realizations of `GL_(r+1)` over a number field with central
characters `ω`, `ω'`. If `ω ω' = 1` and the slab pairing `C(φ, φ')` is nonzero for some
vectors, then `T` realizes the contragredient of `T'`. Conversely, if `T` realizes the
contragredient of `T'`, then `ω ω' = 1`, and for all spectral presentations `P`, `P'` of `T`,
`T'` and every finite set `S` of finite places containing both exceptional sets there are
vectors `x`, `x'` fixed by `GL_(r+1)(𝒪_v)` at every finite place `v ∉ S` with
`C(φ_x, φ'_x') ≠ 0`. -/
def CuspidalSlabPairingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : CuspidalOperatorRealization F r) (ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ),
    T.realization.HasCentralCharacter ω → T'.realization.HasCentralCharacter ω' →
    (ω * ω' = 1 → (∃ (x : T.Space) (x' : T'.Space), slabPairing T T' x x' ≠ 0) →
        OperatorRealization.IsContragredientOf T.realization T'.realization) ∧
      (OperatorRealization.IsContragredientOf T.realization T'.realization →
        ω * ω' = 1 ∧
          ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
            (P' : CuspidalSpectralPresentation.{u, uQ} T') (S : Finset (FinitePlace F)),
            P.exceptional ⊆ S → P'.exceptional ⊆ S →
            ∃ (x : T.Space) (x' : T'.Space), IsSphericalOutside F T S x ∧
              IsSphericalOutside F T' S x' ∧ slabPairing T T' x x' ≠ 0)

end Langlands.Global.RankinSelbergGlobal
