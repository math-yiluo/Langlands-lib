import Langlands.GroupScheme.Rational.EvenChainGaloisAssembly
import Langlands.GroupScheme.Rational.MergedRootGaloisData

/-! # Galois-stable even-path pattern data for pairing-compatible pinnings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

namespace PairingCompatiblePinningData

open LinearAlgebra.RootDatumPairedPaths

variable (D : PairingCompatiblePinningData k K G)

/-- Over a finite extension, the pairs of a pairing-compatible pinning carry Galois-compatible
merged-root data. -/
theorem nonempty_mergedGaloisData [FiniteDimensional k K] : Nonempty D.MergedGaloisData := by
  obtain ⟨M, hM, hmem, hx, hn, hco⟩ :=
    D.toGaloisCompatiblePinningData.exists_mergedRootGaloisData (J := D.Pairs)
      (fun c => c.1) (fun c => partner D.action c.1)
      (fun c => ⟨(c.2.1.partner_ne).symm, c.2.1.pairing_partner D.isPairingCompatible⟩)
      (fun σ c => D.smul_orientation σ c)
  exact ⟨{ data := M
           a_eq := fun c => (hM c).1
           b_eq := fun c => (hM c).2.1
           ca_eq := fun c => (hM c).2.2.1
           cb_eq := fun c => (hM c).2.2.2
           nAlpha_mem := hmem
           xAlpha_conj := hx
           nAlpha_conj := hn
           coroot_conj := hco }⟩

end PairingCompatiblePinningData

end Galois

/-- **Steinberg, Regular elements of semi-simple algebraic groups (1965), 9.3, 9.4 and the
proof of 9.7 e).** For pairing-compatible pinning data over a
finite Galois extension there are even-path data, ordered middle-out, whose set of pattern
products is stable under the Galois action on rational points of the base change. -/
theorem evenChainGaloisData : EvenChainGaloisDataStatement.{u} := by
  intro k K _ _ _ _ _ G _ D
  exact D.nonempty_mergedGaloisData.some.exists_evenChainGaloisData

end Langlands.GroupScheme
