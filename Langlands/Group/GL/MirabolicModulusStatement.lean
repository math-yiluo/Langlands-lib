import Langlands.Group.HaarModulus
import Langlands.Group.GL.MirabolicRadical
import Langlands.Group.GL.NormalizedCharacter

/-!
# The Haar modulus of the actual mirabolic radical

Bernstein--Zelevinsky define `mod_U(m)` by the scaling of a Haar measure of `U`
under `u ↦ m u m⁻¹`. This proposition states that, on the actual last-column
radical of the mirabolic group, the published Haar character
`HaarModulus.closedRestrictCharacter` of the standard Levi subgroup and of the
embedded smaller mirabolic subgroup is the residue-normalized determinant norm.
It is a proposition definition, not a proof.
-/

namespace Langlands

universe uF

open GeneralLinear.Mirabolic in
/-- For the supplied realization `T` and every `n`, pulling the actual closed-radical
Haar character back along the Levi equivalence `GL_n ≃ diag(GL_n, 1) ≤ P_(n+1)` gives
`T.determinantNorm n`, and pulling it back along the successor equivalence
`P_(n+1) ≃ diag(P_(n+1), 1) ≤ P_(n+2)` gives `T.determinantNorm (n+1)` restricted to
`P_(n+1)`. -/
def MirabolicRadicalHaarModulusStatement {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  haveI := T.fieldT2
  ∀ n : ℕ,
    haveI := T.generalLinearTopologicalGroup (n + 1)
    haveI := T.generalLinearLocallyCompactSpace (n + 1)
    haveI := locallyCompactSpace (n := n) (F := F.Carrier)
    haveI := T.generalLinearTopologicalGroup (n + 1 + 1)
    haveI := T.generalLinearLocallyCompactSpace (n + 1 + 1)
    haveI := locallyCompactSpace (n := n + 1) (F := F.Carrier)
    (HaarModulus.closedRestrictCharacter (radical n F.Carrier) radical_isClosed
        (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer).comp
        (leviEquiv (n := n) (F := F.Carrier)).toMonoidHom =
      T.determinantNorm n ∧
    (HaarModulus.closedRestrictCharacter (radical (n + 1) F.Carrier) radical_isClosed
        (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer).comp
        (successorEquiv (n := n) (F := F.Carrier)).toMonoidHom =
      (T.determinantNorm (n + 1)).comp (GeneralLinear.mirabolic n F.Carrier).subtype

end Langlands
