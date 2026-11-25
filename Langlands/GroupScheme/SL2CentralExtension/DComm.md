# Lifts of diagonal matrices commute when the kernel is separated

Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1). This proves the commutativity of Conrad's `D′`, the preimage of
the diagonal torus, in the form of the hypothesis `X.DComm` used in `Torus` and `Cell`. It is
the only step of the existence proof that uses the separatedness of the kernel. It uses the
module `Langlands.GroupScheme.SL2CentralExtension.UnitPairing`.

Throughout, `X : Ext S` is the point-level data from `Setup`.

## Contents

- `Q_comm_h`: `Q (comm (h s) (h t)) = 1`, since diagonal matrices commute.
- `comm_h_mul_left`, `comm_h_mul_right`: `(s, t) ↦ comm (h s) (h t)` is multiplicative in each
  variable. The lifts `hl s` of `h s` from `Torus` are global, so `comm (h s) (h t)` is the
  commutator of `hl s` and `hl t` (`comm_eq`). Then `commutator_mul_left` and
  `commutator_mul_right` from `Setup` apply, because commutators of lifts of commuting matrices
  are central.
- `comm_h_res`: restriction along `k` replaces `s`, `t` by `umap k s`, `umap k t`.
- Let `Z` be a commutative group scheme over `S` and `i : Z.toGrp ⟶ X.E` a homomorphism. Let
  `hi` say that every point `e` of `E` with `Q e = 1` factors as `c ≫ i.hom.hom`. Then
  `hPair i hi s t : T ⟶ Z.X` is a chosen factorization of `comm (h s) (h t)` (`hPair_spec`).
  If `i.hom.hom` is a monomorphism, `hPair` is bimultiplicative (`hPair_mul_left`,
  `hPair_mul_right`) and natural (`hPair_res`), by cancellation of `i.hom.hom`. Hence
  `hUnitPairing i hi : UnitPairing Z` is a natural pairing of units in the sense of
  `UnitPairing`.
- `dComm_of_separated`: with `hi` as above, if `i.hom.hom` is a monomorphism (`hm`) and `Z` is
  separated over `S`, then `X.DComm`. By `UnitPairing.eq_one`, every natural
  pairing of units into a separated commutative group scheme is trivial. So `hPair i hi s t = 1`,
  and `comm (h s) (h t) = 1 ≫ i.hom.hom = 1`.

`UnitPairing.eq_one` first shows that the pairing is trivial when one input has finite order.
It does so by adjoining a root of the other input fppf-locally. It then applies
`units_natural_ext` (module `TorsionDensity`). That result says two natural families of maps
from units into a separated scheme are equal if they agree on units of finite order. Its proof
is a relative schematic density argument on `Spec Γ[X, X⁻¹]`. This replaces the schematic density
of the open cell in Conrad's argument for `D′`.
