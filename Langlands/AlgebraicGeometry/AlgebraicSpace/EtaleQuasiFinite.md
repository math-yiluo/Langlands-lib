# Étale morphisms of schemes are locally quasi-finite

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite`, namespace
`Langlands.AlgebraicGeometry`.

- `locallyQuasiFinite_of_etale f`: for an étale morphism of schemes `f : X ⟶ Y`
  (Mathlib's `Etale`), `f` is locally quasi-finite (Mathlib's `LocallyQuasiFinite`).

This module contains the existing declaration previously in
`Langlands.AbelianScheme.TorsionFiniteEtale`, with its original name, statement and proof.
The relocated proof is due to Worker 268; the torsion module imports it here.
On affine opens, the ring map `f.appLE U V e` is étale.
With its induced algebra structure, Mathlib's instance from
`Mathlib.RingTheory.Unramified.LocalStructure` gives `Algebra.QuasiFinite`.
`HasRingHomProperty.iff_appLE` then proves local quasi-finiteness.

Provenance: internal helper. It is the standard fact that étale (indeed unramified) morphisms
are locally quasi-finite. Only Mathlib results are combined; no
source proof is transcribed. Consequence used later: fibres of étale morphisms are discrete
(Mathlib's `Scheme.Hom.isDiscrete_preimage_singleton`).
