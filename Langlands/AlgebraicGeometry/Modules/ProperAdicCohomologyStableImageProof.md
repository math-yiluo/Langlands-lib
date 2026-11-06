# Stable images of actual proper adic cohomology

`properAdicCohomologyStableImage` proves the complete proposition
`ProperAdicCohomologyStableImageStatement` (Stacks Project Lemma 30.20.4(3),
tag [02OB](https://stacks.math.columbia.edu/tag/02OB)).

Fix a noetherian ring `R`, an ideal `I`, a proper morphism
`f : X ⟶ Spec R`, a quasi-coherent module `M` with finite sections over
every affine open, and a degree `p`.

The proof first chooses a finite ordered affine cover `𝒰`. Properness makes
`X` quasi-compact (`QuasiCompact.compactSpace_of_compactSpace`), and `𝒰` is
`Scheme.OrderedAffineCover.ofCompactSpace X`.

`ProperAdicArtinRees.exists_uniform_cechBoundaryLift` then gives one integer
`c` such that `CechBoundaryLift f M 𝒰 (I^k) (I^n) p` holds whenever
`n + c ≤ k`. Every alternating degree-`p` Čech cochain of `M` whose boundary
lies in `I^k` times cochains has another cochain in `I^n` times cochains with
the same boundary. This is a Čech-level form of the Artin–Rees statement in
Stacks Lemma 30.20.3, obtained from finiteness of the Čech cohomology of a
Rees presheaf on `X ×_R Spec(⊕ Iᵐ)`. The helper module's Markdown gives the
details.

Finally the published `IdealAdic.adic_stable_image_of_cech_boundary_lift`
turns this bound into the conclusion with the same `c`. For all `n` and `k`
with `n + c ≤ k`, the range of the degree-`p` map induced by
`adicTransition f I M` equals the range of the map induced by
`adicProjection f I M n`. That published reduction derives the containment
of kernels
`ker H^(p+1)(I^k M → M) ⊆ ker H^(p+1)(I^k M → I^n M)` from the boundary
lifts, through Čech naturality. It then performs the long-exact-sequence
chase from the proof of Lemma 30.20.4(3). This is the form corrected by
comment 11745, which refers to Lemma 30.20.3(3).

No local-ring, completeness, flatness or projectivity hypothesis is used.
