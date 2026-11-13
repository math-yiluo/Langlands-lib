# The sheafified Čech complex indexed by all tuples

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`.

## Purpose

The Library has two Čech models.

- The ordered complex `Langlands.Cohomology.Cech.complex` of abelian presheaves.
  Its `p`-cochains are indexed by *all* maps `σ : Fin (p + 1) → ι`, and it comes
  with pullbacks along arbitrary index maps and with cup products.
- The sheafified alternating complex `CechResolution.cechComplex`. It is
  indexed by strictly increasing tuples and is connected to actual cohomology
  by `CechResolution.cechCohomologyIso`.

This module builds the sheafified version of the first model. Its terms are
sheaves on `X`. The augmentation is a quasi-isomorphism, so the complex is a
right resolution of `M`. Later modules use it to compare the ordered model
with actual cohomology.

## Definitions

Throughout, `X : Scheme`, `ι : Type u`, `U : ι → X.Opens`, and `M : X.Modules`.
`ι` is required to be a `Fintype` wherever biproducts occur.

- `inter U σ : X.Opens` is `Langlands.Cohomology.Cech.inter U σ = ⨅ a, U (σ a)`,
  regarded as an open of the scheme. `inter_le_comp` and `inter_le_apply` are
  the corresponding containments.
- `term U M p` is the finite biproduct
  `⨁ (σ : Fin (p + 1) → ι), sheafOn M (inter U σ)`. Here `sheafOn M W` is the
  Library's pushforward of `M|_W` along `W ⟶ X`; its sections over `V` are
  `M(W ⊓ V)`.
- `d U M p : term U M p ⟶ term U M (p + 1)` is the ordered Čech differential.
  Its component at `τ : Fin (p + 2) → ι` is
  `∑ j, (-1)^j • (π_{τ ∘ j.succAbove} ≫ res)` (`d_π`).
- `complex U M : CochainComplex X.Modules ℕ` is built from these terms and
  differentials.
- `augmentation U M : M ⟶ term U M 0` collects the restriction units
  `M ⟶ sheafOn M (U i)` (`augmentation_π`). `aug U M : M[0] ⟶ complex U M`
  is the augmentation as a map of complexes.
- `augSc` and `sc n` are the short complexes `M ⟶ C⁰ ⟶ C¹` and
  `Cⁿ ⟶ Cⁿ⁺¹ ⟶ Cⁿ⁺²`.

## Main results

- `d_comp_d`: `d U M p ≫ d U M (p + 1) = 0`. The proof pairs the terms
  `(a, b)` with `a ≤ b` and `(b + 1, a)`, by the simplicial identity
  `succAbove_comp_succAbove`. It copies the Library proof of
  `CechResolution.cechD_comp_cechD`, with faces of strictly increasing tuples
  replaced by `τ ∘ j.succAbove`.
- `augmentation_d`: `augmentation U M ≫ d U M 0 = 0`.
- `quasiIso_aug_of_exact`: `aug U M` is a quasi-isomorphism if the augmentation
  is a monomorphism and the augmented complex is exact in every degree.
- `quasiIso_aug U M hU`: if `hU : ⨆ i, U i = ⊤`, then `aug U M` is a
  quasi-isomorphism. Affineness is not used. Neither is quasi-coherence of `M`.

## Proof of exactness

Exactness is local. Over an open `W ≤ U k`, sections of `term U M p` are
families `Sec U M p W`, given by `σ ↦ c σ ∈ M(inter U σ ⊓ W)` (`toSec` is
bijective, `toSec_d`). On such families the differential is `dSec`. The
contracting homotopy is

`(contr k hW c) σ = c (Fin.cons k σ)|`,

which prepends `k`. This uses `inter U (Fin.cons k σ) = U k ⊓ inter U σ`
(`inter_cons`).

- `cocycle_cons`: for a cocycle `c`, evaluate the cocycle condition at
  `Fin.cons k τ` and split off the face `j = 0` (`cons_comp_succAbove_zero`).
  The remaining faces are `Fin.cons k (τ ∘ j.succAbove)`
  (`cons_comp_succAbove_succ`). This gives
  `c τ = ∑ j, (-1)^j • c (Fin.cons k (τ ∘ j.succAbove))|`.
- `dSec_contr`: hence `dSec (contr k hW c) = c` for every cocycle in positive
  degree.
- `aug0_cr_const`: in degree zero, a cocycle `c` is the restriction of its
  component at the constant tuple `k`.

From these, `d_locally_exact` and `augmentation_locally_exact` give local
preimages. The Library criterion `exact_of_locally` turns local preimages into
exactness of `sc n` and `augSc`. `mono_augmentation` follows from the sheaf
property of `M` on the cover `U i ⊓ V`.

## Provenance

This is internal infrastructure. The complex and its exactness are The Stacks
Project, Cohomology of Sheaves, Section "Alternative view of the Čech complex"
(tag 02FR), Lemma 02FU (`lemma-covering-resolution`). See `cohomology.tex`,
lines 4565–4640, of the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`. There the terms are
`∏_{i₀…i_p} (j_{i₀…i_p})_* F|_{U_{i₀…i_p}}` over all tuples, and the
homotopy is `h(s)_{i₀…i_{p-1}} = s_{i_fix i₀…i_{p-1}}`. Stacks checks
exactness on stalks; here the same homotopy is used on sections over opens
`W ≤ U k`. The module follows the Library's alternating construction in
`CechResolution.Complex` and `CechResolution.Exact`. It reuses that
development's `sheafOn`, `res`, `unit`, `biproduct_ext_app`,
`biproduct_exists_app`, `exact_of_locally`, and `succAbove_comp_succAbove`.
