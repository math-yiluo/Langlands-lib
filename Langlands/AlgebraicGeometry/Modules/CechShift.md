# Dimension shifting for ordered Čech cochains of Čech-acyclic modules

Author: Worker 274.

This module compares ordered Čech cochains of an `𝒪_P`-module `M` with those of its injective
hull and of the cokernel, and derives two results by induction on the degree: refinement
injectivity of Čech cohomology in every positive degree, and Čech vanishing from vanishing of
derived global sections. It also proves degree-one refinement surjectivity for families of
affine opens. It is a helper for the proof of
`Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`. It contains no `sorry`
and no new axioms.

## Provenance

The method is the dimension-shifting argument of The Stacks Project, Cohomology of Schemes,
Lemma 01XD (`coherent-lemma-cech-cohomology-quasi-coherent`, registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`): embed `M` into an injective module `I`,
use that the Čech complexes of `I` are exact (injective modules are flasque, Stacks tags 09SX,
09SY) and that `Q = I / M` again has exact Čech complexes on affine opens, and induct on the
degree. Here the argument is run with the Library's ordered Čech cochains
(`Langlands.Cohomology.CechCochains`), the Library injective embedding
`0 ⟶ M ⟶ Injective.under M ⟶ cokernel (Injective.ι M) ⟶ 0`
(`PushforwardInjectiveAcyclic.injectiveSc`) and the Library predicate
`AffineVanishing.IsCechAcyclic M` (Čech complexes of standard covers of affine opens are exact).
The two results are consequences used by the proof; their exact form is a project choice.

`Cech.ExactAt P V p` is exactness of the Čech complex at cochain degree `p + 1`: every
`(p + 1)`-cocycle is the differential of a `p`-cochain.

## Definitions

All declarations are in namespace `Langlands.AlgebraicGeometry.Modules.CechShift`. Throughout,
`M : P.Modules` and `V : ι → P.Opens`.

- `mapι M V p` and `mapπ M V p` (abbreviations) are the maps of Čech `p`-cochains induced by
  `Injective.ι M : M ⟶ Injective.under M` and by `cokernel.π (Injective.ι M)`.

## Results

- `d_zero_res_top`: the restrictions of a global section form a `0`-cocycle.
- `exists_top_of_d_zero`: for a sheaf of abelian groups and a family `U` with `⊤ ≤ iSup U`, a
  `0`-cocycle is given by the restrictions of a global section.
- `mapπ_mapι`, `mapι_injective`, `exists_mapι_eq`: the sequence of cochain groups
  `0 → C(V, M) → C(V, I) → C(V, Q)` is exact.
- `exists_mapπ_eq`: if `M` is Čech-acyclic and all `inter V σ` with `σ : Fin (p + 1) → ι` are
  affine, every `p`-cochain of `Q` lifts to `I`.
- `exactAt_injective`: for finite `ι`, the ordered Čech complex of `Injective.under M` for `V` is
  exact in every positive degree.
- `exists_d_eq_of_shift`: if `M` is Čech-acyclic, the intersections of `p + 1` members of `V`
  are affine, `ι z = d t` for a `(p + 2)`-cochain `z` of `M`, and `π t = d r`, then `z` is a
  coboundary.
- `exists_d_eq_of_refine` (refinement injectivity): let `ι` and `κ` be finite, let all finite
  intersections `inter V σ` be affine, and let `W : κ → P.Opens` cover `P` and refine `V`
  through `β` (`hβ : ∀ j, W j ≤ V (β j)`). For every Čech-acyclic `M`, a `(p + 1)`-cocycle `z` of
  `M` on `V` whose refinement to `W` is a coboundary is a coboundary on `V`. The base case
  `p = 0` is `Cech.exists_d_eq_of_refine_eq_d`; the step applies the induction hypothesis to the
  cokernel `Q`.
- `exists_refine_sub_eq_d` (degree-one refinement surjectivity): let the members of `V` be
  affine and let a finite family `W` cover `P` and refine `V` through `β`. For a Čech-acyclic
  `M`, every `1`-cocycle `w` on `W` satisfies `refine w' - w = d g` for a `1`-cocycle `w'` on `V`
  and a `0`-cochain `g` on `W`. Proof: `ι w = d t`, the sections `π t` glue to `q ∈ Γ(P, Q)`,
  `q` lifts on `V` to `s` with `d s = ι w'`, and `refine s - t = ι g`.
- `exactAt_of_isZero` (derived vanishing implies Čech vanishing): let `f : P ⟶ Spec R`, `ι`
  finite, `V` covering `P` with all finite intersections affine. If `M` is Čech-acyclic and
  `(relativeCohomology f (p + 1)).obj M` is zero, then `Cech.ExactAt M.presheaf V p`. For
  `p = 0` the vanishing of `H¹(M)` makes `Γ(P, I) → Γ(P, Q)` surjective
  (`DerivedPlus.shortExact_map_of_isZero_rightDerived_one`), so the glued section of `Q` lifts.
  For the step, the connecting map `Hᵖ⁺¹(Q) → Hᵖ⁺²(M)` is a monomorphism because `I` is
  injective, so `Hᵖ⁺¹(Q) = 0` and the induction hypothesis applies to `Q`.
