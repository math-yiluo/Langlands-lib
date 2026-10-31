# Higher cohomology of quasi-coherent modules on affine schemes vanishes: proof

Author: Worker 958.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingStatement.{u}`
from `Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingStatement`,
which it imports unchanged.

## Main result

`Langlands.AlgebraicGeometry.Modules.affineQuasicoherentCohomologyVanishing` is the theorem

```lean
theorem affineQuasicoherentCohomologyVanishing :
    AffineQuasicoherentCohomologyVanishingStatement.{u}
```

for an arbitrary universe `u`. Unfolded, it says: for every scheme `X : Scheme.{u}` with
`IsAffine X`, every `M : X.Modules` with `M.IsQuasicoherent` and every `n : ℕ`,

1. `IsZero ((DerivedSections.cohomology X (n + 1)).obj M)`, and
2. for every `R : CommRingCat.{u}` and `g : X ⟶ Spec R`,
   `IsZero ((DerivedSections.relativeCohomology g (n + 1)).obj M)`.

The theorem uses no hypothesis beyond the statement's. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Library results used

The module imports `Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof`
and uses the following declarations from it, all in the namespace
`Langlands.AlgebraicGeometry.Modules.AffineVanishing`:

- `IsCechAcyclic G`: for every affine open `W` of `X`, every finite `ι : Type u` and every
  `g : ι → Γ(X, W)` generating the unit ideal, and every `p : ℕ`,
  `Cech.ExactAt G.presheaf (cover g) p` holds for the cover `fun i => X.basicOpen (g i)`.
  Here `Cech.ExactAt P U p` (Library `Langlands.Cohomology.CechCochains`) means that every
  ordered Čech `(p + 1)`-cocycle is the differential of a `p`-cochain. So `IsCechAcyclic G`
  is exactness of the ordered Čech complex in every positive cochain degree, that is, the
  vanishing of Čech cohomology `Ȟᵏ` for all `k ≥ 1`; degree `0` is not constrained.
- `isCechAcyclic_of_isQuasicoherent M`: quasi-coherent modules are Čech-acyclic (the Lean
  form of Stacks Lemma 30.2.1, tag 01X9).
- `isCechAcyclic_X₃ hS hG`: in a short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` of
  `𝒪_X`-modules with `I` injective and `G` Čech-acyclic, `Q` is Čech-acyclic.
- `surjective_app_of_exactAt hS hV hG`: for a short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` of
  abelian sheaves on `X`, an affine open `V` and `Cech.ExactAt G (cover g) 0` for every
  standard cover `g` of `V` (exactness in cochain degree `1`, i.e. vanishing first Čech
  cohomology `Ȟ¹`), the map `I(V) ⟶ Q(V)` is surjective.

It also uses `PushforwardInjectiveAcyclic.toAbSheaf`, `injectiveSc` and
`injectiveSc_shortExact` (the chosen short exact sequence
`0 ⟶ G ⟶ Injective.under G ⟶ cokernel (Injective.ι G) ⟶ 0`), the dimension-shift lemmas
`Langlands.Cohomology.DerivedPlus.rightDerivedδ`, `epi_rightDerivedδ_of_isZero` and
`rightDerived_map_comp_δ`, and `DerivedSections.structureRingHom` and
`DerivedSections.relativeCohomologyRestrictScalarsIso`.

## Route of the proof

The Stacks proof of Lemma 30.2.2 (tag 01XB) applies the general criterion Cohomology,
Lemma 20.11.9 (tag 01EW) to the basis of affine opens. The Lean proof runs the dimension
shift of that criterion directly for the global sections functor on the affine scheme `X`,
in three steps.

1. **Global sections are right exact on Čech-acyclic kernels**
   (`AffineVanishing.epi_globalSections_map_of_isCechAcyclic`). Let `X` be affine and let
   `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` be short exact in `X.Modules` with `G` Čech-acyclic. The forgetful
   functor `toAbSheaf X` to abelian sheaves is exact, so the image sequence is short exact.
   The open `⊤` is affine (`isAffineOpen_top X`), and the hypothesis `IsCechAcyclic G`
   specialised to `W = ⊤` and predicate index `p = 0`, namely `Cech.ExactAt … 0`, which is
   exactness in cochain degree `1` (vanishing `Ȟ¹`), is exactly the input of
   `surjective_app_of_exactAt`.
   Hence `Γ(X, I) ⟶ Γ(X, Q)` is surjective, so
   `(DerivedSections.globalSections X).map S.g` is an epimorphism of `Γ(X, ⊤)`-modules
   (`ModuleCat.epi_iff_surjective`).

2. **Dimension shift** (`AffineVanishing.isZero_cohomology_of_isCechAcyclic`). For `X`
   affine, every `n : ℕ` and every Čech-acyclic `G`, `Hⁿ⁺¹(X, G)` is zero. Write `F` for
   `DerivedSections.globalSections X`; `DerivedSections.cohomology X (n + 1)` is
   `F.rightDerived (n + 1)` by definition. The proof inducts on `n` for all `G` at once,
   using the short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` of `injectiveSc G` with `I`
   injective, and its connecting morphisms `δ : Rᵏ F(Q) ⟶ Rᵏ⁺¹ F(G)`.
   - Since `Rᵏ⁺¹ F(I) = 0` for the injective `I`, `epi_rightDerivedδ_of_isZero` makes
     `δ : Rᵏ F(Q) ⟶ Rᵏ⁺¹ F(G)` an epimorphism for every `k`.
   - Case `n = 0`. The map `R⁰F(I) ⟶ R⁰F(Q)` is an epimorphism: under the natural
     isomorphism `F.rightDerivedZeroIsoSelf : R⁰F ≅ F` it is `F(I) ⟶ F(Q)`, an epimorphism
     by step 1. Its composite with `δ` is zero (`rightDerived_map_comp_δ`), so `δ = 0`. An
     epimorphism that is zero has zero target (`IsZero.of_epi_eq_zero`), so `R¹F(G) = 0`.
   - Case `n + 1`. The cokernel `Q` is Čech-acyclic by `isCechAcyclic_X₃`, so the induction
     hypothesis gives `Rⁿ⁺¹F(Q) = 0`. The epimorphism `δ : Rⁿ⁺¹F(Q) ⟶ Rⁿ⁺²F(G)` then has
     zero target (`IsZero.of_epi`).

   The proof works in the standard derived categories `HasDerivedCategory.standard` of
   `X.Modules` and `ModuleCat Γ(X, ⊤)`, which the `DerivedPlus` lemmas require; the
   right-derived functors of Mathlib do not depend on this choice.

3. **The statement** (`affineQuasicoherentCohomologyVanishing`). Given `X`, `M`, `n`, the
   module `M` is Čech-acyclic by `isCechAcyclic_of_isQuasicoherent`, so step 2 gives part 1.
   For part 2, restriction of scalars along `(DerivedSections.structureRingHom g).hom`
   preserves zero objects (`Functor.map_isZero`), and the component at `M` of
   `DerivedSections.relativeCohomologyRestrictScalarsIso g (n + 1)` identifies the
   restricted module with `(DerivedSections.relativeCohomology g (n + 1)).obj M`.

## Declarations in this module

- `AffineVanishing.epi_globalSections_map_of_isCechAcyclic hS hG`: step 1.
- `AffineVanishing.isZero_cohomology_of_isCechAcyclic n G hG`: step 2.
- `affineQuasicoherentCohomologyVanishing`: step 3, the target theorem.

## Original source

The mathematics is Stacks Project, Cohomology of Schemes, Lemma 30.2.2
(`lemma-quasi-coherent-affine-cohomology-zero`, tag 01XB), in `coherent.tex` of the
registered folder `stacks-flasque-affine-vanishing-kunneth-a04446e5` (Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, folder SHA-256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`), statement lines
145–155, proof lines 157–174. The statement Markdown records the specialisation to the
affine open `U = X` and the reading of part 2 as `R`-modules.
