# Degree-one cohomology classes as Čech cocycles

Author: Worker 727.

This module represents classes in the first cohomology of a Čech-acyclic `𝒪_P`-module (for
instance a quasi-coherent one) by Čech `1`-cocycles on a cover of `P` by affine opens. It is a
helper for the proof of `Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement`.
It contains no `sorry` and no new axioms.

## Definitions

Both in namespace `Langlands.AlgebraicGeometry.Modules.CechDegreeOne`, for a scheme `P`, a family
of opens `Z : ι → P.Opens` and `G : P.Modules`. Restrictions are the Library's
`Langlands.Cohomology.Cech.res` on the abelian presheaf `G.presheaf`.

- `IsCocycle Z z` for `z : ∀ a b, Γ(G, Z a ⊓ Z b)`: for all indices `a b c` and every open
  `O` contained in `Z a ⊓ Z b`, `Z b ⊓ Z c` and `Z a ⊓ Z c`,
  `z a b|_O + z b c|_O = z a c|_O`. This is the Čech `1`-cocycle condition for the ordered
  (not alternating) Čech complex, stated on all small enough opens rather than only on
  `Z a ⊓ Z b ⊓ Z c`, which makes it independent of how the triple intersection is
  parenthesised.
- `IsCoboundary Z z`: there are `g : ∀ a, Γ(G, Z a)` with `z a b = g b|_{Z a ⊓ Z b} -
  g a|_{Z a ⊓ Z b}` for all `a b`.

These are internal definitions: the usual Čech cocycles and coboundaries in degree one
(Stacks, Cohomology of Sheaves, section "The Čech complex and Čech cohomology", tag 01ED).

## Main results

`exists_cocycle`:

```lean
theorem exists_cocycle {R : CommRingCat.{u}} (f : P ⟶ Spec R) {M : P.Modules}
    (hM : AffineVanishing.IsCechAcyclic M) (hZ : ∀ a, IsAffineOpen (Z a)) (hcov : iSup Z = ⊤)
    (c : (DerivedSections.relativeCohomology f 1).obj M) :
    ∃ z : ∀ a b, Γ(M, Z a ⊓ Z b), IsCocycle Z z ∧
      (∀ (G : P.Modules) (u : M ⟶ G),
        ((DerivedSections.relativeCohomology f 1).map u).hom c = 0 →
          IsCoboundary Z (fun a b => u.app _ (z a b))) ∧
      (IsCoboundary Z z → c = 0)
```

For any morphism `f : P ⟶ Spec R`, a module `M` in the Library class
`AffineVanishing.IsCechAcyclic` (exact Čech complexes for standard coverings of affine opens;
it contains every quasi-coherent module by `AffineVanishing.isCechAcyclic_of_isQuasicoherent`),
and a cover `Z` of `P` by affine opens indexed by any type, every class
`c ∈ H¹(P, M) = (relativeCohomology f 1).obj M` has a cocycle representative `z` such that

1. for every module map `u : M ⟶ G` with `H¹(u) c = 0`, the image cocycle `u z` is a
   coboundary, and
2. if `z` itself is a coboundary, then `c = 0`.

The cover may be infinite and the pairwise intersections need not be affine. The statement is
the part of the comparison between Čech and derived-functor cohomology in degree one that the
application needs: Stacks Lemma 0B8R (`lemma-cech-h1`: `Ȟ¹(𝒰, H) → H¹(X, H)` is injective, used
in item 2) and the degree-one case of Stacks Lemma 01XD (`lemma-cech-cohomology-quasi-coherent`:
Čech cohomology on a cover with affine intersections computes the cohomology of a
quasi-coherent module; the surjectivity in degree one needs only the members of the cover to be
affine).

`map_unitToPushforwardUnit_eq_zero`: for `f : P ⟶ Spec R`, `i : X ⟶ P`, `n : ℕ` and
`c ∈ Hⁿ(P, 𝒪_P)`, if `c` is killed by the unit `𝒪_P ⟶ i_* i^* 𝒪_P` of Mathlib's adjunction
`Scheme.Modules.pullbackPushforwardAdjunction i`, then it is killed by the Library's structure
map `Langlands.Scheme.Modules.unitToPushforwardUnit i : 𝒪_P ⟶ i_* 𝒪_X`. Proof: by the Library's
`Langlands.Scheme.Modules.pullbackUnitAdjunction` and `Adjunction.homEquiv_unit`,
`unitToPushforwardUnit i` is the unit followed by `i_*` of the Library iso
`pullbackUnitIso i : i^* 𝒪_P ≅ 𝒪_X`, and `Hⁿ` is a functor.

`isQuasicoherent_unit X` (instance): the structure sheaf `SheafOfModules.unit X.ringCatSheaf`
is quasi-coherent. It is isomorphic (`coproductUniqueIso`) to Mathlib's free module on
`PUnit`, which is quasi-coherent, and quasi-coherence is closed under isomorphisms.

## Proof of `exists_cocycle`

Write `F = relativeGlobalSections f`, so `relativeCohomology f n = F.rightDerived n`. The proof
locally installs `HasDerivedCategory.standard` for `P.Modules` and `ModuleCat R` to use the
Library's connecting morphisms `Langlands.Cohomology.DerivedPlus.rightDerivedδ`; this choice does
not occur in the statement. Let `S = PushforwardInjectiveAcyclic.injectiveSc M` be the short
exact sequence `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` with `I = Injective.under M` and `Q` the cokernel.

1. **Lifting to `R⁰ F Q`.** `R¹ F I = 0` (`isZero_rightDerived_obj_injective_succ`), so
   `δ : R⁰ F Q ⟶ R¹ F M` is an epimorphism (`epi_rightDerivedδ_of_isZero`), hence surjective
   on elements. Choose `q₀` with `δ q₀ = c`, and let `q ∈ Γ(Q, ⊤)` be its image under
   `rightDerivedZeroIsoSelf`.
2. **Local lifts.** Each `Z a` is affine and `M` is Čech-acyclic, so `Γ(I, Z a) ⟶ Γ(Q, Z a)` is
   surjective (Library `AffineVanishing.surjective_app_of_exactAt`, Stacks 01EU). Choose
   `t a ∈ Γ(I, Z a)` lifting `q|_{Z a}`.
3. **The cocycle.** `t b - t a` maps to `0` in `Q` on `Z a ⊓ Z b`, so it equals the image of a
   unique `z a b ∈ Γ(M, Z a ⊓ Z b)` (`AffineVanishing.exists_f_app_eq`,
   `AffineVanishing.injective_f_app`: left exactness of sections). The cocycle identity holds
   after applying the injective map `Γ(M, O) ⟶ Γ(I, O)`, where it is
   `(t b - t a) + (t c - t b) = t c - t a`.
4. **Compatibility with `u : M ⟶ G`.** Let `SG = injectiveSc G`. Extend `u` to
   `τ₂ : I ⟶ I_G` with `ι_M ≫ τ₂ = u ≫ ι_G` (`Injective.factorThru`) and to
   `τ₃ : Q ⟶ Q_G` on cokernels, a morphism of short complexes `φ : S ⟶ SG`. Naturality of the
   connecting morphism (`DerivedPlus.rightDerivedδ_naturality`) gives
   `δ_G(R⁰F(τ₃) q₀) = H¹(u) c = 0`, so by exactness of `R⁰F(I_G) ⟶ R⁰F(Q_G) ⟶ R¹F(G)`
   (`DerivedPlus.rightDerived_exact₃`) there is `s ∈ Γ(I_G, ⊤)` with `π_G s = τ₃ q`. Then
   `τ₂(t a) - s|_{Z a}` maps to `0` in `Q_G`, so it is `ι_G (g a)` for some `g a ∈ Γ(G, Z a)`.
   Applying the injective `ι_G` shows `u (z a b) = g b - g a`.
5. **Coboundaries give `c = 0`.** If `z a b = w b - w a`, the sections `t a - ι_M (w a)` of
   `I` agree on overlaps and glue (sheaf property of `I`, `existsUnique_gluing'`) to
   `T ∈ Γ(I, ⊤)`. Then `π T = q`, since both agree on every `Z a` (`eq_of_locally_eq'`).
   Hence `q₀` lies in the image of `R⁰F(I) ⟶ R⁰F(Q)`, and `c = δ q₀ = 0` because the
   composite `R⁰F(I) ⟶ R⁰F(Q) ⟶ R¹F(M)` is zero (`DerivedPlus.rightDerived_map_comp_δ`).

This is the standard argument of Stacks Lemma 01EV (`lemma-cech-vanish`, `cohomology.tex`
lines 1630-1693): embed into an injective and compare the Čech and derived-functor connecting
maps.

## Auxiliary results

- `app_comp_apply φ ψ U x`: `(φ ≫ ψ).app U x = ψ.app U (φ.app U x)`.
- `app_res φ h x`: sections of a module map commute with `Cech.res`.
- `relativeGlobalSections_map_apply f φ x`: `F.map φ` acts on elements as `φ.app ⊤`.
- `ι_app_injective M U`, `exists_ι_app_eq M b hb`, `π_app_ι_app M U a`: left exactness of the
  sections of `0 ⟶ M ⟶ I ⟶ Q`.
- `π_app_surjective M hM hU`: `Γ(I, U) ⟶ Γ(Q, U)` is surjective for affine `U` and
  Čech-acyclic `M`.

## Original source

The Stacks Project at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`: `cohomology.tex` Lemma 0B8R
(`lemma-cech-h1`, lines 1485-1497), Lemma 01EU (`lemma-ses-cech-h1`, lines 1592-1628), Lemma
01EV (`lemma-cech-vanish`, lines 1630-1693); `coherent.tex` Lemma 01XD
(`lemma-cech-cohomology-quasi-coherent`, lines 245-262). The Lean results are proved directly
from the derived-functor definition as described above, not via the Čech-to-cohomology spectral
sequence used by Stacks for 01XD.
