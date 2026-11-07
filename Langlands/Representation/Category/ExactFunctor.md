# Kernels and exact functors of smooth representations

Module `Langlands.Representation.Category.ExactFunctor`, namespace
`Langlands.SmoothRep`.

These are supporting lemmas for the formal step of Renard 2026, VI.9.6 (printed p.202,
PDF p.208). They relate the concrete exactness notion `SmoothRep.IsShortExact` to
categorical kernels in `SmoothRep R G`, and they record what follows from a functor
preserving short exact sequences.

## Kernels

- `hom_ext'`: two morphisms of smooth representations are equal if their intertwiners
  are equal.
- `isLimitKernelForkOfRangeEq ι k w hι hr`: an injective intertwiner `ι : X ⟶ Y` whose
  range equals the kernel of `k : Y ⟶ Z` is a categorical kernel of `k`. Given
  `g : W ⟶ Y` with `g ≫ k = 0`, every value of `g` lies in the range of `ι`. The lift
  is `g` corestricted to that range and then composed with the inverse of
  `LinearEquiv.ofInjective`. It intertwines the actions because `ι` is injective and
  intertwining.
- `comp_cokernelπ`: `f ≫ cokernelπ f = 0`, where `SmoothRep.cokernel f` is the
  Library's concrete quotient by the range of `f`.
- `range_eq_ker_cokernelπ_comp`: if `b : cokernel f ⟶ C` is injective, then the range of
  `f` is the kernel of `cokernelπ f ≫ b`. This follows from `Submodule.ker_mkQ` and
  `LinearMap.ker_comp_of_ker_eq_bot`.
- `isLimitCokernelπComp`: an injective `f` is a kernel of `cokernelπ f ≫ b` for every
  injective `b`.

## Functors preserving short exact sequences

`PreservesShortExact F` says that a functor
`F : SmoothRep R G ⥤ SmoothRep R H` sends every pair `f, g` with
`IsShortExact (hom f) (hom g)` to a pair with
`IsShortExact (hom (F.map f)) (hom (F.map g))`. This is the form of exactness in the
Library's statement of Renard 2026, VI.1.2 (`LeviParabolicFunctorsExactStatement`).

- `isShortExact_cokernelπ`: an injective `f` together with its cokernel projection is
  short exact.
- `PreservesShortExact.hom_map_cokernelπ_id`: `F` sends `cokernelπ (𝟙 A)` to zero. The
  sequence `𝟙 A, cokernelπ (𝟙 A)` is short exact, so `F` of it is short exact, and the
  kernel of `F (cokernelπ (𝟙 A))` is the range of `F (𝟙 A) = 𝟙`.
- `PreservesShortExact.preservesZeroMorphisms`: `F` preserves zero morphisms. Write
  `0 : A ⟶ B` as `cokernelπ (𝟙 A) ≫ 0` and apply the previous lemma.
- `PreservesShortExact.injective_map`: `F` preserves injectivity. Apply `F` to the
  short exact sequence `f, cokernelπ f`.
- `PreservesShortExact.range_map_eq_ker_map_comp`: for injective `ι` and `b`, the range
  of `F ι` is the kernel of `F (cokernelπ ι ≫ b)`. Exactness gives
  `range (F ι) = ker (F (cokernelπ ι))`, and `F b` is injective.
- `PreservesShortExact.isLimitMapCokernelπComp`: `F` sends the kernel diagram
  `X ⟶ Y ⟶ cokernel ι ↪ Z` to a kernel diagram.
