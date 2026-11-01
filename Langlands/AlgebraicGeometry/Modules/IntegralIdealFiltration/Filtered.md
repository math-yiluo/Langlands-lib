# Filtrations by integral ideal pushforwards and the ascending chain argument

Author: Worker 716. This is an internal helper module for
`Langlands.AlgebraicGeometry.Modules.coherentIntegralIdealFiltration`. Its definitions are
derived, not taken from a source: they restate the conclusion of the published
`CoherentIntegralIdealFiltrationStatement` (Stacks Project, tag 01YF) recursively.

## Definitions

- `IsIdealPushforward C` (for `C : X.Modules`) says the following. There are a scheme
  `Z : Scheme.{u}` and a closed immersion `i : Z ⟶ X` with `Z` integral. There are a module
  `I : Z.Modules` with a monomorphism `ι : I ⟶ structureModule Z`, where `I` is
  quasi-coherent, has finite affine sections and is not zero, and an isomorphism
  `C ≅ (Scheme.Modules.pushforward i).obj I`. These are exactly the conditions the statement
  imposes on each successive quotient.
- `Filtered : X.Modules → Prop` is the inductive predicate with two constructors:
  - `zero`: a zero object which is quasi-coherent with finite affine sections is filtered;
  - `step`: suppose `F` is filtered, `M` is quasi-coherent with finite affine sections,
    and `C` satisfies `IsIdealPushforward C`. If `α : F ⟶ M` and `β : M ⟶ C` form a short
    exact sequence (`ShortComplex.ShortExact`), then `M` is filtered.

## Results

- `exists_shortExact_of_iso`: short exactness transported along isomorphisms of the three
  terms. This is `ShortComplex.shortExact_of_iso` with `ShortComplex.isoMk`.
- `Filtered.isQuasicoherent`, `Filtered.hasFiniteAffineSections`: read off the constructors.
- `Filtered.of_iso`: `Filtered` is invariant under isomorphism.
- `Filtered.exists_chain`: a filtered module has a filtration in exactly the form of the
  statement. The proof is by induction on `Filtered`. For `zero`, take `n = 0` and the
  constant family. For `step`, take `Fin.snoc F M` of length `n + 1`. Then
  `Fin.snoc_castSucc`, `Fin.snoc_last` and `Fin.succ_castSucc` identify its terms with the
  old ones, and the short exact sequences are transported along the resulting `eqToIso`
  (and along `F (Fin.last n) ≅ F'` and `C ≅ i_* I`) by `exists_shortExact_of_iso`.
- `vanishesOn_iSup`, `vanishesOn_of_affine`: vanishing on a union of opens, and
  vanishing on an affine open with zero sections for a quasi-coherent module. The second
  uses `QuasicoherentLocal.isLocalizingAt_of_isQuasicoherent`: a section over a basic open
  `D(g)` is, after multiplication by a unit power of `g`, the restriction of a section
  over the affine open, which is zero.
- `secHom`, `injective_app`, `exists_finite_affine_cover`: sections of a morphism as a
  linear map, injectivity of a monomorphism on sections (through
  `PushforwardInjectiveAcyclic.toAbSheaf`), and a finite affine cover of a noetherian
  scheme (compactness).

## The ascending chain argument

`filtered_of_core` takes a hypothesis `core`. It says that every nonzero quasi-coherent `Q`
with finite affine sections receives a monomorphism `φ : C ⟶ Q` with
`IsIdealPushforward C`, `C` quasi-coherent with finite affine sections, and `C` nonzero.
From `core` it proves that every quasi-coherent `M` with finite affine sections is
`Filtered`.

Fix a finite affine cover `U l` of `X`. Each `Γ(M, U l)` is a noetherian module.
Monomorphisms `κ : K ⟶ M` are measured by the family of ranges of `κ` on the `U l`.
These families lie in a finite product of the order duals of the submodule lattices, which
is well founded (`Pi.wellFoundedLT`). Choose a filtered `K₀ ↪ M` whose measure is minimal
in this order, that is, whose ranges are maximal. Suppose `κ₀` is not an epimorphism. Then
`core` applies to `cokernel κ₀` and gives `φ : C ↪ cokernel κ₀`. Let `K'` be the pullback
of `cokernel.π κ₀` along `φ`.

- `pullback.fst : K' ⟶ M` is a monomorphism.
- `pullback.snd : K' ⟶ C` is an epimorphism (`Abelian.epi_pullback_of_epi_f`).
- `pullback.lift κ₀ 0 : K₀ ⟶ K'` is its kernel (via `Abelian.monoLift`).

So `K'` is filtered by `Filtered.step`; it is quasi-coherent with finite affine sections
by the Library pullback lemmas. Its ranges contain those of `K₀`. If they were equal on
every `U l`, then by surjectivity on affine sections and injectivity of `pullback.fst`,
every section of `C` over every `U l` would vanish. Then `C` would vanish on every `U l`
(`vanishesOn_of_affine`), hence everywhere, contradicting `C ≠ 0`. So the measure strictly
decreases, contradicting minimality. Hence `κ₀` is an epimorphism and a monomorphism, so
an isomorphism, and `M ≅ K₀` is filtered.
