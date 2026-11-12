# Archimedean local Weil groups mapped into relative and absolute global Weil groups

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. The declarations lie in the namespaces
`Langlands.ClassField.Global.RelativeWeilGroup` and `Langlands.ClassField.Global.WeilMapSystem`.
The module is the archimedean counterpart of the published finite-place predicates
`RelativeWeilGroup.IsLocalRelativeWeilMap` and `WeilMapSystem.IsLocalWeilMap`. It defines
when a continuous homomorphism from a concrete archimedean Weil group `W_ℂ` or `W_ℝ` is a
local-to-relative Weil map `W_{F_v} → W_{E/F}`, or a local-to-global Weil map
`W_{F_v} → W_F`, at an infinite place `v`. It constructs no such map and asserts no
existence.

## Setting

`F E : Type u` are number fields with `[Algebra F E]` and `[IsGalois F E]`, and `c` is a
class family. `W_{E/F} = RelativeWeilGroup c F E`, with `inclusion`, `projection` and the
idele class group `C_E = IdeleClassGroup (𝓞 E) E`. As in `IsLocalRelativeWeilMap`, maps into
`W_{E/F}` are continuous for the topology built from the Krull topology on `Gal(E/F)`. That
topology is discrete, since the group is finite. The archimedean Weil groups are the
published concrete groups of `Langlands.Weil.Archimedean`:

- `ComplexWeil = ℂˣ`;
- `RealWeil`, with elements `z j^b`, `j² = -1` and `j z j⁻¹ = z̄`. It comes with the
  inclusion `RealWeil.ofComplex`, the Galois map `RealWeil.toGalois : W_ℝ → Gal(ℂ/ℝ)`, and
  the continuous homomorphism `RealWeil.abelianCoordinate (z j^b) = (-1)^b |z|²`.

All places are fixed through a complex embedding `ψ : E →+* ℂ`. The place of `E` is
`w = InfinitePlace.mk ψ`, and the place of `F` below it is the place of
`φ = ψ ∘ algebraMap F E`. `E_w = w.Completion` is Mathlib's completion, and
`IdeleClassGroup.ofCompletion (𝓞 E) E w : E_wˣ →* C_E` is Mathlib's `w`-coordinate map, Tate's
`η` in (1.6.1).

## Declarations

### Relative maps

- `IsCompletionExtension ψ ψw`: `ψw : E_w →+* ℂ` is continuous and extends `ψ` on `E`. Such
  an extension is unique, because `E` is dense in `E_w`. Mathlib's `extensionEmbedding` is
  one when `ψ = w.embedding`. The predicates below quantify existentially over `ψw`, so they
  are independent of a choice.
- `IsComplexLocalRelativeWeilMap ψ ι`, for `ι : ComplexWeil →ₜ* W_{E/F}`, is the conjunction
  of three conditions:
  1. `φ` is not real, so the place of `F` below `ψ` is complex. Then `F_v`, `E_w` and
     `\bar{F_v}` are all identified with `ℂ` through `ψ`, and `W_{F_v} = W_{E_w} = ℂˣ`.
  2. For all `g` and `x : E`: `ψ(projection (ι g) x) = ψ x`. The Galois image of `W_ℂ` is
     trivial.
  3. For some `ψw` with `IsCompletionExtension ψ ψw`, and every `x : E_wˣ`:
     `ι(ψw(x)) = (inclusion (ofCompletion w x))⁻¹`.
- `IsRealLocalRelativeWeilMap ψ ι`, for `ι : RealWeil →ₜ* W_{E/F}`, is the conjunction of
  three conditions:
  1. `φ` is real, so the place of `F` below `ψ` is real, `F_v = ℝ` and `\bar{F_v} = ℂ`.
  2. For all `g` and `x : E`: `ψ(projection (ι g) x) = toGalois(g)(ψ x)`. The image of `ι g`
     in `Gal(E/F)` acts on `E`, through `ψ`, as the Galois image of `g` acts on `ℂ`.
  3. For some `ψw` with `IsCompletionExtension ψ ψw`, and every `x : E_wˣ`, two cases:
     - if `ψ` is real (`w` real, `E_w = ℝ`, `W_{E_w} = W_ℝ`), then
       `ι g = (inclusion (ofCompletion w x))⁻¹` for every `g` with
       `abelianCoordinate g = ψw(x)`;
     - if `ψ` is not real (`w` complex, `E_w = ℂ`, `W_{E_w} = W_ℂ`), then
       `ι(ofComplex (ψw x)) = (inclusion (ofCompletion w x))⁻¹`.

### Absolute maps

For `S : WeilMapSystem c F Ω h` and an embedding `φ : F →+* ℂ`:

- `S.IsComplexLocalWeilMap φ θ`, for `θ : ComplexWeil →ₜ* S.WeilGroup`, holds when for every
  finite Galois layer `K` there are `ψ : K →+* ℂ` with `ψ ∘ algebraMap F K = φ` and
  `x : W_{K/F}` such that `IsComplexLocalRelativeWeilMap ψ (S.conjLevelMap K x θ)`.
- `S.IsRealLocalWeilMap φ θ`, for `θ : RealWeil →ₜ* S.WeilGroup`, is the same with
  `IsRealLocalRelativeWeilMap`.
- `IsComplexLocalWeilMap.conjMap` and `IsRealLocalWeilMap.conjMap`: both properties are
  invariant under conjugation of `θ` by `y : S.WeilGroup`. The witness `x` becomes
  `x * (S.toLevel K y)⁻¹`, by the published `conjLevelMap_conjMap`.
- `IsComplexLocalWeilMap.exists_level` and `IsRealLocalWeilMap.exists_level`: at each layer,
  `S.toLevel K (θ g) = x⁻¹ * ι g * x` for a local-to-relative Weil map `ι` at some `ψ`
  extending `φ`.

## Source correspondence

J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
literature ID `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`. The PDF page is the
printed page plus nine. The following passages were read.

- (1.4.3), printed p.6 (PDF p.15). For `F = ℂ`: `W_F = ℂˣ`, `φ` trivial, and `r_F` the
  identity. For `F = ℝ`: `W_F = ℂˣ ∪ jℂˣ`, `φ` sends `ℂˣ` to 1 and `jℂˣ` to complex
  conjugation, `r_F(-1) = j W_F^c`, and `r_F(x) = x^{1/2} W_F^c` for `x > 0`.
- (1.6.1), printed p.8 (PDF p.17). For an `F`-embedding `i : \bar F → \bar F_v` and
  `E_v = i(E)F_v`, there is a continuous `θ_v : W_{F_v} → W_F`. It is compatible with
  `G_{F_v} → G_F` induced by `i`, and with `η : C_{E_v} → C_E` through `r_{E_v}` and `r_E`.
  It is unique up to inner automorphisms by elements of `W_F^0` in the number field case.
- (1.4.6), printed p.7 (PDF p.16), and the published `Archimedean.md`: the norm
  `|z|²` on `ℂˣ` and the coordinate conventions of `RealWeil`.

### Derived formulation

1. **Embeddings instead of `i`.** Tate's `i` restricted to `E` is the embedding
   `ψ : E → \bar F_v = ℂ`. `E_v = i(E)F_v` is the closure of `ψ(E)`, identified with `E_w`
   through `ψw`. In the complex case, `F_v ⊆ ℂ` is the closure of `φ(F)`, which is all of
   `ℂ`. So `W_{F_v} = F_vˣ = ℂˣ` is the literal group `ComplexWeil`.
2. **Reciprocity at the archimedean places.** For `E_w = ℂ`, `r_{E_w}` is the identity of
   `ℂˣ = W_ℂ`. For `E_w = ℝ`, `r_ℝ⁻¹ : W_ℝ → ℝˣ` is the composite of abelianization with the
   inverse of Tate's `r_ℝ`. It sends `z j^b` to `(-1)^b |z|²`: the circle `|z| = 1` is the
   commutator subgroup, positive reals `x` are `r_ℝ(x²)`, and `j` is `r_ℝ(-1)`. This is the
   published `RealWeil.abelianCoordinate`. Condition 3 in the real-`w` case therefore states
   `ι = (inclusion ∘ η ∘ r_ℝ⁻¹)⁻¹` on all of `W_ℝ`, with `E_w = ℝ` identified through `ψw`.
3. **The inverse.** As in the published `LocalRelativeWeilMap.md`, the library's class
   families follow the arithmetic normalization of Artin–Tate, and Tate's extension class is
   its negative. Tate's coefficient embedding `i_T` corresponds to `x ↦ (inclusion x)⁻¹`.
   Hence Tate's `θ_v(y) = i_T(η(r_{E_w}⁻¹ y))` becomes
   `(inclusion (η (r_{E_w}⁻¹ y)))⁻¹`. The sign argument there concerns the coefficient
   embedding of `W_{E/F}` and applies unchanged at archimedean places.
4. **Consistency checks.** In the real case with complex `w`: `j (ofComplex z) j⁻¹ =
   ofComplex z̄`. By condition 2, `ι(j)` projects to the element of `Gal(E/F)` that acts as
   complex conjugation through `ψ`. That element fixes `w` and acts on `E_w ≅ ℂ` as
   conjugation, so conjugation by `ι(j)` on `C_E` sends `η(ψw⁻¹ z)` to `η(ψw⁻¹ z̄)`, as
   condition 3 requires. In the real case with real `w`, condition 3 defines a homomorphism,
   because `abelianCoordinate` is one and `C_E` is commutative. Condition 2 then forces the
   projection to be trivial. These are explanations, not formal proofs.
5. **Absolute maps.** The absolute predicates test every finite Galois layer and allow an
   inner automorphism of `W_{K/F}` at each layer. This is for the same reason as in the
   published `IsLocalWeilMap`, and it matches the ambiguity in (1.6.1). The embedding
   `φ : F → ℂ` fixes the identification of `F_v`. For complex `v`, `φ` and `φ̄` give
   predicates related by complex conjugation on `W_ℂ`.

## Scope and remaining obligations

The following are not proved here:

- existence of maps satisfying these predicates for the arithmetic fundamental-class
  family (Tate (1.6.1)), which also needs the archimedean local compatibility of the class
  family (the published `FundamentalClass.LocalCompatibility` concerns finite places only);
- uniqueness up to conjugation;
- comparison with the finite-place predicates in a single statement over all places.

Archimedean components of representations of `W_F` along these maps are separate
constructions.
