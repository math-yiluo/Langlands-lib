# Invariant forms on compact induction and equivariant functionals

Author: Worker 805.

This helper module relates invariant bilinear forms on a compactly induced
character to equivariant functionals, and constructs the standard invariant
pairing between compact inductions of inverse characters. It is used by the
proof of `Langlands.Whittaker.MirabolicCompactTwistedPairingStatement`, where
`G` is the mirabolic group, `H` its upper unipotent subgroup and `θ` the
standard character. The construction is internal (derived); it plays the role
of the Frobenius-duality step in BZ76's proof of Proposition 5.15(b), p.50,
in the form needed for bilinear forms on compact inductions.

## Setting and hypotheses

`G` is a topological group, `H` a subgroup, `θ θ' : H →* ℂˣ` characters with
`θ' h * θ h = 1` (`hθ'`), `characterRepresentation θ` smooth (`hσ`, an open
kernel), `π : Representation ℂ G W` smooth (`hπ`), and `ν` a measure on the
published left quotient `QuotientIntegration.LeftQuotient H` (Borel) with

- `hinv`: right translation by every `g` preserves `ν`;
- `hmass`: for every compact open subgroup `J`, the orbit
  `compactOpenQuotientOrbit H J` (the image of `H J` in `H \ G`) has positive,
  finite mass;
- `hG`: compact open subgroups form a neighbourhood basis of `1`.

`InvariantBilinear.forms ρ σ κ` is the published space of bilinear forms with
`B (ρ g v) (σ g w) = κ g * B v w`; here `κ = 1`. `Whittaker.functionals H θ' π`
is the published space of functionals with `ℓ (π h w) = θ' h * ℓ w`.

## Main results

```lean
theorem exists_injective_formsFunctional [T2Space G] (hG) (H) (hH : IsClosed (H : Set G)) (θ) (hσ)
    (π) (hπ) (ν) (hinv) (hmass) (θ') (hθ') :
    ∃ L : InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
        (fun _ => (1 : ℂ)) →ₗ[ℂ] Whittaker.functionals H θ' π,
      Function.Injective L

theorem exists_standardForm (hG) (H) (θ θ') (hσ) (hθ') (ν) [IsFiniteMeasureOnCompacts ν]
    (hinv) (hmass) :
    ∃ B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ))
        (compactInduced H (characterRepresentation θ')) (fun _ => (1 : ℂ)), B ≠ 0
```

(both in namespace `Langlands.Induction.FormsFunctional`; all other
declarations are private).

## The functional attached to a form

For a compact open subgroup `K` on whose conjugate intersection with `H` the
character is trivial, `s_K` is the published double-coset section
`compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv`: supported
on `H K`, with `s_K (h k) = θ h`. For `w` fixed by `K`,

`normalizedValue B K w = ν(compactOpenQuotientOrbit H K)⁻¹ · B (s_K, w)`.

**Independence of `K`** (`normalizedValue_refine`, `normalizedValue_eq`). For
`N ≤ K`, the quotient `K / N` is finite (`finite_cosetSpace`). Summing the right
translates of `s_N` over coset representatives gives `c · s_K`, where `c` counts
the representatives landing in the orbit of `N` (`sum_translate_section`); the
same counting gives `|K/N| · ν(orbit N) = c · ν(orbit K)`
(`orbit_mass_relation`, from right invariance of `ν`). Since `B` is invariant
and `w` is fixed by `K`, each translate pairs with `w` like `s_N`
(`form_translate_of_fixed`), so `|K/N| · B(s_N, w) = c · B(s_K, w)`, and the two
normalized values agree. Two admissible subgroups are compared through their
intersection. These refinement lemmas are adapted from the private part of
`Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof`.

`exists_admissible` produces, from `hG`, `hσ` and `hπ`, a compact open `K`
that is admissible and fixes `w`; `functional` takes the normalized value
there. It is additive and homogeneous (`functional`), and the map
`formsFunctional : B ↦ ℓ_B` is linear.

**Equivariance** (`functional_mem`). For `h ∈ H`, `π h w` is fixed by the
conjugate subgroup `h K h⁻¹` (`conjSubgroup`), the right translate of `s_K` by
`h` is `θ h` times the section of `h K h⁻¹` (`section_translate`), and the
orbit masses agree by right invariance (`orbit_conjSubgroup`). Invariance of
`B` then gives `ℓ_B (π h w) = θ h⁻¹ · ℓ_B w = θ' h · ℓ_B w`.

**Injectivity** (`eq_zero_of_functional_eq_zero`). Suppose `ℓ_B = 0`. For any
admissible `K` and any `w`, choose an open `M` fixing `w`; the sum `Σ π(k_q) w`
over representatives of `K / (K ⊓ M)` is fixed by `K` (`sum_mul_rep`), so
`0 = ℓ_B(Σ π(k_q) w)` is a nonzero multiple of `|K/(K ⊓ M)| · B(s_K, w)`,
since `s_K` is fixed by `K` (`translate_section_of_mem`). Hence `B(s_K, w) = 0`
for every `K` and `w`; by scaling the same holds for every section value `v`.
The published `compactLocalSectionSpanning` (here `H` is closed and `G` is
Hausdorff) says that translates of such sections span the compact induction,
and `form_translate` moves translations to the second argument, so `B = 0`.

## The standard pairing

For `f₁` in the compact induction of `θ` and `f₂` in that of `θ'`, the
pointwise product `x ↦ f₁ x · f₂ x` is left `H`-invariant (by `hθ'`), smooth,
and has compact projected support (`productSmooth`, `product`). The standard
form is

`standardForm (f₁, f₂) = coinvariantValue (compactCoinvariantIntegral H 1 ν (f₁ f₂))`,

using the published algebraic integral `compactCoinvariantIntegral` for the
trivial representation of `H` on `ℂ` (finite on compacts by
`IsFiniteMeasureOnCompacts ν`) and the identification of trivial coinvariants
with `ℂ` (`coinvariantValue`). It is bilinear (`LinearMap.mk₂`) and invariant
because the product of translates is the translate of the product and the
integral is right invariant (`compactCoinvariantIntegral_translate`,
`standardForm_mem`). On the unit sections of an admissible `K` (admissible for
both characters, since `θ = 1` on `H ∩ K` forces `θ' = 1` there) the product is
the indicator of the orbit of `K`, so the pairing equals
`ν(compactOpenQuotientOrbit H K)` (`standardForm_section`), which is nonzero by
`hmass`. This gives `exists_standardForm`.
