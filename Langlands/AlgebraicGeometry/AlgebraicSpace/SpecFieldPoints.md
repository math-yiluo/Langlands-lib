# Spectra of field extensions over a field

Internal infrastructure for the proof of
`SeparatedAddCommGroupSheafSchemeRepresentabilityStatement`. The field theory is
standard. It uses Mathlib's normal closure, `Normal.algHomEquivAut` and
`AlgEquiv.restrictNormal`.

- `specOver k L` is `Spec L` over `Spec k`, for a `k`-algebra `L`. For a `k`-algebra map
  `σ : L →ₐ[k] L'`, `specOverMap σ : specOver k L' ⟶ specOver k L` is the induced morphism
  (`specOverMap_left`), with `specMap_comp` and `specMap_id`. The map and its
  underlying-map formula reuse
  `Langlands.AlgebraicGeometry.Picard.DualNumberDouble.specOverMap` and
  `specOverMap_left` from `GroupObjectTangentAddition`.
- Instances: `specOver k L` is affine and every `(specOverMap σ).left` is an affine morphism. If
  `L` and `L'` are fields and `L'` is finite over `k`, then `(specOverMap σ).left` is finite. For
  a field `L` over `k`, the structure morphism of `specOver k L` is separated, flat and
  surjective, and finite and locally of finite presentation when `L` is finite over `k`.
- `exists_algHom_of_specOver_hom`: every morphism `specOver k L' ⟶ specOver k L` is
  `specOverMap j` for a `k`-algebra map `j`. `specIso σ` is the automorphism of `specOver k L`
  given by `σ ∈ Aut(L/k)`. `surjective_specOver_hom`: every morphism over `Spec k` from the
  spectrum of a nonzero ring to the spectrum of a field is surjective.
- `exists_algEquiv_comp`: two `k`-embeddings of a normal extension `L` into a field differ
  by an automorphism of `L`.
- `exists_restrict`: for `j : L →ₐ[k] L'` between fields with `L` normal, every
  `σ ∈ Aut(L'/k)` has a `τ ∈ Aut(L/k)` with `σ ∘ j ∘ τ = j`.
- `exists_finite_normal_extension`: a finite extension `K/k` embeds into a finite normal
  extension in the same universe (the normal closure inside an algebraic closure of `K`).
- `exists_algHom_of_hom` and `exists_galois_of_hom`: a morphism from a field point
  `s : Spec K ⟶ Spec k` to `specOver k L` comes from a `k`-algebra map `L → K` (with the
  `k`-algebra structure on `K` given by `s`). Two such morphisms into a normal field `L`
  differ by `specOverMap σ` for some `σ ∈ Aut(L/k)`.
- `fst_invariant_of_galois_stable`: let `W` be an open subfunctor of `F × Spec L`, with `L`
  a normal field extension of `k`, that is stable under `mapRight (specOverMap σ)` for all
  `σ ∈ Aut(L/k)`. Then for any two sections with the same `F`-component, one lies in `W`
  if and only if the other does. This is checked on field-valued tests with Worker 1150's
  `OpenSubfunctorPoints.invariant_of_field_tests`.
