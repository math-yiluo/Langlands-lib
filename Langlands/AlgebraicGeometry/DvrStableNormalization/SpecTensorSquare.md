# Base change of an affine scheme as the spectrum of a tensor product

Worker 6.

- `hom_eq_isoSpec_comp`: for affine `Zo` over `Spec R`, `Zo.hom` is `Zo.left.isoSpec.hom` followed by
  `Spec` of the algebra map `R → Γ(Zo, ⊤)`.
- `isPullback_spec_tensor`: `Spec (R' ⊗[R] Γ(Zo, ⊤))`, with the maps induced by `includeRight`
  (followed by `isoSpec.inv`) and by `algebraMap R' (R' ⊗[R] Γ(Zo, ⊤))`, is a pullback of `Zo.hom`
  along `Spec R' → Spec R` (from `pullbackSpecIso`).
