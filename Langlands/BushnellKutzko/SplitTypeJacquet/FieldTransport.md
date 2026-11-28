# Transport of block subgroups and cuspidality along a field isomorphism

Module `Langlands.BushnellKutzko.SplitTypeJacquet.FieldTransport`. Let `ψ : k ≃+* k'` be a ring
isomorphism of fields.

- `glMap ψ : GL_n(k) →* GL_n(k')` is the entrywise map `Matrix.GeneralLinearGroup.map`.
  `glMap_apply` gives its entries, and `glMap_symm_glMap`, `glMap_glMap_symm` show that
  `glMap ψ.symm` is inverse to it.
- `glMap_mem_parabolic` and `glMap_mem_unipotentSubgroup` use preservation of zero and one
  to map `B.parabolic k` and `B.unipotentSubgroup k` into the respective subgroups over `k'`.
  Applying the same lemmas to `ψ.symm` gives surjectivity onto each subgroup.
- `parabolic_ne_top_of_map` carries properness of `B.parabolic k'` back to `B.parabolic k`.
- In `isCuspidal_comp_glMap`, if `ρ` is a cuspidal representation of `GL_n(k)` (in the sense of
  `FiniteGeneralLinear.IsCuspidal`), then `ρ ∘ glMap ψ.symm` is a cuspidal representation of
  `GL_n(k')`. A vector fixed by `B.unipotentSubgroup k'` under the composite is fixed by
  `B.unipotentSubgroup k` under `ρ`, since `u = glMap ψ.symm (glMap ψ u)`.
