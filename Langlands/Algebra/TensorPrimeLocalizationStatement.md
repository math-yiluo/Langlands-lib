# Prime localization of an actual tensor transition

`Langlands.Algebra.TensorPrimeLocalizationStatement` is a Prop-valued internal statement. It isolates the localization step used in the construction of Stacks 00QV. It is derived infrastructure, not a verbatim claim of the original source. The six ring carriers `A`, `B`, `Q`, `Q'`, `L`, `C` live in the independent universes `u`, `v`, `w`, `x`, `y`, `z`, in that order.

## Hypotheses

All six rings are commutative, and `C` is a local ring. The square `A → Q`, `A → B`, `Q → Q'`, `B → Q'` is given by the algebra structures `Algebra A Q`, `Algebra A B`, `Algebra Q Q'`, `Algebra B Q'`, `Algebra A Q'`. It satisfies the scalar-tower conditions for `A → Q → Q'` and `A → B → Q'` and is a pushout (`Algebra.IsPushout A Q B Q'`). The ring `L` carries an `A`-algebra and a `Q`-algebra structure with the scalar tower `A → Q → L`. The ring `C` carries an arbitrary `Q'`-algebra structure. For arbitrary submonoids `M ⊆ Q` and `N ⊆ Q'`, `L` is a localization of `Q` at `M` and `C` is a localization of `Q'` at `N`.

The tensor product `L ⊗[A] B` uses the given `A`-algebra structures of `L` and `B`. It is a `B`-algebra through its right factor (`Algebra.TensorProduct.rightAlgebra`, a local instance in this file). The statement takes a `B`-algebra map `ψ : Q' → L ⊗[A] B` with `ψ ∘ algebraMap Q Q' = includeLeftRingHom ∘ algebraMap Q L`. That is, on `Q` the map `ψ` agrees with the canonical map `Q → L → L ⊗[A] B`, `l ↦ l ⊗ 1`. It also takes a ring map `f : L ⊗[A] B → C` with `f ∘ ψ = algebraMap Q' C`.

## Conclusion

With exactly the algebra structure `f.toAlgebra`, `C` is the localization of `L ⊗[A] B` at the prime ideal `f⁻¹(𝔪_C)`, the inverse image under `f` of the maximal ideal of `C`. Formally the conclusion is `IsLocalization.AtPrime C ((IsLocalRing.maximalIdeal C).comap f)`. It does not replace this claim by an isomorphism of rings or tensor products. Carriers are not altered. There are no finite-type, finite-presentation, flatness, injectivity, or locality assumptions on the rings other than `C`.

## Provenance

The source is Stacks Project, Lemma 10.127.11 (tag 00QV). Its property (4) asks that for `λ ≤ μ` the map `S_λ ⊗_{R_λ} R_μ → S_μ` present `S_μ` as the localization of `S_λ ⊗_{R_λ} R_μ` at a prime ideal. The proof sets `S_λ = (R_λ[x_1, …, x_n]/(f_{1,λ}, …, f_{m,λ}))_{𝔮_λ}` and leaves this property to the reader. The statement applies with `A = R_λ` and `B = R_μ`, with `Q` and `Q'` the polynomial quotients over `R_λ` and `R_μ`, with `L = S_λ` and `C = S_μ`, and with `M`, `N` the complements of `𝔮_λ`, `𝔮_μ`. Here `Q'` is the base change of `Q` along `R_λ → R_μ`, since the relations `f_{j,μ}` are images of the `f_{j,λ}`. The map `ψ` is the canonical map and `f` is the actual transition map. For a local target the contracted maximal ideal is the only prime at which `C` can be such a localization. So the conclusion is property (4) for this construction.

Remark 10.127.12 (tag 00QW) gives an example where a system with the properties of Lemma 10.127.10 fails property (4). Property (4) is therefore a feature of the chosen construction, not of every approximating system. The statement accordingly assumes the shape of that construction: `Q'` is a pushout of `Q` along `A → B`, and `L` and `C` are localizations of `Q` and `Q'`.

Registered source `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, files `00QV.html` and `00QL.html`. The abstract formulation is internal and adds no assumptions to 00QV.

## Intended proof route

The proof belongs to a separate task. Composition of pushout squares makes `L ⊗[A] B`, with `ψ.toAlgebra`, a localization of `Q'` at the image of `M`. The equation `f ∘ ψ = algebraMap Q' C` then makes `f` a map between two localizations of `Q'`. Because the target is local, this map is the localization at the contracted maximal ideal. The published theorem `Langlands.Algebra.isLocalization_atPrime_tensor_of_isPushout` in `Langlands.Algebra.PrimeLocalizationCriterion` has the same hypotheses and conclusion.

Worker 706 designed this interface. Worker 928 checked it and revised this documentation.
