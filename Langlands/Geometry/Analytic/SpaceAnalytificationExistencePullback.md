# Fibre squares of affine test points go to pullbacks

Internal conditional proof (derived provenance) of the fourth condition of `IsAnalytification`
for the glued point family of `SpaceAnalytificationExistenceConstruction`, under `AnalyticInputs`.

- `comp_ofId_eq`: the two composites `K → A → C` and `K → B → C` of algebra maps agree.
- `jointly_mono`: for a presheaf pullback `Spec C` of `u : Spec A → F` and `v : Spec B → F`,
  the analytified projections `loc f` and `loc g` are jointly monic. Proof:
  - Let `M` model `Spec A ×_{Spec K} Spec B` (`testModel`) and let `k : M → C` be the induced
    algebra map.
  - `ty k` is a monomorphism of presheaves, because `Spec C` is a pullback.
  - So `𝟙, 𝟙` is a kernel pair of `ty k`, and `affPullback` makes `𝟙, 𝟙` a kernel pair of
    `loc k`, i.e. `loc k` is monic.
  - Maps agreeing after `loc f` and `loc g` agree after `loc k`, by the pullback square of
    `M` (`affPullback`).
- `exists_local_lift`: let `a : S → Spec(A)ᵃⁿ` and `b : S → Spec(B)ᵃⁿ` be compatible over `Y`.
  Every point of `S` has an étale neighbourhood `e : W₂ → S` and a map `W₂ → Spec(C)ᵃⁿ`
  lifting `e ≫ a` and `e ≫ b`. Proof:
  1. Pull back the chart cover of `Spec(A)ᵃⁿ` along `a`, then the chart cover of
     `Spec(B)ᵃⁿ` along `b` (`base`). Points lift (`points`, `coverMap_surj`).
  2. Lift through the chart quotient square of `Spec Aᵢ ×_X Spec Aⱼ` (`QuotientData.pullback`).
  3. Lift through the analytifications of two affine fibre products (`testModel`,
     `affPullback`).
  4. Finish with the algebra map from `C` given by the presheaf pullback property of `Spec C`.
- `pointFamily_isPullback`: commutativity follows from naturality and `changeRing f x =
  changeRing g y`. The pullback property follows from
  `isPullback_of_etale_local_lifts` (module `EtaleHomGluing`), with `sheaf`, `jointly_mono`
  and `exists_local_lift`.
