# Projectivity of flat algebras with geometrically integral fibres

`Langlands.CommutativeAlgebra.integralFibreProjectivity` proves
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement.{u}`, which is Stacks Project
Lemma 38.9.3 (Tag 05FT). Let `R` and `S` be commutative rings in universe `u`, with `S` a
finitely presented, flat `R`-algebra such that
`Spec.map (CommRingCat.ofHom (algebraMap R S))` is geometrically integral. Then `S` is a
projective `R`-module.

## Route

The Stacks proof descends to a Noetherian base. That requires the geometrically integral fibre
condition to spread out over a Noetherian model, which uses EGA IV constructibility results that
are not available. The implemented proof avoids this step. Every Noetherian argument takes place
on a model of the algebra, and the fibre condition is used only at points of the original base.

1. **Fibres.** `isDomain_tensor_of_geometricallyIntegral`
   (`IntegralFibre/GeometricallyIntegral`) shows that `K ⊗[R] S` is a domain for every field `K`
   over `R`.
2. **Smooth cover.** `exists_smooth_free_cover` (`IntegralFibre/SmoothCover`) produces
   `s : Fin m → S` with the following properties. Each `Localization.Away (s i)` is smooth over
   `R` with free differentials, and `R → ∏ i, Localization.Away (s i)` is faithfully flat. It uses
   generic smoothness of the fibres, `exists_mem_smoothLocus_comap_eq`
   (`IntegralFibre/GenericSmoothness`).
3. **Local splitting on each factor.** `IntegralFibre.locallySplit_away` (`IntegralFibre/AwaySplit`)
   shows that `B ⊗[R] S` is locally split over `B = Localization.Away (s i)`. The diagonal gives a
   section in the smooth locus. Truncated Taylor expansion along it is an isomorphism
   (`IntegralFibre/Taylor`, `IntegralFibre/TaylorSmooth`). The Taylor coefficients are the
   splitting functionals. That they detect elements is proved on a Noetherian model
   (`IntegralFibre/Model`, `IntegralFibre/Transfer`, `IntegralFibre/ModelSplit`), using Krull's
   intersection theorem and a purity lemma (`IntegralFibre/Purity`). The purity lemma needs only
   that the fibres over points of `B` are domains.
4. **Product.** `locallySplit_pi` (`LocallySplit/Pi`) gives local splitting over the product
   ring.
5. **Descent.** `projective_of_locallySplit_baseChange` (`LocallySplit/Projective`, with
   `LocallySplit/Domination`) descends projectivity of countably generated flat modules along
   faithfully flat maps. Countable generation is `exists_countable_span_eq_top`
   (`IntegralFibre/Countable`).

## Proof in Lean

After introducing the hypotheses, the proof obtains `hS` from step 1. It then applies
`projective_of_forall_locallySplit_away` (`IntegralFibre/Assembly`, by Worker 928) to the family
of local-splitting statements `IntegralFibre.locallySplit_away s hS`. That assembly lemma
carries out steps 2, 4 and 5: it takes the cover from `exists_smooth_free_cover`, combines the
factors with `locallySplit_pi`, and applies `projective_of_locallySplit_baseChange` with
`R' = ∀ i, Localization.Away (s i)` together with `exists_countable_span_eq_top`.

## Provenance

The route is project-internal, by Worker 281 and Worker 928. The descent theorem, the fibre
translation, countable generation, generic smoothness, the product lemma, the cover and the
assembly lemma are by Worker 928. The Taylor, purity, model and local-splitting modules are by
Worker 281. The original result and its Stacks proof are in the registered source
`stacks-integral-fibre-projectivity-05ft-2026-11-02` (Tags 05FT and 05FS). Stacks Remark 05FU
sketches the Raynaud–Gruson argument for smooth algebras, which the route adapts.
