# Affine stalk models from semilocal localization data

This internal development constructs the scheme maps needed for the
semilocal step in Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4.
The algebraic localization data are explicit inputs; the finite-DVR
intersection theorem supplies them separately.

Let `X` be integral and separated, let `A` be a domain with
`X.functionField` as a specified fraction field, and suppose `A` is
an `R`-algebra compatibly with a morphism `p : X ⟶ Spec R`.
`affineModelFieldEquiv` identifies the function field of `Spec A`
with that of `X`. The resulting map `affineModelGenericMap` goes from
the spectrum of the former field into `X`, and
`affineModelGenericMap_over` proves its base compatibility.

For a point `x`, a map `κ : A →+* X.presheaf.stalk x` fixing the
embeddings into the function field is automatically over `Spec R`;
this is `specMap_stalk_over_of_field_compatibility`.

If `κ` realizes the stalk as the localization of `A` at a prime `m`,
`exists_affineModel_stalk_extension` constructs an actual map from
the spectrum of the stalk of `Spec A` at `m` into `X`. It retains
the equation over the base and its agreement with the generic map.
The proof uses the canonical equivalence of two localizations,
and proves generic compatibility by uniqueness of ring homomorphisms
from a localization. All constructions work in every universe.

When `p` is locally of finite type, `affineStalkModelOfLocalizations`
takes such maps `κ` at every point of a specified set `E`, with
every maximal ideal of `A` admitting a localization presentation by one
of these stalks. It constructs `AffineStalkModel p E` itself, including
the global map `Spec A ⟶ X`. It spreads out the generic map to a
rational map, applies the stalk extension theorem at every maximal
ideal to show its domain is the whole affine spectrum, and globalizes.
The generic and base equations are retained, and the original `κ` give
the model's local maps. The supporting theorem
`rationalMapToHomOfDomainEqTop_generic` verifies the generic equation of
globalization. The model algebra's fraction-field and localization
properties remain algebraic hypotheses to be supplied by the
finite-DVR intersection construction.
