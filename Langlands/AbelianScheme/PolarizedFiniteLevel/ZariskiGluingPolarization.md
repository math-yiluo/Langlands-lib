# Gluing the polarizations of rigid local data

Setting as in `ZariskiGluingAbelian`, with `B = gluedAbelian hU c hrig θ` and, from
`[QuasiSeparatedSpace S]`, the dual witness `WB = DualWitness.ofQuasiSeparated B` with
dual `D = WB.dual P`.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing`.

- `hom_restrictIso_overMap W W' h`: the restriction isomorphisms are compatible with the
  transition maps,
  `hom (restrictIso W).hom ≫ (θ W W' h).overMap = pullback.map … ≫ hom (restrictIso W').hom`.

Coherence of dual base change (generic):

- `DualWitness.baseChangeIso_cocycle`: for `b : T' ⟶ S`, `c : T ⟶ T'` and dual witnesses
  `Wb`, `Wd`, `Wc` of the base changes of `B` along `b`, `c ≫ b` and then `c`,
  `(Wb.baseChangeIso c Wc).hom ≫ Wd.map Wc (baseChangeCompIso b c B).hom ≫
  (WB.baseChangeIso (c ≫ b) Wd).inv ≫ (baseChangeCompIso b c D).hom =
  (baseChange c).map (WB.baseChangeIso b Wb).inv`. This is a rearrangement of the
  Library's `dualAbelianBaseChangeIso_comp`.
- `hom_injective'`: homomorphisms of abelian schemes are determined by `hom`.
- `hom_baseChangeCompIso_fst`: the scheme map of `baseChangeCompIso b c X` followed by
  the first projection is the canonical map of fibre products.
- `overlap_abstract`: the final step below, with the dual and its comparisons as
  variables. Stating it abstractly keeps the concrete dual out of unification, which
  otherwise times out.
- `polarization_overlap`: let `d` be a base map with `c ≫ b = d`. Let
  `κ : (baseChange d) B ≅ (baseChange c) ((baseChange b) B)` lie over the canonical maps
  of fibre products (`hκ1`, `hκ2`). Suppose it carries a map `lamd` to the dual of `Wd` to
  the pullback along `c` of a map `lamb` to the dual of `Wb` (`hlam`, the polarization
  equation of a polarized isomorphism). Then `lamd ≫ βd⁻¹` and `lamb ≫ βb⁻¹`, with values
  in the base changes of `D`, are compatible with the canonical maps of fibre products.

Gluing (section `Glue`):

- `gluedDualWitness`, `localTransport W := (c W).transport (restrictIso W) (WB.pullback P W.ι)`
  (a datum on `(baseChange W.ι).obj B`, via `Datum.transport`), and
  `localPolarization W := (localTransport W).polarization ≫ (WB.baseChangeIso P W.ι _).inv`.
- `overlapIso W W' h : PolarizedIso (localTransport W) ((localTransport W').pullback (S.homOfLE h))`,
  composed from the transport isomorphisms and `θ W W' h`; `hom_overlapIso_fst`,
  `hom_overlapIso_fst_fst`, `hom_overlapIso_snd`: it lies over the canonical maps of fibre
  products (from `hom_restrictIso_overMap`).
- `localPolarization_compat`: `polarization_overlap` applied to `overlapIso`.
- `gluedPolarization : B ⟶ D`: `gluedHom` of the local polarizations.
- `baseChange_map_gluedPolarization`, `pullbackMap_gluedPolarization W`: the pullback
  `WB.pullbackMap P W.ι (WB.pullback P W.ι) gluedPolarization` is
  `(localTransport W).polarization`.

No rigidity is needed for the compatibility: the polarized isomorphism `overlapIso` is
explicit.

## Provenance

Internal. Gluing a morphism to the dual along open covers, with the Library's
coherence of dual base change (`dualAbelianBaseChangeIso_comp`).
