# Transport of morphisms between pullbacks along further pullbacks

Module `Langlands.AlgebraicGeometry.Modules.PullbackTransport`, namespace
`Langlands.Scheme.Modules`.

This module is internal infrastructure for the proof of
`Langlands.AbelianScheme.MumfordFiniteWeilAlternationStatement` (see
`Langlands.AlgebraicGeometry.Picard.MumfordAlternationTrivialization`). It contains no source
statement. It provides a calculus for morphisms between pullbacks `u^* C ⟶ v^* D` of modules
on a scheme `Z`. Such morphisms are pulled back along a further map `g` and re-expressed as
morphisms between pullbacks along prescribed composites. All results are proved; none is
assumed.

## Definitions

- `compIso g u u' h C : g^* (u^* C) ≅ u'^* C` for an equation `h : g ≫ u = u'`. It is the
  Library's composition isomorphism `pullbackComp g u` followed by `pullbackCongr h`. Its
  `hom` is the Library's `compHom g u u' h C`. The definition and
  `compIso_hom` reuse `UnitCocycleDescentUniqueness.compIso` and its
  published hom identity, retaining the same definitional comparison.
- `transport g hu hv φ : u'^* C ⟶ v'^* D` for `φ : u^* C ⟶ v^* D`, `hu : g ≫ u = u'` and
  `hv : g ≫ v = v'`. It is `(compIso g u u' hu C).inv ≫ g^* φ ≫ (compIso g v v' hv D).hom`.
- `unitTransfer a b : a^* O_Z ⟶ b^* O_Z` for `a b : X ⟶ Z`. It is
  `(pullbackUnitIso a).hom ≫ (pullbackUnitIso b).inv`, the canonical identification of both
  pullbacks of the structure sheaf with `O_X`. It is an isomorphism (instance).
- `sectionMap L : ε^* O_X ⟶ ε^* L.carrier` for a rigidified module `L` along `ε : S ⟶ X`. It
  is `(pullbackUnitIso ε).hom ≫ L.rigidification.hom`. It is an isomorphism (instance).

## Results

Transport calculus (section `Transport`):

- `transport_id`: transport of an identity is the identity.
- `transport_comp`: transport preserves composition.
- `transport_congr`: transport along equal maps `g = g'` agrees.
- `transport_smul`: `transport g hu hv (r • φ) = g.appTop r • transport g hu hv φ` for a global
  function `r` on `Y`.
- `transport_isIso`: transport of an isomorphism is an isomorphism (instance).
- `transport_transport`: transport along `g'` of a transport along `g` is transport along
  `g' ≫ g`. `transport_transport_eq` is the same with `g' ≫ g` replaced by any `k` with
  `g' ≫ g = k`. The proof uses the Library's associativity `compHom_assoc` and the naturality
  of `pullbackComp`.

Unit comparisons (section `Unit`):

- `unitTransfer_self`: `unitTransfer a a = 𝟙`; `unitTransfer_comp`: the comparisons compose.
- `compIso_unit`: `compIso g a a' h O_Z` is compatible with the unit isomorphisms:
  `(compIso g a a' h O).hom ≫ (pullbackUnitIso a').hom =
  g^* (pullbackUnitIso a).hom ≫ (pullbackUnitIso g).hom`. The proof substitutes `h` and uses
  the Library's `pullbackUnitComposition`.
- `transport_unitTransfer`: `transport g ha hb (unitTransfer a b) = unitTransfer a' b'`.

Constancy (section `Constancy`):

- `exists_transport_eq_smul`: let `pr : Y ⟶ X` be such that `pr.appTop` is an isomorphism (all
  global functions on `Y` come from `X`). Let `φ, ψ : u^* C ⟶ v^* D` with `ψ` an isomorphism and
  `u^* C` locally free of rank one. Then there is one `c : Γ(X, ⊤)` such that for every section
  `s` of `pr` (`s ≫ pr = 𝟙 X`) and all `hu : s ≫ u = u'`, `hv : s ≫ v = v'`,
  `transport s hu hv φ = c • transport s hu hv ψ`.

  Proof. The endomorphism `φ ≫ ψ⁻¹` of the rank-one module `u^* C` is `d • 𝟙` for a global
  function `d` on `Y` (the Library's `exists_eq_smul_id_of_isLocallyFreeRankOne`), so
  `φ = d • ψ`. Take `c = (pr.appTop)⁻¹ d`. By `transport_smul` it remains to see
  `s.appTop d = c`. This holds because `d = pr.appTop c` and `s ≫ pr = 𝟙`.

Equal composites (section `EqualComposite`):

- `equalCompositeIso_hom_compIso`: compatibility of the Library's `equalCompositeIso p a b h`
  for `q^* C` with the composition isomorphisms for `p ≫ q`. Both sides are rewritten with
  `compHom_assoc` (the Library's `equalCompositeIso_hom_eq_compHom`).
- `equalCompositeUnitAut_eq_refl_of_transport`: let `α' : (p ≫ q)^* C ⟶ m^* O_Z` be an
  isomorphism. Let `a, b : U ⟶ X` satisfy `a ≫ p = b ≫ p`, and let both `a ≫ (p ≫ q)` and
  `b ≫ (p ≫ q)` equal `w`. If `transport a ha ha' α' ≫ unitTransfer a' b' = transport b hb hb' α'`,
  then the Library's `equalCompositeUnitAut p a b h α` is `Iso.refl`. Here `α` is the
  trivialization `p^* (q^* C) ≅ O_X` given by
  `compIso p q (p ≫ q) rfl C ≪≫ asIso α' ≪≫ pullbackUnitIso m`. The proof rewrites the pullbacks
  of `α` along `a` and `b` as transports of `α'` (via `compIso_unit`) and uses
  `equalCompositeIso_hom_compIso`.

Rigidified modules (section `Rigidified`), for a rigidified module `L` along `ε : S ⟶ X` and
a commutative square `ε' ≫ f = g ≫ ε` with `ε' : S' ⟶ X'`:

- `pullback_rigidification_compIso`: the rigidification of the pulled-back rigidified module
  `(RigidifiedModule.pullback f g comm).obj L`, followed by `compIso ε' f w`, equals
  `(pullbackUnitIso w).inv ≫ transport g hg hg (sectionMap L)`.
- `transport_sectionMap_comp_of_hom`: let `Φ : f₁^* L ⟶ f₂^* L` be compatible with the
  rigidifications of the two pulled-back rigidified modules (hypothesis `hΦ`). Then
  `transport g₁ (sectionMap L) ≫ transport ε' Φ = unitTransfer w₁ w₂ ≫ transport g₂ (sectionMap L)`.
- `transport_sectionMap_comp_of_hom_comp`: the same identity transported further along a map
  `k : V ⟶ S'`. It is derived from the previous lemma with `transport_comp`,
  `transport_transport_eq` and `transport_unitTransfer`.
- `transport_sectionMap_comp_of_trivial`: let `Φ : f^* L ⟶ O_{X'}` be compatible with the
  rigidifications, the target carrying the trivial rigidification `(pullbackUnitIso ε').inv`.
  Then `transport g (sectionMap L) ≫ transport ε' (Φ ≫ (pullbackUnitIso f).inv) = 𝟙`.

All proofs are diagram chases with the Library's `compHom_assoc`, `pullbackUnitComposition`
and the definition of `RigidifiedModule.squarePullbackIso`.
