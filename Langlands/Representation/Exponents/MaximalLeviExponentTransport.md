# Moving exponents between parabolics with Levi factor `M`

Module `Langlands.Representation.Exponents.MaximalLeviExponentTransport`. Written for the
proof of Renard VII.1.3 (`MaximalLeviSupercuspidalUnitarizableConstituentStatement`), where
the exponents of the constituents of `i^G_P(ρ)` along the various represented parabolics `Q`
with Levi factor `M` are compared with the central character of the supercuspidal `ρ`.

## Provenance

Internal. These are bookkeeping lemmas for the step of Renard's proof of VII.1.3 (printed
pp.224-226, PDF pp.230-232) that moves an exponent of `r_Q(π)` attached to a double coset
`P z Q` to an exponent along the conjugate parabolic `z⁻¹Qz`, and compares its real part with
the positive cones of the parabolics. They only combine published Library results:

- `ParabolicRootPresentation.compAmbientIso`, `positiveCone_compAmbientIso` (module
  `Langlands.GroupScheme.Rational.ParabolicRootPresentationAmbientTransport`),
  `ParabolicRootPresentation.leviIsoComp`, `positiveCone_leviIsoComp` and
  `isNormalizedJacquetExponent_comp_innerIso_iso_comp_iff` (module
  `Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization`),
  `ParabolicRootPresentation.pullbackComponent` and `image_positiveCone_pullbackComponent`
  (module `Langlands.GroupScheme.Rational.ParabolicRootPresentationTransport`);
- `isGeneralizedEigencharacter_comp_mulEquiv_iff` (module
  `Langlands.Representation.Geometric.SingleBlockJacquetTransport`) and
  `normalizedGeneralizedWeight_congr` (module `Langlands.Representation.Exponents.ArbitraryParabolic`);
- `Schur.leviPoint_scalarEndomorphism` (module `Langlands.Representation.Schur.RationalPoints`);
- `splitComponentCentralCharacter` (module
  `Langlands.Representation.Exponents.CentralCharacterIdentityJacquet`) and
  `unitaryCentralCharacterOfSplitComponent` (module
  `Langlands.Representation.Exponents.FullCenterFromSplitComponent`);
- `Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff` (module
  `Langlands.Representation.Plancherel.SplitTorusNormFormula`),
  `normalizedRealPart_comp_points` (module `Langlands.Representation.Plancherel.SplitTorusRealPartLaws`),
  `pair_normalizedRealPart_tmul` (module `Langlands.Representation.Plancherel.SplitTorusRealPart`),
  `CocharacterUniformizer.latticeSection` and
  `normalizedJacquetExponent_norm_eq_one_of_mem_center` (module
  `Langlands.Representation.Exponents.CasselmanCentralDirections`).

## Group schemes and presentations (namespace `Langlands.GroupScheme`)

Throughout, `k` is a field and `A, A'` are commutative group schemes over `Spec k`.

- `splitPointsEquiv e` (definition): for `e : A ≅ A'`, the group isomorphism
  `A(k) ≃* A'(k)` given by `rationalPoints.map (CommGroupScheme.groupHom e.hom)` with inverse
  given by `e.inv`. `splitPointsEquiv_apply` and `splitPointsEquiv_toMonoidHom` unfold it.
- `rationalCharacterRestrictReal_comp_apply`: restricting a real character
  `x ∈ ℝ ⊗ X*(G)` along `f : H ⟶ G` and then along `g : K ⟶ H` equals restricting along
  `g ≫ f`. `rationalCharacterRestrictReal_id_apply`: restriction along `𝟙 G` is the identity.
  Both by induction on the tensor and `characterRestrict_comp` / `characterRestrict_id`.
- `ParabolicRootPresentation.conjugate pres z ψ e ha' he` (definition): let `q : Q ⟶ G` be a
  parabolic with Levi `lQ : M ⟶ Q`, `G` affine over the base, `pres` a root presentation of
  `(q, lQ, a)` for a split component `a : A ⟶ M`, `z ∈ G(k)`, `ψ : M ≅ M`, `e : A ≅ A'`,
  `a' : A' ⟶ M` a split component and
  `he : CommGroupScheme.groupHom e.hom ≫ a' = a ≫ ψ.hom`. The result is a root presentation
  of `(q ≫ (G.innerIso z).hom, ψ.symm.hom ≫ lQ, a')`, namely
  `((pres.compAmbientIso (G.innerIso z)).leviIsoComp ψ.symm).pullbackComponent e.symm.hom ha' _`;
  the side condition `e.inv ≫ a ≫ ψ.hom = a'` follows from `he`.
- `ParabolicRootPresentation.positiveCone_conjugate` (with `G` locally of finite type): the
  positive cone of `pres.conjugate z ψ e ha' he` is the image of `pres.positiveCone` under
  `rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv)`.

## Central characters (namespace `Langlands.Aubert.General.RepresentedParabolic`)

Here `k` is a nonarchimedean local field, `l : M ⟶ P` a rational Levi subgroup and `M(k)`
carries `leviPointTopology l hl`.

- `exists_hasCentralCharacter_of_isIrreducible l hl`: every irreducible smooth
  representation `ρ` of `M(k)` has a central character `ω : Z(M(k)) →* ℂˣ`
  (`ρ.HasCentralCharacter ω`). Proof: each central element gives an endomorphism of `ρ`, which
  is a scalar by `Schur.leviPoint_scalarEndomorphism`; the scalars are multiplicative, take
  the value `1` at `1`, and are nonzero (tested on a nonzero vector). No admissibility is
  assumed.
- `splitComponentCentralCharacter_smul` (any field, any topology on `M(k)`): if
  `ρ.HasCentralCharacter ω` and `a : A ⟶ M` is a split component, then
  `ρ(a(t)) y = (splitComponentCentralCharacter a ha ω t) • y` for `t ∈ A(k)`.
- `nonempty_unitaryCentralCharacter_of_normalizedRealPart_eq_zero l hl ha hcpt ρ hi ω hω
  hopen h0`: assume `hcpt : CenterSplitComponentCompactness M _ A a ha` (the centre of `M(k)`
  is compact modulo `a`), `ρ` irreducible with central character `ω`, the kernel of
  `ωA := splitComponentCentralCharacter a ha ω` open in `A(k)`, and
  `normalizedRealPart ωA = 0`. Then `ρ` has a unitary central character. Proof:
  `normalizedRealPart_eq_zero_iff` makes `ωA` unitary, and
  `unitaryCentralCharacterOfSplitComponent` extends unitarity to the whole centre.

## Exponents along conjugate parabolics

In this section `G(k)` has `RationalPointFamily.pointTopology`, assumed locally compact and
nonarchimedean, `k` is a Hausdorff topological field, `q : Q ⟶ G` is a parabolic with
rational Levi `lQ : M ⟶ Q` and geometric unipotent radical `rQ : U ⟶ Q` (`hmulQ`), and
`π` is a smooth representation of `G(k)`. The predicate is
`IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha π χ` for a split component `a` and
`χ : A(k) →* ℂˣ`.

- `isNormalizedJacquetExponent_comp_splitPointsEquiv_iff e hea ha ha' π χ'`: if `e : A ≅ A'`
  and `CommGroupScheme.groupHom e.hom ≫ a' = a`, then `χ' ∘ e` is an exponent for the split
  component `a` iff `χ'` is one for `a'`. Proof: `isNormalizedJacquetExponent_iff` and
  `isGeneralizedEigencharacter_comp_mulEquiv_iff` for `splitPointsEquiv e`.
- `isNormalizedJacquetExponent_conjugate_iff z ψ e he hq' hlQ' hmulQ' ha ha' π χ'`: with
  `he : CommGroupScheme.groupHom e.hom ≫ a' = a ≫ ψ.hom`, the character `χ'` is an exponent
  along `(q ≫ (G.innerIso z).hom, ψ.symm.hom ≫ lQ, rQ)` for the split component `a'` iff
  `χ' ∘ e` is an exponent along `(q, lQ, rQ)` for `a`. Proof: the previous lemma (for the
  split component `a ≫ ψ.symm.inv`) and the published
  `isNormalizedJacquetExponent_comp_innerIso_iso_comp_iff`.
- `isNormalizedJacquetExponent_congr`: if a second parabolic `(q₂, lQ₂, rQ₂)` with Levi
  source `M` satisfies `lQ ≫ q = lQ₂ ≫ q₂` and
  `SubgroupFunctor.range (rQ ≫ q) = SubgroupFunctor.range (rQ₂ ≫ q₂)`, then both have the
  same exponents for the split component `a`. Proof: `normalizedGeneralizedWeight_congr`.

With moreover `k` a nonarchimedean local field (`ValuativeRel`, `IsNonarchimedeanLocalField`):

- `normalizedRealPart_notMem_positiveCone_conjugate pres ha z ψ e ha' he χ' hopen hχ` (`G`
  locally of finite type; the Hausdorff, local compactness and nonarchimedean assumptions are
  not used): if `χ'` has open kernel and the
  normalized real part of `χ' ∘ e` is not in `pres.positiveCone`, then the normalized real
  part of `χ'` is not in `(pres.conjugate z ψ e ha' he).positiveCone`. Proof:
  `positiveCone_conjugate`, `normalizedRealPart_comp_points` and the two restriction lemmas.
- `pair_normalizedRealPart_eq_zero_of_isCentral ha π c χ hχ ν hν`: if `π` has a unitary
  central character `c` and `χ` is an exponent of `π` along `(q, lQ, rQ)` for `a`, then for
  every cocharacter `ν` of `A` with `IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ lQ ≫ q)`,
  `RealTorusSpace.pair A (normalizedRealPart χ) (1 ⊗ ν) = 0`. Proof: by
  `pair_normalizedRealPart_tmul` the pairing is `normLog` of `‖χ(ν(ϖ))‖`, evaluated at the
  lattice section point `latticeSection ν`; that point maps to the centre of `G(k)`, so
  `normalizedJacquetExponent_norm_eq_one_of_mem_center` gives norm `1`.

No maximality of `Q`, supercuspidality or admissibility enters this module.
