# Level structures and isotriviality of étale local systems over normal schemes

This module proves the local-system form of Conrad's Corollary B.3.6 from three
prerequisite statements:
- `Langlands.FiniteOrderCongruenceDetectionStatement`: a finite-order automorphism of a
  finitely generated abelian group that is congruent to the identity modulo `n ≥ 3` is
  trivial, when `n` kills the torsion;
- `Langlands.AlgebraicGeometry.FiniteLocallyConstantRepresentableStatement`: finite
  locally constant étale sheaves of sets are represented by finite étale schemes;
- `Langlands.AlgebraicGeometry.EtaleLocalSystemIsotrivialSpreadingStatement`:
  isotriviality over `Spec 𝒪_{S,s}` spreads out to an open neighbourhood of `s`.

The module takes these as explicit hypotheses and does not import their proofs. The
Library proves all three: `Langlands.FiniteOrderCongruence.finiteOrderCongruenceDetection`,
`Langlands.AlgebraicGeometry.finiteLocallyConstantRepresentable` and
`Langlands.AlgebraicGeometry.etaleLocalSystemIsotrivialSpreading`.

The main results are `isotrivial_of_irreducible` (irreducible normal base) and
`etaleLocalSystemNormalIsotrivial_of` (the full statement
`Langlands.AlgebraicGeometry.EtaleLocalSystemNormalIsotrivialStatement`). All declarations
are in the namespace `Langlands.AlgebraicGeometry.EtaleLocalSystem`, and all schemes and
groups are in one universe `u`. The module builds on `EtaleLocalSystemDescent`
(transitions, labels, gluing, monodromy). It is an internal derived module of the proof that groups of multiplicative type over normal
bases are locally isotrivial (`multiplicativeTypeNormalIsotrivial` in `Langlands.GroupScheme.Torus.MultiplicativeTypeNormalIsotrivialProof`).

Throughout, `F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}` is an abelian presheaf on all `S`-schemes,
`M : AddCommGrpCat.{u}` is a group, and `e i : restrict (f i) F ≅ constant (X i) M` are
trivializations over morphisms `f i : X i ⟶ S` (`i : ι`, `ι : Type u`).

## 1. Level-`n` frames

### Definitions

- `nsmulRange M n`: the subgroup `n M`. `reduce M n : M →+ M ⧸ n M` is the quotient map.
- `Frames M n`: the *level-`n` frames* of `M`. These are homomorphisms
  `φ : M →+ M ⧸ n M` of the form `reduce ∘ α` for some automorphism `α : M ≃+ M`.
- `Frames.comp φ γ`: precomposition of a frame with an automorphism `γ`.
- `Frames.rep r`: a chosen automorphism `α` with `r = reduce ∘ α` (`Frames.rep_spec`).

### Statements

- `finite_quotient_nsmulRange`, `finite_frames`: for finitely generated `M` and `n ≠ 0`,
  `M ⧸ n M` and `Frames M n` are finite.
- `Frames.comp_val`, `Frames.comp_comp`, `Frames.comp_refl`: action lemmas.
- `congr_of_frames_eq`: two automorphisms with the same frame differ by an automorphism
  congruent to the identity modulo `n`.
- `exists_eq_add_nsmul_of_frames`: if `s = r.comp τ.symm`, then
  `rep s ∘ τ ∘ (rep r)⁻¹` is congruent to the identity modulo `n`.
- `isLocallyConstant_labelEquiv`, `labelEquiv_trans`, `labelEquiv_refl`,
  `labelEquiv_transition_comp`: for finitely generated `M`, the label of an automorphism of
  a constant sheaf is a locally constant automorphism-valued function, compatible with
  composition and pullback.

## 2. The frames presheaf

For `U` over `S`, write `U ×_S X i` for `pullback U.hom (f i)`, and
`(U ×_S X i) ×_U (U ×_S X j)` for the overlap.

### Definitions

- `overlapLabel e U i j z : M ≃+ M`: the label at a point `z` of the overlap of the
  transition from `e i` to `e j`.
- `FramesFamily n e U`: the *level-`n` frames of `F` over `U`*. These are families
  `g i : U ×_S X i → Frames M n` of locally constant functions such that, at every point `z`
  of every overlap, `g j (q₂ z) = (g i (q₁ z)).comp (overlapLabel e U i j z).symm`. Here
  `q₁`, `q₂` are the two projections.
- `pullbackMapOver φ i`, `overlapMap φ i j`: the maps induced by `φ : U' ⟶ U` on the
  pullbacks and on the overlaps.
- `FramesFamily.map φ`: restriction of frame families along `φ`.
- `framesPresheaf n e : (Over S)ᵒᵖ ⥤ Type u`: the presheaf `U ↦ FramesFamily n e U`.
- For `V` over `X k`: `secPt k V : V.left ⟶ V ×_S X k` is the diagonal section.
  `tlabV e k V i` is the label of the transition from `e k` to `e i` on `V ×_S X i`.
  `familyOfLocallyConstant n e k V` sends a locally constant frame on `V` to a frame
  family. `locallyConstantOfFamily n e k V` restricts a frame family along `secPt`.
- `framesPresheafRestrictIso n e k`: with `Frames M n` given the discrete topology, an
  isomorphism of presheaves on `Over (X k)`:
  `(Over.map (f k)).op ⋙ framesPresheaf n e ≅
    (Over.forget (X k)).op ⋙ continuousMapPresheaf (Frames M n)`.
- `pullbackContinuousMapPresheaf T i`: continuous maps from `U ×_S X i` to `T`, as a
  presheaf on `Over S`. It is `(Over.pullback (f i)).op ⋙ (Over.forget (X i)).op ⋙
  continuousMapPresheaf T`.

### Statements

- `overlap_condition`, `overlapLabel_map` (overlap labels are natural in `U`),
  `pullbackMapOver_fst/_snd/_id/_comp`, `overlapMap_fst/_snd`, `trans_cond`, `secPt_fst`,
  `secPt_snd`, `tlabV_secPt`, `secPt_pullbackMapOver`: bookkeeping.
- `locallyConstantOfFamily_familyOfLocallyConstant` and
  `familyOfLocallyConstant_locallyConstantOfFamily`: the two constructions are inverse
  bijections. So over each member `X k` the frames presheaf is the constant presheaf of the
  finite set `Frames M n` (`framesPresheafRestrictIso`).
- `exists_mem_sieve_apply_eq`: every point of `U.left` lifts along some arrow of a covering
  sieve of `U` for `Scheme.etaleTopology.over S`.
- `exists_overlapMap_eq_of_apply_eq`: a point of the overlap over `U` that lies over the
  image of `h : W ⟶ U` comes from the overlap over `W`.
- `isSheaf_pullbackContinuousMapPresheaf`: `pullbackContinuousMapPresheaf T i` is a sheaf
  for `Scheme.etaleTopology.over S`.
- `isSheaf_framesPresheaf n e`: `framesPresheaf n e` is a sheaf of sets for
  `Scheme.etaleTopology.over S` (`Presieve.IsSheaf`).

## 3. Level covers

### Definitions

- `toRestrict q ef`: a trivialization of `F` along `a ≫ q`, read as a trivialization of
  `restrict q F` along `a`. The two presheaves agree definitionally.
- For a frame family `g : FramesFamily n e U`, an index `i` and a frame `r`:
  - `frameLocus n e g i r`: the open subset of `U ×_S X i` where `g i = r`;
  - `levelMap n e g i r`: its open subscheme, mapped to `U.left`;
  - `levelTriv n e g i r`: the trivialization of `restrict U.hom F` over this member. It is
    `e i` pulled back, then changed by `Frames.rep r` (`constantCongr`);
  - `levelLift`: the map from the overlap of two members to the overlap over `U`.

### Statements

- `transition_toRestrict`, `transition_congrIso_left`, `transition_congrIso_right`:
  transitions are unchanged by these reinterpretations.
- `levelMap_cond`, `levelLift_frames`, `label_levelTriv`: the transition from member
  `(i, r)` to member `(j, s)` has label `rep s ∘ τ ∘ (rep r)⁻¹`, where `τ` is the overlap
  label over `U`, and `s = r.comp τ.symm`.
- `exists_level_cover hcov g` (**a frame family gives a level-`n` structure**): if the
  `f i` are étale and jointly surjective, then a frame family `g` over `U` gives an étale
  cover `z k : Z k ⟶ U.left` (`k : κ`, `κ : Type u`), jointly surjective. It carries
  trivializations `E k : restrict (z k) (restrict U.hom F) ≅ constant (Z k) M` whose
  transitions on `Z k ×_{U.left} Z l` have all labels congruent to the identity modulo `n`.

## 4. Isotriviality

- `exists_pos_nsmul_torsion_eq_zero M`: a finitely generated abelian group has a positive
  integer `N` killing all its torsion elements.
- `isotrivial_of_irreducible hFOC hRep hS hF` (**irreducible normal base**): let `S` be
  irreducible with `∀ x, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed
  (S.presheaf.stalk x)`, and let `IsFinitelyGeneratedLocallyConstant.{u, u} F`. Assume
  `hFOC : FiniteOrderCongruenceDetectionStatement.{u}` and
  `hRep : FiniteLocallyConstantRepresentableStatement.{u}`. Then there are a finite, étale,
  surjective `p : S' ⟶ S` and a finitely generated `M` with
  `Nonempty (restrict p F ≅ constant S' M)`.
- `stalk_isDomain_isIntegrallyClosed_spec_stalk hS s`: if the stalks of `S` are
  integrally closed domains, so are the stalks of `Spec (S.presheaf.stalk s)`.
- `etaleLocalSystemNormalIsotrivial_of hFOC hRep hSpread`: the three prerequisite
  statements imply `EtaleLocalSystemNormalIsotrivialStatement.{u}`.

## Correspondence with the source

Brian Conrad, *Reductive group schemes* (2014), `conrad-2014-reductive-group-schemes`,
proof of Corollary B.3.6, pp.293-295. Conrad reduces to `S` irreducible, takes a common
group `M` (Library: `exists_common_model`), and represents `F/nF` by a finite étale
`S`-group `G_n`. He splits `G_n` over a connected finite étale cover `S'` (irreducible since
`S` is normal) and shows that `F|S'` is constant once `F/nF` is constant, for `n ≥ 3`
divisible by the exponent of `M_tor`.

This module follows the same strategy with one change. Instead of `F/nF`, it represents
the sheaf of level-`n` frames of `F` (`framesPresheaf`), which is locally the constant sheaf
of the finite set `Frames M n`. The representing finite étale `W ⟶ S` carries a universal
frame, so no splitting cover and no Galois closure is needed. A connected component of `W`
plays the role of Conrad's connected cover `S'`. It is open and irreducible, because `W` is
étale over an irreducible normal scheme
(`EtaleNormalLocallyIrreducible.isIrreducible_connectedComponent_of_etale`). It is also
closed, so it is finite étale over `S`, and surjective because `S` is connected. Over it,
the universal frame gives transitions congruent to the identity modulo `n`
(`exists_level_cover`), and Conrad's argument "F is constant once F/nF is" is
`nonempty_iso_constant_of_level_of_irreducible` from `EtaleLocalSystemDescent`.

Part 1 of the target (Zariski-local isotriviality for arbitrary normal `S`) follows
Conrad's reduction on p.293: each `Spec 𝒪_{S,s}` is normal and irreducible, and
isotriviality over it spreads out. The spreading out is the hypothesis `hSpread`.

## Proofs

**Frames.** `M ⧸ n M` is finitely generated and killed by `n`, hence finite
(`Module.finite_of_fg_torsion`). A frame is determined by its values on a finite
generating set, so `Frames M n` is finite. `exists_eq_add_nsmul_of_frames` computes
`reduce (rep s (τ ((rep r)⁻¹ m))) = reduce m` from `s = r.comp τ.symm` and reads off the
difference in `n M` (`QuotientAddGroup.eq`).

**Frames presheaf.** The maps `FramesFamily.map` respect identities and composition
because `pullbackMapOver` does, and the overlap condition is preserved by
`overlapLabel_map`. For `V` over `X k`, a frame family `g` over `(Over.map (f k)).obj V` is
determined by the values of `g k` along the diagonal section `secPt`. Conversely, a locally constant frame
`lf` on `V` extends to the family `z ↦ lf(fst z) ∘ (tlabV e k V i z)⁻¹`. Its overlap
condition is the cocycle identity `transition_trans`. The round trip on `lf` uses that the
diagonal transition is trivial (`tlabV_secPt`, `transition_self`). The round trip on `g`
applies the overlap condition of `g` at the point `(secPt (fst z), z)` of the overlap of
`k` and `i`. Naturality is `secPt_pullbackMapOver`. Locally constant maps to a discrete
space are the continuous maps (`IsLocallyConstant.iff_continuous`).

**Sheaf property.** `pullbackContinuousMapPresheaf T i` is a sheaf. Indeed,
`continuousMapPresheaf T` is an fpqc sheaf (Mathlib), hence an étale sheaf, and
`Over.forget` and `Over.pullback (f i)` are continuous functors for the relevant
topologies (`Functor.op_comp_isSheaf_of_isSheaf`). Given a covering sieve and a compatible
family of frame families, each component `i` is a compatible family of continuous maps.
It has a unique amalgamation `c i`. The family `(c i)` satisfies the overlap condition: a
point `w` of the overlap over `U` lies, by `exists_mem_sieve_apply_eq` and
`exists_overlapMap_eq_of_apply_eq`, in the image of the overlap over some arrow `h` of the
sieve. There the condition holds for the given family, and `overlapLabel_map` transports
it. Uniqueness follows componentwise from uniqueness of the amalgamations `c i`.

**Level cover.** Index the cover by pairs `(i, r)`. The member is the open locus where
`g i = r`, mapped to `U.left` through `U ×_S X i`. It is étale as an open immersion
followed by a base change of `f i`. Every point of `U.left` lies under a point of some
`U ×_S X i` (`exists_preimage_pullback`), which lies in the locus of its own frame value.
The label of a transition is computed by `transition_toRestrict`,
`constantCongr_transition`, `transition_trans_constantCongr`, the `congrIso` lemmas,
`transition_fromRestrict` and `labelEquiv_transition_comp`. The overlap condition of `g`
gives `s = r.comp τ.symm` (`levelLift_frames`), and `exists_eq_add_nsmul_of_frames`
finishes the proof.

**Torsion exponent.** The torsion subgroup of a finitely generated abelian group is
finitely generated (`IsNoetherian`), torsion, hence finite
(`AddCommGroup.finite_of_fg_isAddTorsion`). Its exponent is positive and kills every torsion
element.

**Irreducible base.** `exists_common_model` gives `M` and a trivializing étale cover. Take
`N` from `exists_pos_nsmul_torsion_eq_zero` and `n = 3 * N`. The frames presheaf is an
étale sheaf and locally isomorphic to the constant sheaf of the finite set `Frames M n`, so
`hRep` gives a finite étale `q : W ⟶ S` representing it. `W` is nonempty: a constant frame
over a member `X i₀` gives a morphism to `Over.mk q`. Take the connected component `W'` of
a point of `W`. As above it is open, irreducible, closed and finite étale surjective over
`S`. Its stalks are integrally closed domains
(`EtaleNormalLocallyIrreducible.stalk_isDomain_isIntegrallyClosed_of_etale`). Restrict the
universal element of the representation to `W'`. `exists_level_cover` then gives a level-`n`
structure on `restrict (W'.ι ≫ q) F`, which is an étale sheaf (`isEtaleSheaf_restrict`).
`nonempty_iso_constant_of_level_of_irreducible` makes it constant.

**Full statement.** Part 2 is `isotrivial_of_irreducible`. For part 1 and a point `s`,
`Spec (S.presheaf.stalk s)` is irreducible (the stalk is a domain). Its stalks are
localizations of the stalk at primes, hence integrally closed domains
(`isIntegrallyClosed_of_isLocalization`, `Spec.stalkIso`). The restriction of `F` along
`S.fromSpecStalk s` is again a finitely generated local system
(`isFinitelyGeneratedLocallyConstant_restrict`). So `isotrivial_of_irreducible` makes it
isotrivial over `Spec 𝒪_{S,s}`, and `hSpread` spreads this to an open neighbourhood of `s`.
