# KP 13.3.2, 13.3.4 and 13.2.6 for the constructed lattices `𝔤_{x,r} = Lie(𝒢_{x,r})`

## Setting

`F` is a nonarchimedean local field of either characteristic with valuation ring `𝒪[F]`, maximal
ideal `𝔪` and residue field `𝔣`, `G` an affine group over `F`,
`P : ParahoricBuildingData G` with `hP : P.SatisfiesApartmentAxioms`,
`h : P.MinimalCongruentCentralizerOrder` and `x` a point of the apartment. The objects are the
Library's constructions, used unchanged:

- `𝒢_{x,r} = P.moyPrasadModel hG hP h x r`, the smooth model chosen from
  `hG : MoyPrasadModelStatement`, with Lie lattice `𝔤_{x,r} = P.moyPrasadLie hG hP h x r` and
  `𝔤_{x,0+} = P.moyPrasadLiePlus hG hP h x 0 = ⨆_{s > 0} 𝔤_{x,s}` (`KPMoyPrasadLieLattices`);
- `L = P.lieFiltrationData hZ hU hOrder hP`, the `LieFiltrationData` built from the centralizer
  models chosen from `hZ : CentralizerModelStatement`, the root models chosen from
  `hU : AffineRootGroupModelStatement` and `hOrder : MinimalCongruentOrderStatement` (for the
  decreasing property of `z_r`), with `z_r = Lie(𝒵_r)` and `u_ψ = Lie(𝒰_ψ)`. Its `lieFiltration x r`
  is the `𝒪[F]`-span of KP 13.3.3; that it equals `𝔤_{x,r}` is the comparison asserted by the
  statement `MoyPrasadLieSpanStatement` (KP 13.3.3), which is not a premise here: the statements
  below are about `L` itself. Its real-depth lattices `lieFiltrationReal x r` (`𝔤_{x,r}` for real
  `r`, KP 13.3.1), its strict-depth lattices `lieFiltrationPlusReal x r` (`𝔤_{x,r+}`), the dual
  lattices `dualLieFiltration x r` (`𝔤*_{x,r}`), the stabilizer `filtrationStabilizer x`, the graded
  pieces `gradedLie x r` and `dualGradedLie x r` with the actions `gradedAdjoint` and
  `dualGradedAdjoint`, and the predicates `ActsTriviallyOnGraded` and `ActsTriviallyOnDualGraded`
  are those of `KPLieFiltrationDual` and `KPLieGradedAction`;
- `P_{x,0} = P.minimalCongruentMoyPrasad h x 0` and `P_{x,0+} = P.minimalCongruentMoyPrasadPlus h x 0`
  (`KPMinimalCongruentCentralizer`).

The existence statements `hG`, `hZ`, `hU`, `hOrder` enter only as the arguments of these
constructions.

Periodicity (`L.IsPeriodic`, `𝔤_{x,r+1} = 𝔪 𝔤_{x,r}`) is what makes the graded pieces KP's: under
it the real-depth family decreases, `𝔤_{x,r+} ⊆ 𝔤_{x,r}` (`lieFiltrationPlusReal_le`) and
`𝔤_{x,r+}` is the union `⋃_{s > r} 𝔤_{x,s}` (`mem_lieFiltrationPlusReal`), so that `gradedLie x r`
is `𝔤_{x,r}/𝔤_{x,r+}` for every real `r`; and `𝔪` kills both graded pieces, which gives their
residue-field structures `gradedLieResidueModule` and `dualGradedLieResidueModule`
(`KPLieGradedResidue`). The algebraic statement below asserts periodicity as part of its
conclusion and uses these structures.

## KP 13.3.2: `𝔤_{x,0}/𝔤_{x,0+} = Lie(Ḡ_x)`

`MoyPrasadReductiveQuotientLieStatement`: let `D : RelativeComponentModelData 𝒪[F] F G` have
neutral model `D.neutral = 𝒢_{x,0}` and let `Q : SpecialFibreQuotientData D` satisfy
`Q.IsReductiveQuotient`: `Q.radical ⟶ 𝒢̄_{x,0}` is the unipotent radical of the special fibre and
`Q.projection : 𝒢̄_{x,0} ⟶ Q.quotient = Ḡ_x` the quotient by it, with `Ḡ_x` connected reductive.
Then there is an `𝒪[F]`-linear equivalence

`e : 𝔤_{x,0} / 𝔤_{x,0+} ≃ Lie(Ḡ_x)` with `e (class of X) = Q.latticeReductiveLieMap X`,

where `Q.latticeReductiveLieMap : 𝔤_{x,0} → Lie(Ḡ_x)` is reduction to the special fibre followed by
the differential of the projection (`BruhatTits.IntegralModels.ReductiveQuotientLie`). Here
`𝔤_{x,0} = D.neutral.lieLattice` because `D.neutral = 𝒢_{x,0}`, and the quotient is by
`𝔤_{x,0+} ∩ 𝔤_{x,0}` (`comap` along the inclusion), which is KP's `𝔤_{x,0+}` since the lattices
`𝔤_{x,s}`, `s > 0`, lie in `𝔤_{x,0}`.

The full model of `D` plays no role. Data `D` with `D.neutral = 𝒢_{x,0}` exist: take the full and
neutral models both equal to `𝒢_{x,0}` with the identity inclusion, which is a relative identity
component by `isRelativeIdentityComponent_id_of_geometricallyConnected`, since `𝒢_{x,0}` has
geometrically connected fibres (`moyPrasadModel_hasGeometricallyConnectedFibres`).

For supplied data the Library proves `Q.reductiveQuotientLieEquiv : g_0/g_0+ ≃ Lie(Ḡ)`, where
`g_0+ = Q.positiveLieLattice` is the set of elements of `g_0` whose reduction lies in the Lie
algebra of the radical, and that `Q.latticeReductiveLieMap` is surjective. The content of the
statement for the constructed lattices is therefore that the kernel of reduction modulo the
radical is `𝔤_{x,0+}`. KP 13.3.2 derives this from `Ḡ_x = cok(𝒢̄_{x,0+} → 𝒢̄_{x,0})` (13.2.6), the
smoothness of the kernel of `𝒢_{x,0+} → 𝒢_{x,0}` on special fibres (Proposition 8.5.18), the
discussion of §2.4(a) and the inclusions `𝔪 𝔤_{x,0} ⊂ 𝔤_{x,0+} ⊂ 𝔤_{x,0}`; the Library's
`lieLatticeQuotientEquiv` is the corresponding criterion on supplied models.

## KP 13.3.4: the action of `P_{x,0}` on the graded pieces

`MoyPrasadLieGradedActionStatement`: for the constructed `L`,

- `P_{x,0} ≤ L.filtrationStabilizer x`: for `g ∈ P_{x,0}`, `Ad(g)` and `Ad(g⁻¹)` map every
  `𝔤_{x,r}`, `r ≥ 0`, into itself (hence also every real-depth lattice and every dual lattice,
  by `adjoint_mem_lieFiltrationReal` and `coadjoint_mem_dualLieFiltration`);
- `P_{x,0+}` is a normal subgroup of `P_{x,0}` (`P_{x,r}` is normal in the stabilizer of `x`, KP
  Proposition 13.2.5(2));
- for every real `r`, `P_{x,0+}` acts trivially on `𝔤_{x,r}/𝔤_{x,r+}`
  (`Ad(n) X - X ∈ 𝔤_{x,r+}` for `n ∈ P_{x,0+}` and `X ∈ 𝔤_{x,r}`) and on `𝔤*_{x,r}/𝔤*_{x,r+}`.

With these, `quotientGradedAdjoint` and `quotientDualGradedAdjoint` of `KPLieGradedAction` give
the representations of `P_{x,0}/P_{x,0+}` on the two graded pieces. KP 13.3.4 obtains them from the
extension of the conjugation action of `G` to an action of `𝒢_x^0 = 𝒢_{x,0}` on `𝒢_{x,r}`
(Corollary 2.10.10, as `G(K)_{x,r}` is normal in `G(K)_x^0` by Proposition 13.2.5), hence on
`𝔤_{x,r}` and `𝔤*_{x,r}` for all real `r`, descending to an action of the reductive quotient
`Ḡ_x` on `𝔤_{x,r}/𝔤_{x,r+}` and `𝔤*_{x,r}/𝔤*_{x,r+}`; by 13.2.6, `P_{x,0}/P_{x,0+} = Ḡ_x(𝔣)`.

## KP 13.2.6 and the algebraic action of `Ḡ_x`

`MoyPrasadReductiveQuotientGradedRepresentationStatement`: for `D` with `D.neutral = 𝒢_{x,0}` and a
reductive quotient `Q` of its special fibre as above,

- `Q.positivePoints = P_{x,0+}`: the elements of `P_{x,0} = 𝒢_{x,0}(𝒪)` whose reduction lies in
  the unipotent radical, that is the kernel of reduction to `Ḡ_x(𝔣)`, form `P_{x,0+}` (KP 13.2.6).
  With the Library's `ker_parahoricReduction`, `parahoricReduction_surjective` and
  `depthZeroQuotientEquiv` (`DepthZeroReduction`) this identifies `P_{x,0}/P_{x,0+}` with
  `Ḡ_x(𝔣)` by reduction (`Q.parahoricReduction`);
- `L` is periodic, and for every real `r` there are `𝔣`-linear coordinates
  `e : 𝔤_{x,r}/𝔤_{x,r+} ≃ 𝔣ⁿ` and a representation `ρ : Ḡ_x ⟶ GL_n` of the `𝔣`-group scheme `Ḡ_x`
  (`MatrixRepresentation Q.quotient (Fin n)`) such that for every `g ∈ P_{x,0}` and every `Y`,
  `e(Ad(g) Y) = ρ(ḡ) · e(Y)`, where `ḡ = Q.parahoricReduction g ∈ Ḡ_x(𝔣)` and `ρ(ḡ)` is its
  matrix (`MatrixRepresentation.rationalMatrix`); and the same for `𝔤*_{x,r}/𝔤*_{x,r+}` with the
  coadjoint action.

The group elements are quantified as pairs `g ∈ L.filtrationStabilizer x`,
`g' ∈ D.neutral.integralPoints` with the same image in `G(F)`. The second subgroup is `P_{x,0}`
(`moyPrasadModel_integralPoints`), and the first contains `P_{x,0}` by the stabilizer clause
asserted in `MoyPrasadLieGradedActionStatement`; under that clause every `g ∈ P_{x,0}` occurs. The
representation is given in coordinates because a `MatrixRepresentation` is a homomorphism to
`GeneralLinear.groupScheme`; any choice of coordinates gives one. The
condition concerns `ρ` only at the `𝔣`-points `Ḡ_x(𝔣)`, where it is compared with the action of
`P_{x,0}`; KP's `ρ` is the descent of the action of `𝒢_{x,0}` on `𝒢_{x,r}` to the reductive
quotient (KP 13.3.4).

## Not stated

- No particular representation `ρ` of `Ḡ_x` is constructed; the statement asserts the existence of
  one compatible with the action of `P_{x,0}` through reduction.
- This file states these results and does not prove them.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (printed page = PDF
  page − 31): Proposition 13.2.5 (p. 469); 13.2.6 and §13.3.1–13.3.4 (pp. 470–471).
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`: no entry on §13.2 or §13.3.
