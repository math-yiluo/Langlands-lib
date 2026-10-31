# Actual highest mirabolic layer

`Langlands.Derivative.MirabolicHighestLayerStatement.{uF,uV} F T` is a
proposition definition. It specifies a nonzero actual highest layer, a full
subrepresentation-lattice comparison with its ambient interval, and
homogeneity if and only if essentiality. It supplies no Lean proof.

## Exact scope

The outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`. The supplied topology `T.topology` is installed.
The field universe `uF` and representation-carrier universe `uV` are independent.
For every

- `ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`,
- natural number `N`,
- actual smooth representation
  `A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear.mirabolic N F.Carrier)`,
- order `k` with `hk : 0 < k ∧ k ≤ N + 1`,

the only further hypotheses are `Nontrivial A` and `k = level T ψ A`.
The character type itself includes continuity, unit-circle values and
nontriviality. The conclusion is the existence of one
`U : Subrepresentation A.representation` with all three properties:

1. `U ≠ ⊥`.
2. `Nonempty (Subrepresentation
   ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).representation ≃o Set.Iic U)`.
3. `IsHomogeneous T ψ A ↔
   ∀ S : Subrepresentation A.representation, S ≠ ⊥ → U ⊓ S ≠ ⊥`.

The same `U` occurs in each property. It is an actual invariant complex
subspace of the supplied representation `A`. An element of `Set.Iic U`
is an actual ambient invariant subspace together with a proof that it lies
in `U`; its bottom and binary intersections are inherited from the ambient
lattice. The order isomorphism covers the **entire** subrepresentation lattice
of the actual quotient derivative and the **entire** ambient interval below
`U`. It is stronger than a lattice embedding or a choice of an unrelated
isomorphic representation. `Nonempty` makes existence of that order
isomorphism Prop-valued; no isomorphism is supplied as a hypothesis.
The last property is essentiality in the ambient representation: the chosen
layer intersects every nonbottom actual ambient invariant subspace nontrivially.

No finite-length, Artinian, irreducibility, admissibility, exactness, detection,
adjunction, filtration, plus-model, supplied-layer, lattice-isomorphism or
classification hypothesis occurs. There is no strong-indecomposability
assertion or hypothesis, and no ordered-product conclusion.

## Ranks, quotients and zero convention

`GeneralLinear.mirabolic N F.Carrier` is the actual matrix subgroup
`P_(N+1)`. `mirabolicDerivativeOfOrder T ψ N k hk` lands in
`GL_(N+1-k)`. It transports along
`N = (N+1-k)+(k-1)` and then applies the published
`mirabolicDerivative T ψ (N+1-k) (k-1)`: first `k-1` changing-rank
`Φ⁻` steps, then `Ψ⁻`. These are the actual character-localized quotient
functors of `MirabolicMinus`, with their determinant normalization.
Localization takes the quotient by the span of
`ρ u v - (θ u : ℂ) • v`, followed by the descended action. The normalized
minus action twists by the explicit residue-normalized `|det|^(-1/2)`;
the twist retains the quotient carrier.

Order one is `Mirabolic.psiMinus T N`. This includes `N=0`, `k=1`,
the actual `P₁ → GL₀` boundary. The top order `k=N+1` is included and
also lands in `GL₀`. There is no extra rank-positivity restriction,
fixed-rank replacement, derivative of invalid order or order-zero derivative
in this proposition.

The imported `level T ψ A` is the finite maximum of the valid nonzero
derivative orders in `1,…,N+1`, implemented by
`Nat.findGreatest (HasNonzeroDerivative T ψ A) (N+1)`. Its explicit default
is zero when no such derivative is nontrivial. This statement only concerns
a supplied positive order equal to that level; it does not prove that every
nonzero `A` has positive level. `IsHomogeneous T ψ A` says that every
nonbottom actual invariant subspace, equipped with
`SmoothRep.subrepresentation A S`, has the ambient level. That representation
uses the restricted action on `S.toSubmodule`, with smoothness transferred
along the actual injective inclusion.

## Original-source rationale and remaining analytic proof

This existential interface is derived from the following registered originals;
it is not a verbatim theorem statement from either article.

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)* (1980), §5.1(1) iff (2),
  printed p.187, one-based PDF page 24.
  Literature ID `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Retained original:
  `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I* (1977), §3.3(a), printed p.451, PDF page 12,
  and the derivative/filtration construction of §3.5, printed p.452,
  PDF page 13. Literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

Worker 658 read and visually checked these three original pages on
2026-10-31 and verified both complete PDF fingerprints against the registered
sources. The literature index was checked; no source-specific errata note
was present in the project or public `notes/errata` locations.

With source rank `n=N+1`, Bernstein–Zelevinsky §3.5 filters a representation
by actual subrepresentations. At highest derivative order `k`, the relevant
layer is `(Φ⁺)^(k-1) Ψ⁺(A^(k))` inside `A`. Its realization as an actual
ambient subrepresentation motivates the existential `U`. Section 3.3(a)
states the full submodule-lattice comparison for `Φ⁺` and analogously for
`Ψ⁺`, using equivalence onto a subobject-closed essential image. Iteration
and transport through the actual embedded layer motivate the order
isomorphism to `Set.Iic U`. Zelevinsky §5.1(1) iff (2) identifies homogeneity
with essentiality of this same layer. Its argument examines each actual
submodule's intersection with the layer and its highest derivative.
The abstract existential packaging, the `Nonempty` wrapper, the explicit
valid-order proof, independent Lean universes and zero-default convention
are internal interface choices.

The analytic proof must construct the genuine plus layer and its embedding
in `A`, compare the determinant normalization to the source Haar-modulus
normalization, prove nonzeroness, prove the full submodule-lattice comparison,
and establish the homogeneity/essentiality equivalence. All remain substantive
proof obligations; none is supplied or assumed by this proposition definition.
The nearby Zelevinsky §5.4 strong-indecomposability conclusion and subsequent
classification results are not inputs to this prerequisite. Source references
do not supply Lean proofs. A constructor for a plus or minus functor alone
also does not establish adjunction, exactness, filtration or this endpoint.

## Authorship and controlled boundaries

Worker 440 authored the reused statement draft and prepared its contract.
Worker 658 completed the companion, source verification and dependency audit.
Workers 864/700 supplied parent planning; their generic lattice unit is separate
and no private draft from it is used here. The public generic lattice statement
and its exact proof task `a2baddab-056b-4503-865e-74d58ecb3812` are not
duplicated or assumed proved.

This statement does not resume or replace the operator-paused minus exactness
task `b65bc667-6951-4bd5-82af-10fb7046df7f` or Worker 127's controls.
Worker 157's finite-length scope
`0717fd42-d711-4f42-8269-f6ae4c8da1e9`, Worker 357's
mixed-product/restriction/Leibniz and raw tensor/partial-derivative scope,
and Worker 288's order-zero adapter remain separately controlled.
Any later substantial split must first search and coordinate the existing
plus-functor, adjunction, exactness and filtration owners. Lower statements
must be public before their exact proof successors are published.

## Validation and dependency audit

The statement compiled and was inspected in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` on 2026-10-31, diagnostic
`170fb8f4-a0fe-4b40-b4a8-c4b1750d4b3d`: successful Lake build,
zero errors and warnings, `statement_returns_prop = true`, and level
parameters exactly `[uF,uV]`. The only foundational axioms reported were
`propext`, `Classical.choice` and `Quot.sound`. This development diagnostic
is neither independent acceptance nor a proof of the proposition.

The sole direct project import is
`Langlands.Representation.Derivative.Homogeneity`.
The following audit uses public Library commit
`42ebad9dec7efaf48307e0b6085168e104486dfb`. Recursive native import
enumeration found 54 existing project modules, including `Homogeneity`;
the new statement makes 55 project modules in the complete closure.
Every imported Lean file and its same-stem Markdown was compared byte for
byte with that public tree. All 108 comparisons matched, and this candidate
changes none of those pairs.

For declaration-level independence, a private diagnostic traversed
`ConstantInfo.getUsedConstantsAsSet` recursively from the new definition,
including types, opaque proof values, constructors and recursors. It visited
26,851 constants in total and 272 project constants in 25 project modules,
including the new root. Diagnostic
`9b1fe246-e923-43e6-9d68-bfdf9e0c8a27` completed successfully with no errors
or warnings. No project axiom was present. The complete project constant
list appears below, including generated and private names rather than
silently dropping proof dependencies.

The mathematical inputs to the **definition of this statement** are actual
field/topological data, matrix mirabolic groups, smooth representations and
subrepresentations, actual localized quotient minus functors and determinant
twists, iteration with rank transport, the finite-maximum level, and actual
subrepresentation homogeneity. Their closure contains no strong
indecomposability, ordered-socle, segment classification, segment product,
head/socle existence, exhaustion or other excluded consumer conclusion.
No derivative detection theorem, plus functor, adjunction, filtration,
minus exactness theorem or generic lattice theorem is imported or used.
The abstract proposition declarations in imported statement modules do not
become assumptions or proofs of their mathematical contents.

The full import closure is broader than the actual constant closure:
for example it loads elementary Whittaker-character, matrix-coefficient and
twist/admissibility infrastructure. Those modules introduce no excluded
classification or consumer dependency. No new theorem-valued parameter
is added to the telescope to compensate for an absent analytic proof.
The future exact proof must make a fresh mathematical proof-dependency and
complete project import/declaration audit of its additional prerequisites.

### Complete imported project pairs

The dependency column lists project imports by row number. Imports from the
pinned Lean/Mathlib environment are outside this project-module table. Full
SHA256 fingerprints are given for both unchanged public files in each pair.

| ID | Module | Project imports | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- | --- | --- |
| 1 | `Langlands.Group.GL.Basic` | — | `d7867286deba424f8f285ea9712b328b762954307fb31c69d4235c8a7b1f29e1` | `b4831fd91123aea6efd64c1da3dbddc32f0c71c9b3f31c7eaed176e7dc9a3d32` |
| 2 | `Langlands.Group.GL.Mirabolic` | 9 | `358505b5bb7db8a3c7d1ae8175bddb476a7cba621a8407f4180fc1834160a7a9` | `b7549d1b35fa084279ceafc6dedb466a4914fd9b21434b0cd6a0e3afc03e0399` |
| 3 | `Langlands.Group.GL.MirabolicRadical` | 2, 8 | `b75812e0f24586a5b6365b6282088886d7f359fcd5bef368136946b5b6137eda` | `183e771f6e76b3094d607822e15effb869cd80bc1666c7e76962e86c27f58eed` |
| 4 | `Langlands.Group.GL.Nonarchimedean` | 5 | `81e9aee8a06787452e827803cdc32cd1bab00b5988dfddbdf85a9762b79f46bc` | `16db461b54c5a193c29f5319bea7fa2e3d454a5766b2cd94bf8ee0a3a655b042` |
| 5 | `Langlands.Group.GL.NonarchimedeanStatement` | — | `e6c1d5e722bb4ebf86de405f0bf4e57627c19fbe3cc7e4bdfbd5a31b6af1b63c` | `f390f56b1aa616cb1e5226df67f7893e9c33248e51d462197e7461862cfc1a10` |
| 6 | `Langlands.Group.GL.NormalizedCharacter` | 7, 14, 53 | `31deaadcf15cf03e88fd00e26452df03cc103ca9bae18206dac748b9b6d53568` | `296f42c5aeb400f8d131210db13508fff6f220755b08b8c4b8a6f9c129640507` |
| 7 | `Langlands.Group.GL.Padic` | 1, 11, 16 | `803a2561ddc85a54c7846a421d37ed5dc61b8974157b02b72c26bc41d96e1722` | `380b41087f6569d499e54580e487d1da0755236b84ec3085649cbc37f7a66d89` |
| 8 | `Langlands.Group.GL.RankMaps` | 1, 7 | `5cd299ec27e66d96bccc8bd9a67d69ecbbc42974351b143c44838f32dd03de41` | `507811ee6523775ec504dbf4ee4b9b783636fced040a6d1780e709743a393653` |
| 9 | `Langlands.Group.GL.UpperUnipotent` | 1 | `6c2858fa5f866777a0cd3066f3bba643d3300ef24bc1532a3d034001d9ec28c2` | `bbce6c75bc9a59268b36ee5d4fa0f475b59be64dfc1a396b897cf4937269c02f` |
| 10 | `Langlands.HarmonicAnalysis.Basic` | — | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` | `770a9f6e068d76d72fb10ff91ee1a27b66696ebf0c52af23464fb4d0956ffdf6` |
| 11 | `Langlands.LocalField.Canonical` | 12 | `e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48` | `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d` |
| 12 | `Langlands.LocalField.Definitions` | — | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` | `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf` |
| 13 | `Langlands.LocalField.Normalization.Definitions` | 12 | `b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b` | `dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436` |
| 14 | `Langlands.LocalField.Normalization.Proof` | 15 | `4efa0826ddc069b2963ab4933716979e5bc7c5c866498047aabfbfc417071ded` | `1c3bf219eca92cd04af13c152757d83b4d92dd9787c334acec773bb51a4ad161` |
| 15 | `Langlands.LocalField.Normalization.Statement` | 13 | `27f6b841c15cf1e4dffcb40126f95ea329c08d91ab9950d8fe645a94683eedc6` | `245db7bd9d6b10a8e9cb2882021f2d210a396aa1149e9a8adeb9a889bc7d753b` |
| 16 | `Langlands.LocalField.Topology` | 12 | `09ba251eb70a2455da2a7864c7cd34739adbfa717771adc3a86670d2bd0d791c` | `1c28337c12f885cb438b405d58a077c186b4710d20a1256dc0fe8288b4107992` |
| 17 | `Langlands.Representation.Category.Basic` | 33 | `6a4781890b642e590206b68b7cea02bc4add8bdfb85e6a29991f73992bbcf706` | `647da2c8e2011decf8c6971c0f4a20a162e6ead265bf4d7448b2045072862ba2` |
| 18 | `Langlands.Representation.Category.Subquotients` | 17, 36 | `d443366e944c46fad3f3ef4e82e519a30e44d1b5194c829b795d9fc1a6c531b4` | `9ebebf01a99db613b0ca298928e6a479773819216d81de9506a8faaf08860325` |
| 19 | `Langlands.Representation.Category.Twist` | 17, 38, 40, 49 | `9fb1bca986f0a1a202a4e3d9e1ac481405646293ece6da63374e447cd85ca740` | `e16d708bc3b312c0a79947852bbf147ea230b0a9b8b9ddbd9f80432833bfcb5d` |
| 20 | `Langlands.Representation.Derivative.Homogeneity` | 21, 18 | `93070ffd89ec0f58a8bb256e7714a1c637efe612db946ebcae89c037925ffabc` | `c3b5e1c916b681f21902386e0216029d1c9607dd56095a63eac52fed57fe6062` |
| 21 | `Langlands.Representation.Derivative.Iteration` | 23 | `ab8bbcca5fd7affabf804d6adbe09bdf2d578f961d1149a3182e6bc5a7a9a25b` | `056e0b7c6718776422735f35b44ca4749b31b5ed176349e9311460eecb880b1c` |
| 22 | `Langlands.Representation.Derivative.MirabolicCharacter` | 3, 4, 54, 26, 52, 42 | `27ad9768aa1f5ee9f1534e99521462f22cdb280abbcf711b79621d405d654a6d` | `f7b710cddba2ed791d268d8a1644315548f2b64912ffed0138579cbd497fae25` |
| 23 | `Langlands.Representation.Derivative.MirabolicMinus` | 22, 19, 45, 34, 6 | `526932155b00d435068485ffb7a8a5d4f565b9729779cebe97cfcf96e894e02e` | `3b6fbca0a52aed7251fab742229c22ded359759b67326d66f69db5c1a9b0e9c9` |
| 24 | `Langlands.Representation.Dual.Definitions` | — | `53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5` | `bf9972bb15d854ff605ed825fdcdf90734dc924ad0ae33efb6bb4e55a882845a` |
| 25 | `Langlands.Representation.Jacquet.Coinvariants` | — | `73e5003712204a35595095b0582ad64d931423aeecec2f6165c4c20d945a4566` | `5e040cb16af3b1c72e0c7f1530881639ab055f9528703b9bc20de1931d098a00` |
| 26 | `Langlands.Representation.Jacquet.Localization` | 27, 17 | `0b50fec4e9e7ad2561f86c6d7e485e2c3a10b1e1c6f750f10c35f5cfc1b3b6ee` | `2a575f90942a22b363b4184941a2470d33e27ad633afe02aa4aa1b818ae62332` |
| 27 | `Langlands.Representation.Jacquet.SmoothTwist` | 25, 34, 36, 46 | `61f9309e04c330e87ceaf2f948868645d6d668a0d9dfde75d16435ca355a5daa` | `4c8fa6423740da78ca9a07a79872d36139c9823e5ed0befa880912105823fda8` |
| 28 | `Langlands.Representation.MatrixCoefficient.Definitions` | — | `92c0bf57151ef798f1198793a4d685afd175274240c1956b54ce3d10e855b7ae` | `c9fdcc728fe28ed0de403801ed10d861d70dd69994179b4fd14f35662d910955` |
| 29 | `Langlands.Representation.MatrixCoefficient.LawsProof` | 30 | `f73da4941552a524d5e0116675df291d5e99ae1c59b6bc10b21ce2f0ae0fbbae` | `b517f288c98cb53bcb505562f68a20db15025e1c89de85733fec3c8a501b2f6a` |
| 30 | `Langlands.Representation.MatrixCoefficient.LawsStatement` | 28, 24, 33 | `bf9b7e4cbef45e07642511fbfb033312f2378714476510549e1c6c9189d570fb` | `c077dcf35c8f1229abc17244c5545fbc17603b1c96ae635ced585c82892d1fdd` |
| 31 | `Langlands.Representation.Smooth.Admissibility.CofinalProof` | 32 | `b01c589f73cb2488a38477ea95bbb6adda0863507efbcb54e561843e467c112a` | `df9117b7ccc80b412fac95816eda27bb0bb18762909c8b0ec39ff35a9a398b59` |
| 32 | `Langlands.Representation.Smooth.Admissibility.CofinalStatement` | 33 | `df36b24b8e9972dbaa6d810baa13fcb796fbc81465367c8de92a08ca4449a433` | `7cd745762089838e4cbc5d4e6a96718a7bc7632de6b74c2499e84e59af9911e1` |
| 33 | `Langlands.Representation.Smooth.Definitions` | — | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |
| 34 | `Langlands.Representation.Smooth.Transfer.PullbackProof` | 35 | `b0502abed8a3551e9a5c542f07605cd66b83649fafbcb38a23b05dddc3e691b6` | `46884ac73c7107c18ce746c2110810d14d19939b7fca6a608670a6c70265ddfb` |
| 35 | `Langlands.Representation.Smooth.Transfer.PullbackStatement` | 33 | `a5aaff9766d2e8213ffc82b44625f6fb2ec7f20921b7b03da4ad3250849bcb4d` | `694ccbf90e6fea84743fe380fefdcc25cdaacd1294c53bab78298a465e0df17b` |
| 36 | `Langlands.Representation.Smooth.Transfer.SubquotientProof` | 37 | `8e26bf64cb2eff5bfdc6037d5d6c52650bd92944a1c9ef0b57c4f12cc3b0d1cd` | `c1f909953edfa360eacae0f2f266025e1dc1ae7000755873f9ad5d3d2985eb0b` |
| 37 | `Langlands.Representation.Smooth.Transfer.SubquotientStatement` | 33 | `d5729f07038515e26eb8d56cc94a982ed8c066a505acea9b1bc2020f4be08c88` | `fea9069973877d67465589b6e5a0d9336d9b1781e7c275c82492a63ce10b3470` |
| 38 | `Langlands.Representation.Twist.AdmissibilityProof` | 39, 46, 31 | `706ab8ce915e9902ec30d92c2d471cf7e2e79e2012bf524c9c28868403bf0467` | `25f27ae9ae9c290b60794b1790f6cf0ae47594117c0eee6076dd1cef6b7a0d44` |
| 39 | `Langlands.Representation.Twist.AdmissibilityStatement` | 44, 33 | `c875a02d8f49506749bc2265041879888de7ad0c76428211a20ffc755f7e7127` | `04559a67afac5b26f332a6122fd9c43424b35f6d9fa9adf917a186108b7702c2` |
| 40 | `Langlands.Representation.Twist.AlgebraProof` | 41 | `15d469011c703f801ddf6810a9104c0588ab917eb2a179ff6360907425c4fad6` | `9d1893be208c8fcbda33b717d999e2767f76eb9068b70f62932fb3de8d0b17b2` |
| 41 | `Langlands.Representation.Twist.AlgebraStatement` | 44 | `4c643392e7fc949501dc3e36df71fda5e507598d1a8296be6ea43b3768337895` | `9fd167f7518e27a89b19cfe238a977c8ca2146e0554bb8a92b4dd95171c5b504` |
| 42 | `Langlands.Representation.Twist.ContinuousCharacterProof` | 43 | `ff9b38a8e4ded2734ccaed8429df42e2abbf92e580034a2576ad111899820f8e` | `ba9c6c6026b6b6a6b576b0d71dba2f8ce39625451f884fc7fe0a309bd7191dc9` |
| 43 | `Langlands.Representation.Twist.ContinuousCharacterStatement` | — | `78a1e542d56cbdfe0f0cf448a0010e6ca2f3331fb3af7437e8d03927de7210c0` | `0791b592e84c04c73f41709e1391c23f874061e8991bf57f5bf750dba5367b3a` |
| 44 | `Langlands.Representation.Twist.Definitions` | — | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` | `94e8c64945411e253a2c91a8e1bf52090d6df15a43362b2032717064c6ac49bc` |
| 45 | `Langlands.Representation.Twist.RealPower` | 46 | `83e415568697155665a471b9690d6504e353648839503a9a500ef10601f88896` | `509f3af473e1897d2b340724874834fae55db09fe14bfe5007dcea7eca6e1023` |
| 46 | `Langlands.Representation.Twist.SmoothProof` | 47 | `704914497f29af5abae486c96edead39aa8fa267efeae2d061016c36634cac90` | `b5423ba5dfe57fe3f53686c01a19fb27df085454007505922a788e5666c8a1e4` |
| 47 | `Langlands.Representation.Twist.SmoothStatement` | 44, 33 | `61616bd03710ca5a5c35ba3bb2b4e5793a9f15801ad99a60d7b20bd95ee3de90` | `6e819947725e6a0877bb7d78dba6c2cbe15a6b7f273c4fe531e4ee3fdc31674e` |
| 48 | `Langlands.Representation.Twist.SubquotientDefinitions` | 44 | `a9bb92883a9272653ba680cdadc8e025d2f1268bd124ccb7d612f26894227584` | `75aac3b4caadfe14697eeb85f8a4ed729b308d33fd8cac2776c50565de53a7c7` |
| 49 | `Langlands.Representation.Twist.SubquotientProof` | 50 | `99a2a6e8fe25e885daffea5e59aa2c77f4304afa100d564adabcd869754365a9` | `cf6dad59297e353be1f3cdeca307c3c507d4fc0a5d29ac1c4806b7edc22c4cd0` |
| 50 | `Langlands.Representation.Twist.SubquotientStatement` | 48 | `1c2bae8d080e8c21743d658d1e3a251e4f5c5c997a4ecd2edd77d6d9315d4b7d` | `407963c3e4e87823630f491fca84066dc7d5a0ca1e7c7404d4d1d577905d7732` |
| 51 | `Langlands.Representation.Whittaker.Algebraic` | 28, 33 | `890e409cf2b4d586912b928755a4a0dc7b72de9d058ede7510482d816dad3906` | `8127b520fe0395c6600d6b72a7340b87edbf38c4ae1ca664546d63452f8e9072` |
| 52 | `Langlands.Representation.Whittaker.GeneralLinear` | 9, 10, 29, 51 | `5f5057d690e1bac49a27d650a3c9e678b94660efe8e244ed96e869f33488594c` | `f30d2edde346bc5bbdf3103a54c35f205a6be9643d900be6c4fea23ad38a49cc` |
| 53 | `Langlands.Topology.CompactNormCharacter` | — | `6f70b9473d6386cd111d890c4df0bf411842d28dfdc377e38c2c4fe55e8b0fb7` | `3e50c9561e3e7a068e729aec594ce107f572b2858cd859e6c000fcb8c0aef482` |
| 54 | `Langlands.Topology.Nonarchimedean.Subgroup` | — | `a45ededd3f67a6645df268d1bf9da0cbcac964137c448ef89966630cd4b4c026` | `01724029b2c592535f55fea2ec4a857a7d15d15156063567d1216e1e4b265675` |

### Complete project declaration closure

Each block lists exactly the project constants reached by recursive type/value
dependency traversal, grouped by their defining module. Modules in the import
table with no listed constant are loaded but not reached by this traversal.

`Langlands.Group.GL.Basic` (10 constants):

```text
Langlands.GeneralLinear
Langlands.GeneralLinear.determinant
Langlands.GeneralLinear.determinantContinuous
Langlands.GeneralLinear.determinantContinuous._proof_1
Langlands.GeneralLinear.entry
Langlands.GeneralLinear.entry._proof_1
Langlands.GeneralLinear.reindex
Langlands.GeneralLinear.reindexContinuous
Langlands.GeneralLinear.reindexContinuous._proof_1
Langlands.GeneralLinear.reindexContinuous._proof_2
```

`Langlands.Group.GL.Mirabolic` (8 constants):

```text
Langlands.GeneralLinear.Mirabolic.entry
Langlands.GeneralLinear.Mirabolic.entry._proof_1
Langlands.GeneralLinear.mirabolic
Langlands.GeneralLinear.mirabolic._proof_1
Langlands.GeneralLinear.mirabolic._proof_2
Langlands.GeneralLinear.mirabolic._proof_3
Langlands.GeneralLinear.mirabolic._simp_1
_private.Langlands.Group.GL.Mirabolic.0.Langlands.GeneralLinear.lastRow_mul
```

`Langlands.Group.GL.MirabolicRadical` (56 constants):

```text
Langlands.GeneralLinear.Mirabolic.continuous_levi
Langlands.GeneralLinear.Mirabolic.continuous_successor
Langlands.GeneralLinear.Mirabolic.levi
Langlands.GeneralLinear.Mirabolic.levi._proof_1
Langlands.GeneralLinear.Mirabolic.leviContinuousEquiv
Langlands.GeneralLinear.Mirabolic.leviContinuousEquiv._proof_1
Langlands.GeneralLinear.Mirabolic.leviContinuousEquiv._proof_2
Langlands.GeneralLinear.Mirabolic.leviEquiv
Langlands.GeneralLinear.Mirabolic.leviEquiv_symm_entry
Langlands.GeneralLinear.Mirabolic.leviSubgroup
Langlands.GeneralLinear.Mirabolic.leviSubgroup_le_normalizer
Langlands.GeneralLinear.Mirabolic.levi_bottom
Langlands.GeneralLinear.Mirabolic.levi_conjugate_radicalElement
Langlands.GeneralLinear.Mirabolic.levi_first
Langlands.GeneralLinear.Mirabolic.levi_injective
Langlands.GeneralLinear.Mirabolic.levi_last
Langlands.GeneralLinear.Mirabolic.levi_mul_radicalElement
Langlands.GeneralLinear.Mirabolic.radical
Langlands.GeneralLinear.Mirabolic.radical._proof_1
Langlands.GeneralLinear.Mirabolic.radical._proof_2
Langlands.GeneralLinear.Mirabolic.radical._proof_3
Langlands.GeneralLinear.Mirabolic.radicalCoordinates
Langlands.GeneralLinear.Mirabolic.radicalCoordinates_element
Langlands.GeneralLinear.Mirabolic.radicalElement
Langlands.GeneralLinear.Mirabolic.radicalElement_add
Langlands.GeneralLinear.Mirabolic.radicalElement_bottom
Langlands.GeneralLinear.Mirabolic.radicalElement_coordinates
Langlands.GeneralLinear.Mirabolic.radicalElement_first
Langlands.GeneralLinear.Mirabolic.radicalElement_last
Langlands.GeneralLinear.Mirabolic.radicalEquiv
Langlands.GeneralLinear.Mirabolic.radicalEquiv._proof_1
Langlands.GeneralLinear.Mirabolic.radicalEquiv._proof_2
Langlands.GeneralLinear.Mirabolic.radicalToUpperUnipotent._proof_1
Langlands.GeneralLinear.Mirabolic.successor
Langlands.GeneralLinear.Mirabolic.successor._proof_1
Langlands.GeneralLinear.Mirabolic.successorContinuousEquiv
Langlands.GeneralLinear.Mirabolic.successorContinuousEquiv._proof_1
Langlands.GeneralLinear.Mirabolic.successorContinuousEquiv._proof_2
Langlands.GeneralLinear.Mirabolic.successorEquiv
Langlands.GeneralLinear.Mirabolic.successorEquiv_symm_entry
Langlands.GeneralLinear.Mirabolic.successorSubgroup
Langlands.GeneralLinear.Mirabolic.successorSubgroup_le_normalizer
Langlands.GeneralLinear.Mirabolic.successor_first
Langlands.GeneralLinear.Mirabolic.successor_injective
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL.eq_1
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_bottom
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_first
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_last
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit._proof_1
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit._proof_2
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.continuous_leviEquiv_symm
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.continuous_successorEquiv_symm
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.fixedColumn_mul
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.levi_conjugate_mem
```

`Langlands.Group.GL.NormalizedCharacter` (13 constants):

```text
Langlands.PadicField.TopologicalData.determinantNorm
Langlands.PadicField.TopologicalData.isOpen_ker_determinantNorm
Langlands.PadicField.TopologicalData.isOpen_ker_normalizedAbsUnits
Langlands.PadicField.TopologicalData.isOpen_ker_normalizedAbsUnits._simp_1_1
Langlands.PadicField.TopologicalData.normalizedAbsHom
Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_1
Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_2
Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_3
Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_4
Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_5
Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_6
Langlands.PadicField.TopologicalData.normalizedAbsUnits
Langlands.PadicField.TopologicalData.normalizedAbs_eq_one_iff_discreteValuation
```

`Langlands.Group.GL.Padic` (4 constants):

```text
Langlands.PadicField.TopologicalData.generalLinearDeterminant
Langlands.PadicField.TopologicalData.generalLinearDeterminant._proof_1
Langlands.PadicField.TopologicalData.generalLinearTopologicalGroup
Langlands.PadicField.TopologicalData.generalLinearTopology
```

`Langlands.Group.GL.RankMaps` (23 constants):

```text
Langlands.GeneralLinear.blockSum
Langlands.GeneralLinear.blockSumContinuous
Langlands.GeneralLinear.blockSumContinuous._proof_1
Langlands.GeneralLinear.blockSum_apply_left
Langlands.GeneralLinear.blockSum_apply_left_right
Langlands.GeneralLinear.blockSum_apply_right
Langlands.GeneralLinear.blockSum_apply_right_left
Langlands.GeneralLinear.rankInclusion
Langlands.GeneralLinear.rankInclusion._proof_1
Langlands.GeneralLinear.rankInclusion._proof_2
Langlands.GeneralLinear.rankInclusionContinuous
Langlands.GeneralLinear.rankInclusionContinuous._proof_1
Langlands.GeneralLinear.rankInclusion_injective
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_1
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_2
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_3
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_4
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_5
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_6
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_7
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_8
_private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.continuous_blockSumCoordinates
```

`Langlands.HarmonicAnalysis.Basic` (4 constants):

```text
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.mk
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar
```

`Langlands.LocalField.Definitions` (10 constants):

```text
Langlands.PadicField
Langlands.PadicField.Carrier
Langlands.PadicField.TopologicalData
Langlands.PadicField.TopologicalData.localField
Langlands.PadicField.TopologicalData.mk
Langlands.PadicField.TopologicalData.topology
Langlands.PadicField.TopologicalData.valuativeRel
Langlands.PadicField.algebra
Langlands.PadicField.field
Langlands.PadicField.mk
```

`Langlands.LocalField.Normalization.Definitions` (9 constants):

```text
Langlands.PadicField.TopologicalData.Integers
Langlands.PadicField.TopologicalData.ResidueField
Langlands.PadicField.TopologicalData.ResidueField._proof_1
Langlands.PadicField.TopologicalData.discreteValuation
Langlands.PadicField.TopologicalData.discreteValuation._proof_1
Langlands.PadicField.TopologicalData.discreteValuation._proof_2
Langlands.PadicField.TopologicalData.normalizedAbs
Langlands.PadicField.TopologicalData.ord
Langlands.PadicField.TopologicalData.residueCardinality
```

`Langlands.LocalField.Normalization.Proof` (12 constants):

```text
Langlands.PadicField.TopologicalData.finite_residueField
Langlands.PadicField.TopologicalData.finite_residueField._proof_1_1
Langlands.PadicField.TopologicalData.normalizedAbs_le_iff_of_ne_zero
Langlands.PadicField.TopologicalData.normalizedAbs_mul
Langlands.PadicField.TopologicalData.normalizedAbs_nonneg
Langlands.PadicField.TopologicalData.normalizedAbs_of_ne_zero
Langlands.PadicField.TopologicalData.normalizedAbs_one
Langlands.PadicField.TopologicalData.normalizedAbs_pos
Langlands.PadicField.TopologicalData.normalizedAbs_zero
Langlands.PadicField.TopologicalData.ord_mul
Langlands.PadicField.TopologicalData.ord_one
Langlands.PadicField.TopologicalData.residueCardinality_gt_one
```

`Langlands.Representation.Category.Basic` (9 constants):

```text
Langlands.SmoothRep
Langlands.SmoothRep.hom
Langlands.SmoothRep.instAddCommGroupVObjRepSmoothRepProperty
Langlands.SmoothRep.instModuleVObjRepSmoothRepProperty
Langlands.SmoothRep.isSmooth
Langlands.SmoothRep.of
Langlands.SmoothRep.ofHom
Langlands.SmoothRep.representation
Langlands.smoothRepProperty
```

`Langlands.Representation.Category.Subquotients` (3 constants):

```text
Langlands.SmoothRep.stable
Langlands.SmoothRep.subrepresentation
Langlands.SmoothRep.subrepresentation._proof_1
```

`Langlands.Representation.Category.Twist` (5 constants):

```text
Langlands.SmoothRep.twist
Langlands.SmoothRep.twist._proof_1
Langlands.SmoothRep.twistFunctor
Langlands.SmoothRep.twistFunctor._proof_1
Langlands.SmoothRep.twistFunctor._proof_2
```

`Langlands.Representation.Derivative.Homogeneity` (7 constants):

```text
Langlands.Derivative.HasNonzeroDerivative
Langlands.Derivative.IsHomogeneous
Langlands.Derivative.level
Langlands.Derivative.mirabolicDerivativeOfOrder
Langlands.Derivative.mirabolicRankCast
Langlands.Derivative.mirabolic_rank_eq_of_order
Langlands.Derivative.mirabolic_rank_eq_of_order._proof_1_1
```

`Langlands.Representation.Derivative.Iteration` (4 constants):

```text
Langlands.Derivative.mirabolicDerivative
Langlands.Derivative.phiMinusIterate
Langlands.Derivative.phiMinusIterate._f
Langlands.Derivative.phiMinusIterate.match_1
```

`Langlands.Representation.Derivative.MirabolicCharacter` (10 constants):

```text
Langlands.Derivative.Mirabolic.lastCoordinate
Langlands.Derivative.Mirabolic.lastCoordinate._proof_1
Langlands.Derivative.Mirabolic.lastCoordinate._proof_2
Langlands.Derivative.Mirabolic.lastCoordinate._proof_3
Langlands.Derivative.Mirabolic.lastCoordinate._proof_4
Langlands.Derivative.Mirabolic.mulVec_last
Langlands.Derivative.Mirabolic.theta
Langlands.Derivative.Mirabolic.theta_isInvariant
Langlands.Derivative.Mirabolic.theta_radicalElement
Langlands.PadicField.TopologicalData.mirabolicTheta
```

`Langlands.Representation.Derivative.MirabolicHighestLayerStatement` (1 constants):

```text
Langlands.Derivative.MirabolicHighestLayerStatement
```

`Langlands.Representation.Derivative.MirabolicMinus` (27 constants):

```text
Langlands.Derivative.Mirabolic.continuousPullback
Langlands.Derivative.Mirabolic.continuousPullback._proof_1
Langlands.Derivative.Mirabolic.continuousPullbackFunctor
Langlands.Derivative.Mirabolic.continuousPullbackFunctor._proof_1
Langlands.Derivative.Mirabolic.continuousPullbackFunctor._proof_2
Langlands.Derivative.Mirabolic.continuousPullbackMap
Langlands.Derivative.Mirabolic.continuousPullbackMap._proof_1
Langlands.Derivative.Mirabolic.continuousPullbackMap._proof_2
Langlands.Derivative.Mirabolic.isOpen_ker_phiMinusCharacter
Langlands.Derivative.Mirabolic.isOpen_ker_psiMinusCharacter
Langlands.Derivative.Mirabolic.phiMinus
Langlands.Derivative.Mirabolic.phiMinusCharacter
Langlands.Derivative.Mirabolic.phiMinusUnnormalized
Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_1
Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_2
Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_3
Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_4
Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_5
Langlands.Derivative.Mirabolic.psiMinus
Langlands.Derivative.Mirabolic.psiMinusCharacter
Langlands.Derivative.Mirabolic.psiMinusCharacter._proof_1
Langlands.Derivative.Mirabolic.psiMinusUnnormalized
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_1
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_2
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_3
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_4
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_5
```

`Langlands.Representation.Jacquet.Localization` (35 constants):

```text
Langlands.Jacquet.Localization.Coinvariants
Langlands.Jacquet.Localization.IsInvariant
Langlands.Jacquet.Localization.action
Langlands.Jacquet.Localization.conjugate
Langlands.Jacquet.Localization.conjugate._proof_1
Langlands.Jacquet.Localization.hom_ext
Langlands.Jacquet.Localization.isInvariant_one
Langlands.Jacquet.Localization.isSmooth_action
Langlands.Jacquet.Localization.lift
Langlands.Jacquet.Localization.lift._proof_1
Langlands.Jacquet.Localization.map
Langlands.Jacquet.Localization.map._proof_1
Langlands.Jacquet.Localization.mapLinear
Langlands.Jacquet.Localization.mapLinear._proof_1
Langlands.Jacquet.Localization.map_comp
Langlands.Jacquet.Localization.map_id
Langlands.Jacquet.Localization.mk
Langlands.Jacquet.Localization.mk_apply_subgroup
Langlands.Jacquet.Localization.mk_eq_iff
Langlands.Jacquet.Localization.mk_surjective
Langlands.Jacquet.Localization.quotientMap
Langlands.Jacquet.Localization.quotientMap._proof_1
Langlands.Jacquet.Localization.quotientMap._proof_2
Langlands.Jacquet.Localization.relations
Langlands.Jacquet.Localization.relations._proof_1
Langlands.Jacquet.Localization.relations_le_ker_iff
Langlands.Jacquet.Localization.relations_le_ker_iff._simp_1_1
Langlands.Jacquet.Localization.relations_le_ker_iff._simp_1_2
Langlands.Jacquet.Localization.relations_stable
Langlands.Jacquet.Localization.smoothFunctor
Langlands.Jacquet.Localization.smoothFunctor._proof_1
Langlands.Jacquet.Localization.smoothFunctor._proof_2
Langlands.Jacquet.Localization.smoothObject
Langlands.Jacquet.Localization.smoothObject._proof_1
Langlands.Jacquet.Localization.sub_mem_relations
```

`Langlands.Representation.Smooth.Definitions` (3 constants):

```text
Langlands.IsSmooth
Langlands.IsSmoothVector
Langlands.fixedVectors
```

`Langlands.Representation.Smooth.Transfer.PullbackProof` (2 constants):

```text
Langlands.isSmoothVector_comp
Langlands.isSmooth_comp
```

`Langlands.Representation.Smooth.Transfer.SubquotientProof` (4 constants):

```text
Langlands.isSmoothVector_map
Langlands.isSmoothVector_of_injective
Langlands.isSmooth_of_injective
Langlands.isSmooth_of_surjective
```

`Langlands.Representation.Twist.Definitions` (7 constants):

```text
Langlands.twist
Langlands.twist._proof_1
Langlands.twist._proof_2
Langlands.twist._proof_3
Langlands.twistIntertwining
Langlands.twistIntertwining._proof_1
Langlands.twistIntertwining._proof_2
```

`Langlands.Representation.Twist.RealPower` (4 constants):

```text
Langlands.isOpen_ker_realPowerCharacter
Langlands.ker_le_realPowerCharacter_ker
Langlands.positiveUnitsToComplex
Langlands.realPowerCharacter
```

`Langlands.Representation.Twist.SmoothProof` (2 constants):

```text
Langlands.isSmoothVector_twist_iff
Langlands.isSmooth_twist_iff
```

## Inherited independence controls for the proof successor

These controls preserve the complete mathematical exclusion set. They are
restrictions on the future proof route and any lower splits, not additional
Lean hypotheses. The scoped detection restrictions below apply to detection
and its prerequisite closure; the separately authorized Ze80 §5.1 analytic
route of this layer statement remains available.

Do not use the mathematical conclusion `Langlands.Derivative.MirabolicStrongIndecomposabilityReduction`, its proof task `08fe06ea-e64e-4f3a-b899-3e0acacf61db`, or their proof successors or transitive proof consequences to establish this analytic prerequisite. Exclude an assumed strong-indecomposability conclusion as a substitute for the actual highest layer. The generic lattice transport/essential-interval unit is already owned separately by Workers 864/700: statement artifact `ec62132d-2b17-4cbd-bd75-d5fd43de7cde` is public, and exact proof task `a2baddab-056b-4503-865e-74d58ecb3812` exists; do not duplicate that algebraic unit. It does not provide this actual layer or its analytic comparisons.

This is a lower input to ordered-socle existence task 23189526-80b0-4828-a6d4-7ebec2cbeef5. Exclude that conclusion and socle exhaustion f3a69bc8-7312-4f82-8a7d-ea3c8188cb63, analytic segment classification aca8805b-054f-4d56-8045-12db7f623404, segment-socle product irreducibility 23e98d90-6055-4e35-91a9-b0f5d8a84961, final segment-socle irreducibility criterion 2ae5cbe5-0701-4509-88a0-db8cbeb35be4, AdjacentUnlinkedSegmentSocleSwap, TwoSegmentSocleCommutation, special-head product criterion 8364e73f-14ec-4d14-8f2b-1555a7c1ce95, special-head exhaustion 3bfb61fa-1129-4fc9-83fd-7fcfec22106e, ordered special-head existence ebea9a8a-9b21-4208-aa31-98c2dea1f8a3, quotient coverage 20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584, tempered block uniqueness 52e97845-36bb-457d-b76f-70753334b88c, SquareIntegrableLanglandsClassification / 1cb45da2-7007-4351-a694-594fb148b8d1, square-integrable exhaustion cd8ab97c-0b78-4bce-97c4-d307a28159a4, regular exhaustion bf433f0a-921a-428c-b0c0-6475438125ac, GenericSegmentProductUniqueness / 30341ae4-65f2-4a0e-9283-763db01a409e, ordered special-segment conversion 8252833d-c269-41a9-824c-5879e531b23b, and forward special-segment essential square-integrability 5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807. These exclusions cover the mathematical conclusions, their proof successors and transitive proof dependencies. Check shared lower inputs for independence and record the complete import/declaration audit in the paired proof Markdown. Preserve this exclusion set in any lower splits.

The complete parent context is carried verbatim below as inherited context. Its detection-specific restrictions apply to detection and its prerequisite closure; they do not prohibit the separately authorized Ze80 5.1/5.4 analytic route here. Preserve every stated exclusion on any reused detection dependency, including the additional nonadjacent/full-formula consumer exclusions. Record both mathematical proof dependencies and the complete project import/declaration closure in the relevant final paired Markdown; shared lower constructions require their own independence checks.

Do not resume, replace or bypass the operator-paused minus exactness task `b65bc667-6951-4bd5-82af-10fb7046df7f` or Worker 127's controls, or treat this endpoint task as authority to replace the paused exactness work. Preserve Worker 157's finite-length scope `0717fd42-d711-4f42-8269-f6ae4c8da1e9`, Worker 357's mixed-product/restriction/Leibniz and raw tensor/partial-derivative scope, and Worker 288's k=0 adapter. Search and coordinate existing plus-functor, adjunction, exactness and filtration owners before splitting further substantial prerequisites; lower definitions and statements must be accepted/public before exact proof successors. Reuse accepted/public constructions by Lean name after checking their precise guarantees; constructors alone do not prove adjunction, exactness or the endpoint. Worker 710's message read by the publisher disclaims ownership of the actual layer, lattice comparison, homogeneity-essentiality and adjunction endpoints. No pause is waived by this publication.


### Inherited detection-specific restrictions

The shared general detection prerequisites have stricter independence conditions from their nonadjacent-product consumer. The following is the complete inherited ownership/independence extract from that detection contract. In this extract, “this” means the general detection unit, not this successor's whole target. Preserve these restrictions on detection and its prerequisite closure. They do not prohibit the separately specified Ze80 5.4/6.2 arguments in their respective consumers.

This is the BZ77-only upstream detection clause for mirabolic strong-indecomposability statement task `ff4738d8-47e3-433b-bedc-629bc2d492a7`, ordered-socle proof task `23189526-80b0-4828-a6d4-7ebec2cbeef5`, and nonadjacent two-supercuspidal product task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`. It does not duplicate or replace the combined Ze80 section 5.4 reduction statement. Do not use that combined reduction or its strong-indecomposability conclusion to prove detection. Do not use either the nonadjacent product conclusion or the full two-supercuspidal product-structure conclusion of `ab61f565-1427-4746-ba77-46097563e962`, including its adjacent composition/Jacquet conjuncts. The proof route must be general BZ77 derivative theory and independent of these consumers.

The trusted operator conditions recorded for the nonadjacent consumer are in `/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md` (sender_role operator); read that file completely. They allow a fully proved BZ77 derivative route and forbid using Ze80 segment derivative formulas or circular results. Every lower derivative result later used must have an independently accepted and published proof. A citation, unproved proposition, draft or pending task is not a proof input. Preserve the following full union of exclusion sets, including mathematical conclusions, exact proof successors and transitive dependencies, in all later proof and lower prerequisite tasks.

Do not use conclusions, proof successors or transitive proof dependencies of ordered-socle existence `23189526-80b0-4828-a6d4-7ebec2cbeef5`, socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`, unlinked segment-socle product irreducibility `23e98d90-6055-4e35-91a9-b0f5d8a84961`, the final segment-socle irreducibility criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`, the special-head product irreducibility criterion `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`, `SquareIntegrableLanglandsClassification` / `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`, `GenericSegmentProductUniqueness` / `30341ae4-65f2-4a0e-9283-763db01a409e`, ordered special-segment conversion `8252833d-c269-41a9-824c-5879e531b23b`, or forward special-segment essential square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`. Preserve this full exclusion set in later proof tasks and lower splits. Shared lower inputs need their own independence audit.

Additional nonadjacent-consumer exclusions (the references to "this proof" mean that consumer and every prerequisite, including detection):

Neither this
proof nor any prerequisite may depend directly or transitively on the following
tasks, their mathematical conclusions, proof successors or downstream
consequences:

- Individual special-head/reverse-socle existence
  `67279e36-f3c2-42e3-9302-11729784042e`.
- Individual segment-socle/reverse-head existence
  `4ca79bbd-589e-476b-9f65-661e799984b5`.
- Analytic segment classification
  `aca8805b-054f-4d56-8045-12db7f623404`.
- Forward special square-integrability,
  `SegmentSpecialEssentialSquareIntegrability`, and
  `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`.
- Multisegment special-head exhaustion
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`.
- Ordered strong-head existence
  `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`.
- Quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`.
- Ordered conversion `8252833d-c269-41a9-824c-5879e531b23b`.
- Tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c`.
- `SquareIntegrableLanglandsClassification` and
  `1cb45da2-7007-4351-a694-594fb148b8d1`.
- Square-integrable exhaustion
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`.
- Regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`.
- Special-head product irreducibility
  `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`.
- `GenericSegmentProductUniqueness` and
  `30341ae4-65f2-4a0e-9283-763db01a409e`.
- `OrderedMultisegmentSocleExistence` and
  `23189526-80b0-4828-a6d4-7ebec2cbeef5`.
- `MultisegmentSocleExhaustion` and
  `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`.
- `SegmentSocleProductIrreducibility` and
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`.
- Adjacent socle commutation
  `e3634665-571b-4852-9f4c-bab8a1053434`.
- `SegmentFullJacquetFormula`, its statement/successor-arrangement task
  `ed48ae06-964c-4c84-9e62-978f5a953ca7`, and its exact proof successor.
- `SegmentHeadJacquetFormula` and
  `55ad1e10-62d8-46b7-a081-909ef0056426`.
- `SegmentSocleJacquetFormula` and
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034`.
- `SegmentSpecialJacquetExponentNormFormula` and
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`.

Preserve also the full-formula consumer's additional restrictions: do not
use Ze80's segment derivative formulas (§3.5 or §9.6), and do not assume any
derivative result (including BZ77's) without a proof accepted and published
under the operator conditions above; do not assume a segment product
irreducibility criterion (Ze80 4.2 or 9.7), an analytic or
square-integrability result (Ze80 9.3), or a classification or exhaustion
theorem. Ze80 Theorem 4.2's linked-pair converse rests on §2 and cannot
prove Proposition 1.11 circularly. Carry these exclusions unweakened to every
prerequisite and document the import and mathematical proof-dependency audit
in the final proof Markdown. Shared lower constructions may be reused only
after their independence is checked.

Audit the full transitive project import closure against the public Library and record it completely in the paired Markdown. Do not use Ze80 section 3.5 or 9.6, or the segment-socle part of task `8e5b4563-0365-41c7-b134-70f2a0b36292`; this detection assertion requires no segment or cuspidal derivative formula at all. Shared lower constructions may be reused only after independence checks.
