# Maps used in the actual highest mirabolic layer

Authors: Worker 1185 (construction and proofs), Worker 805 (interfaces and
composition design).

This internal helper module is part of task
`3826dc7b-ec07-4059-9425-ee376ebcf07b`. It proves postcomposition and base-layer
comparisons for the actual published normalized plus constructions. It imports
only `Langlands.Representation.Derivative.MirabolicPlusNormalization`, leaving
all published files unchanged.

The constructions are derived directly from the function-space and quotient
definitions. Their source context is Bernstein–Zelevinsky (1977), §1.8 and
§3.2 (printed pp.444 and 451; one-based PDF5 and PDF12), source `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The cited formulas were checked in the original; no source-specific errata
note was found in the prescribed project locations. These are internal derived
maps, rather than verbatim statements from that source. They do not assume
source adjunction or exactness assertions.

`phiPlusPost` postcomposes a normalized compactly induced function with an
injective intertwiner `E`. Covariance follows from linearity and equivariance.
The same open subgroup fixes the postcomposed function on the right.
Injectivity of `E` makes the two actual nonzero supports equal, so their
projections to the quotient have equal compact support.
`phiPlusPost_eval` is its pointwise formula and `phiPlusPost_injective`
follows from injectivity of evaluation and of `E`.
`mem_range_phiPlusPost` characterizes its entire image by values belonging to
`E.range`. For the reverse implication, choose the unique preimage of each
value. Applying `E` proves covariance and right invariance; equality of supports
transfers compactness. The preimages therefore form an actual vector of the
published normalized compact induction.

`psiPlusBaseEmbedding` applies when the actual radical acts trivially on `A`.
The identity map on `A` annihilates every trivial-character relation, and the
published quotient universal property factors it through the actual Psi-minus
carrier. For equivariance, write a mirabolic matrix as a radical element times
its projected Levi element. The radical acts trivially; the Psi-plus positive
half and Psi-minus negative half characters cancel. The two quotient/embedding
`psiPlusBaseEmbedding_quotient` and
`psiMinusQuotient_psiPlusBaseEmbedding` identities prove
`psiPlusBaseEmbedding_injective` and `psiPlusBaseEmbedding_range`: the range is
the whole ambient representation. Both inverse identities concern the actual
quotient map, without changing its carrier.

All statements install the supplied `T.topology`. Field and input/output carrier
universes `uF`, `uV`, `uW` remain independent. Phi-plus has actual carrier
universe `max uF uV` or `max uF uW`; the maps are heterogeneous
`Representation.IntertwiningMap`s. Every natural rank, including zero, is
allowed. No finite-length, classification, detection, adjunction or general
exactness result is used. This helper alone does not construct the nontrivial
compact counit or the iterated highest layer.

## Dependency and independence audit

The direct project import is `MirabolicPlusNormalization`. The implemented
proofs use its actual function-space constructors, evaluation laws and
normalization character identities, the actual quotient universal property
in `Jacquet.Localization`, and the radical/Levi factorization. The base
comparison is conditional precisely on trivial radical action, as stated;
it makes no unconditional reconstruction claim.

The complete transitive project import closure has 68 modules including
this helper. The 67 pre-existing module pairs are byte-identical to Library
`b22e185743f7c318f709e14e422801f4360105d5`. The table below records both
SHA-256 fingerprints for every pre-existing pair. This helper itself is
identified by its candidate bundle fingerprints rather than a self-hash.

The public exact target and all 54 of its transitive project imports
(55 pairs in total) were also compared byte for byte to that Library
and remain unchanged. Their unchanged root fingerprints are
`18167297f5a3657e1b35b1d09a87eb24430248f08baa2bdf9a1b46eae13a6c0d` (Lean) and
`038132bad17090900b65626b9b168205e311906d32c96ba4c6e5eaae49e588b1` (Markdown).

The complete declaration traversal starts from all nine public declarations
in this helper and recursively follows every referenced constant in types
and bodies, including theorem and opaque bodies and constructors of reached
inductives. It visits 27,469 constants in all libraries; the full project
part is 398 names in 30 modules, listed below, including generated and
private names. The traversal was compiled through the Lean service as a
private audit module; it is not part of the published source.

Neither closure contains detection, homogeneity, the exact endpoint proof,
generic lattice transport, segment/classification or the strong
indecomposability consumer. In particular, these elementary map proofs do
not invoke BZ77 adjunction or exactness theorems. They use the independently
published constructors only with their explicit guarantees; their
elementary evaluation/normalization and quotient identities are checked
from those definitions, without promoting a constructor to adjunction.

No conclusion, exact proof successor or transitive proof consequence of
any item in the inherited exclusion set is used. The retained exclusions
are the following (task IDs are locators, not mathematical dependencies):

- Strong indecomposability reduction `MirabolicStrongIndecomposabilityReduction`,
  task `08fe06ea-e64e-4f3a-b899-3e0acacf61db`.
- Ordered-socle existence and exhaustion; analytic segment classification;
  individual special-head/reverse-socle and segment-socle/reverse-head
  existence; unlinked segment-socle product irreducibility and its final
  criterion; adjacent unlinked socle swap and two-segment socle commutation;
  special-head product irreducibility and exhaustion; ordered special-head
  existence and ordered strong-head existence; quotient coverage; ordered
  special-segment conversion; tempered-block uniqueness; square-integrable
  Langlands classification and exhaustion; regular exhaustion; generic
  segment-product uniqueness; forward special-segment essential square
  integrability; segment full/head/socle Jacquet formulas; special Jacquet
  exponent norm formula; the nonadjacent two-supercuspidal product and full
  two-supercuspidal product-structure consumers.
- Named exclusions include `AdjacentUnlinkedSegmentSocleSwap`,
  `TwoSegmentSocleCommutation`, `SquareIntegrableLanglandsClassification`,
  `GenericSegmentProductUniqueness`, `SegmentSpecialEssentialSquareIntegrability`,
  `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
  `SegmentSocleProductIrreducibility`, `SegmentFullJacquetFormula`,
  `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, and
  `SegmentSpecialJacquetExponentNormFormula`.
- The corresponding inherited task IDs are:

```text
1cb45da2-7007-4351-a694-594fb148b8d1
20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584
23189526-80b0-4828-a6d4-7ebec2cbeef5
23e98d90-6055-4e35-91a9-b0f5d8a84961
2ae5cbe5-0701-4509-88a0-db8cbeb35be4
30341ae4-65f2-4a0e-9283-763db01a409e
3bfb61fa-1129-4fc9-83fd-7fcfec22106e
4ca79bbd-589e-476b-9f65-661e799984b5
52e97845-36bb-457d-b76f-70753334b88c
55ad1e10-62d8-46b7-a081-909ef0056426
5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807
67279e36-f3c2-42e3-9302-11729784042e
8252833d-c269-41a9-824c-5879e531b23b
8364e73f-14ec-4d14-8f2b-1555a7c1ce95
92aea10f-62ac-4e0b-bd4a-9a80909797c5
aca8805b-054f-4d56-8045-12db7f623404
b95105c6-f8bb-4641-ae53-2f49d1e7f034
bf433f0a-921a-428c-b0c0-6475438125ac
cd8ab97c-0b78-4bce-97c4-d307a28159a4
e3634665-571b-4852-9f4c-bab8a1053434
ebea9a8a-9b21-4208-aa31-98c2dea1f8a3
ed48ae06-964c-4c84-9e62-978f5a953ca7
f3a69bc8-7312-4f82-8a7d-ea3c8188cb63
3c9849a4-a6c0-43ac-9982-d15ed76bf1e9
ab61f565-1427-4746-ba77-46097563e962
```

No Ze80 segment derivative formula from §3.5 or §9.6, segment product
irreducibility criterion from §4.2 or §9.7, analytic/square-integrability
assertion from §9.3, classification or exhaustion theorem is used. The
segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` is excluded.
Every reused derivative theorem remains subject to the operator requirement
of independent acceptance and actual publication. This helper does not
resume, replace or bypass minus exactness task
`b65bc667-6951-4bd5-82af-10fb7046df7f` or Worker 127 controls. It preserves
Worker 157 finite-length task `0717fd42-d711-4f42-8269-f6ae4c8da1e9`,
Worker 357 mixed-product/restriction/Leibniz and raw tensor/partial-derivative
scope, Worker 288 k=0 adapter, and the distinct Workers 864/700 generic
lattice unit `a2baddab-056b-4503-865e-74d58ecb3812`.

### Complete transitive project import closure and fingerprints

| Module | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Langlands.Group.GL.Basic` | `d7867286deba424f8f285ea9712b328b762954307fb31c69d4235c8a7b1f29e1` | `b4831fd91123aea6efd64c1da3dbddc32f0c71c9b3f31c7eaed176e7dc9a3d32` |
| `Langlands.Group.GL.Mirabolic` | `358505b5bb7db8a3c7d1ae8175bddb476a7cba621a8407f4180fc1834160a7a9` | `b7549d1b35fa084279ceafc6dedb466a4914fd9b21434b0cd6a0e3afc03e0399` |
| `Langlands.Group.GL.MirabolicModulusProof` | `9f899e92c826ce169b9fe6157aa0e3d92cb114d838488f2b13fc6cf9adac259f` | `d0e9a06c2d30d4ff5b3b2c139fa92e65f645b424b9f5f3c91e108fb851007e99` |
| `Langlands.Group.GL.MirabolicModulusStatement` | `524d0c7ff5073db5955a72aacf748090e42f68b3f0aa24098db8d67ca5c375bb` | `2390593e4cf2ddd8c9ee205a396cbfeb1acdc8ecc5148161e17a5dc134f790f7` |
| `Langlands.Group.GL.MirabolicProjection` | `48ddcc2f501eebf37b70cfcb26be042530e50b73df1ea5c31f928ac18a48a90c` | `cd1210bd7bf8fb47239171c04d9dd24e1f934efcabdecf2339a5d57517dcb6b9` |
| `Langlands.Group.GL.MirabolicRadical` | `b75812e0f24586a5b6365b6282088886d7f359fcd5bef368136946b5b6137eda` | `183e771f6e76b3094d607822e15effb869cd80bc1666c7e76962e86c27f58eed` |
| `Langlands.Group.GL.Nonarchimedean` | `81e9aee8a06787452e827803cdc32cd1bab00b5988dfddbdf85a9762b79f46bc` | `16db461b54c5a193c29f5319bea7fa2e3d454a5766b2cd94bf8ee0a3a655b042` |
| `Langlands.Group.GL.NonarchimedeanStatement` | `e6c1d5e722bb4ebf86de405f0bf4e57627c19fbe3cc7e4bdfbd5a31b6af1b63c` | `f390f56b1aa616cb1e5226df67f7893e9c33248e51d462197e7461862cfc1a10` |
| `Langlands.Group.GL.NormalizedCharacter` | `31deaadcf15cf03e88fd00e26452df03cc103ca9bae18206dac748b9b6d53568` | `296f42c5aeb400f8d131210db13508fff6f220755b08b8c4b8a6f9c129640507` |
| `Langlands.Group.GL.Padic` | `803a2561ddc85a54c7846a421d37ed5dc61b8974157b02b72c26bc41d96e1722` | `380b41087f6569d499e54580e487d1da0755236b84ec3085649cbc37f7a66d89` |
| `Langlands.Group.GL.RankMaps` | `5cd299ec27e66d96bccc8bd9a67d69ecbbc42974351b143c44838f32dd03de41` | `507811ee6523775ec504dbf4ee4b9b783636fced040a6d1780e709743a393653` |
| `Langlands.Group.GL.UpperUnipotent` | `6c2858fa5f866777a0cd3066f3bba643d3300ef24bc1532a3d034001d9ec28c2` | `bbce6c75bc9a59268b36ee5d4fa0f475b59be64dfc1a396b897cf4937269c02f` |
| `Langlands.Group.HaarModulus` | `1e036132d276a4380b2f5a80e8ac69d81a4726c8f3648169e94ee7db97084f3b` | `e47c8bb2e8b2e3e639005b9a4e866d58630ea301c3776650d1418fa32246a3e8` |
| `Langlands.HarmonicAnalysis.Basic` | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` | `770a9f6e068d76d72fb10ff91ee1a27b66696ebf0c52af23464fb4d0956ffdf6` |
| `Langlands.HarmonicAnalysis.PadicHaarScalingStatement` | `84366b106ce213647dbccdccf6477cf19a01ebefaf549e68f2239424c420b2d2` | `48bf7cd23e6d04220618a8814fb60021d27eea0db5a325f5ba80999f4d7fa76e` |
| `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof` | `7f7abfe921074321491b39fa2b70c827b63b6076ecdf9076b1a2b442ce674b2f` | `53c72042369b1d7b05b17ffe7654eea861c4c8c7c688d754a5c912eb880d1c40` |
| `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` | `56a5614e6c50f3cce0c08d21118e596550591f8e9f506bd3893598ed04591d0c` | `7f2ba889475ac0cf7ed7f10c7da58eb9994daa9e6a1cb36c7c91690a9d6de398` |
| `Langlands.LocalField.Canonical` | `e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48` | `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d` |
| `Langlands.LocalField.Definitions` | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` | `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf` |
| `Langlands.LocalField.Normalization.Definitions` | `b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b` | `dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436` |
| `Langlands.LocalField.Normalization.Proof` | `4efa0826ddc069b2963ab4933716979e5bc7c5c866498047aabfbfc417071ded` | `1c3bf219eca92cd04af13c152757d83b4d92dd9787c334acec773bb51a4ad161` |
| `Langlands.LocalField.Normalization.Statement` | `27f6b841c15cf1e4dffcb40126f95ea329c08d91ab9950d8fe645a94683eedc6` | `245db7bd9d6b10a8e9cb2882021f2d210a396aa1149e9a8adeb9a889bc7d753b` |
| `Langlands.LocalField.Topology` | `09ba251eb70a2455da2a7864c7cd34739adbfa717771adc3a86670d2bd0d791c` | `1c28337c12f885cb438b405d58a077c186b4710d20a1256dc0fe8288b4107992` |
| `Langlands.Representation.Category.Basic` | `6a4781890b642e590206b68b7cea02bc4add8bdfb85e6a29991f73992bbcf706` | `647da2c8e2011decf8c6971c0f4a20a162e6ead265bf4d7448b2045072862ba2` |
| `Langlands.Representation.Category.Twist` | `9fb1bca986f0a1a202a4e3d9e1ac481405646293ece6da63374e447cd85ca740` | `e16d708bc3b312c0a79947852bbf147ea230b0a9b8b9ddbd9f80432833bfcb5d` |
| `Langlands.Representation.Derivative.MirabolicCharacter` | `27ad9768aa1f5ee9f1534e99521462f22cdb280abbcf711b79621d405d654a6d` | `f7b710cddba2ed791d268d8a1644315548f2b64912ffed0138579cbd497fae25` |
| `Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps` | new helper | candidate bundle |
| `Langlands.Representation.Derivative.MirabolicMinus` | `526932155b00d435068485ffb7a8a5d4f565b9729779cebe97cfcf96e894e02e` | `3b6fbca0a52aed7251fab742229c22ded359759b67326d66f69db5c1a9b0e9c9` |
| `Langlands.Representation.Derivative.MirabolicMinusNormalization` | `fdc1fd8583588ba1ca5722d96f91b455ea9dadb494b5d8a22ec9e96d789836c9` | `06468be815383e4f98fe355fb5319430a986d5b93115ad2befd16ac6ac3f515a` |
| `Langlands.Representation.Derivative.MirabolicPlus` | `07129014f7995b8bfc85636fb59192ab88b8b9cff9a63ff862a14fcdc03ab421` | `62e65478b9b3b0007744b3409f7dcaf68275f2fcb9d87f1fc7a2ba7441112798` |
| `Langlands.Representation.Derivative.MirabolicPlusNormalization` | `595ce946b02e177f66379f9f449fadaf8e82ea1eb872dc146dc96543e52d5c0d` | `a4cb8910f86b4dff1dfe1618b5aff3681645c21a6913b3cd3a264c739b29ad3c` |
| `Langlands.Representation.Dual.Definitions` | `53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5` | `bf9972bb15d854ff605ed825fdcdf90734dc924ad0ae33efb6bb4e55a882845a` |
| `Langlands.Representation.Induction.Definitions` | `c4d24368c009c903ea7450a8fc08f3dbeb5dbdb31fc3aabdc394b89b731880cf` | `7e3f0697431e4814007ac100da702a56037c1fd35f01f7c5df5e235d4eac7274` |
| `Langlands.Representation.Jacquet.Coinvariants` | `73e5003712204a35595095b0582ad64d931423aeecec2f6165c4c20d945a4566` | `5e040cb16af3b1c72e0c7f1530881639ab055f9528703b9bc20de1931d098a00` |
| `Langlands.Representation.Jacquet.Localization` | `0b50fec4e9e7ad2561f86c6d7e485e2c3a10b1e1c6f750f10c35f5cfc1b3b6ee` | `2a575f90942a22b363b4184941a2470d33e27ad633afe02aa4aa1b818ae62332` |
| `Langlands.Representation.Jacquet.PositiveCharacter` | `90891bcc752689f5fc8071e63de8598efecfd17987cd5d804b470ff6ac57df4d` | `0fc44a60a88f7d48415d5e2f804c2837de5fc253eb1520a4ddee2f6ff6414f40` |
| `Langlands.Representation.Jacquet.SmoothTwist` | `61f9309e04c330e87ceaf2f948868645d6d668a0d9dfde75d16435ca355a5daa` | `4c8fa6423740da78ca9a07a79872d36139c9823e5ed0befa880912105823fda8` |
| `Langlands.Representation.MatrixCoefficient.Definitions` | `92c0bf57151ef798f1198793a4d685afd175274240c1956b54ce3d10e855b7ae` | `c9fdcc728fe28ed0de403801ed10d861d70dd69994179b4fd14f35662d910955` |
| `Langlands.Representation.MatrixCoefficient.LawsProof` | `f73da4941552a524d5e0116675df291d5e99ae1c59b6bc10b21ce2f0ae0fbbae` | `b517f288c98cb53bcb505562f68a20db15025e1c89de85733fec3c8a501b2f6a` |
| `Langlands.Representation.MatrixCoefficient.LawsStatement` | `bf9b7e4cbef45e07642511fbfb033312f2378714476510549e1c6c9189d570fb` | `c077dcf35c8f1229abc17244c5545fbc17603b1c96ae635ced585c82892d1fdd` |
| `Langlands.Representation.Smooth.Admissibility.CofinalProof` | `b01c589f73cb2488a38477ea95bbb6adda0863507efbcb54e561843e467c112a` | `df9117b7ccc80b412fac95816eda27bb0bb18762909c8b0ec39ff35a9a398b59` |
| `Langlands.Representation.Smooth.Admissibility.CofinalStatement` | `df36b24b8e9972dbaa6d810baa13fcb796fbc81465367c8de92a08ca4449a433` | `7cd745762089838e4cbc5d4e6a96718a7bc7632de6b74c2499e84e59af9911e1` |
| `Langlands.Representation.Smooth.Definitions` | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |
| `Langlands.Representation.Smooth.SmoothPart.Definitions` | `1362c38a196d6657c4d9dd2388e00c77059fc772bdd7f4369e0cbbee19ca4a47` | `b8775524d5fdc90acf4c52611d96c401e588f6eff68f682843ce999cf414ac60` |
| `Langlands.Representation.Smooth.Transfer.PullbackProof` | `b0502abed8a3551e9a5c542f07605cd66b83649fafbcb38a23b05dddc3e691b6` | `46884ac73c7107c18ce746c2110810d14d19939b7fca6a608670a6c70265ddfb` |
| `Langlands.Representation.Smooth.Transfer.PullbackStatement` | `a5aaff9766d2e8213ffc82b44625f6fb2ec7f20921b7b03da4ad3250849bcb4d` | `694ccbf90e6fea84743fe380fefdcc25cdaacd1294c53bab78298a465e0df17b` |
| `Langlands.Representation.Smooth.Transfer.SubquotientProof` | `8e26bf64cb2eff5bfdc6037d5d6c52650bd92944a1c9ef0b57c4f12cc3b0d1cd` | `c1f909953edfa360eacae0f2f266025e1dc1ae7000755873f9ad5d3d2985eb0b` |
| `Langlands.Representation.Smooth.Transfer.SubquotientStatement` | `d5729f07038515e26eb8d56cc94a982ed8c066a505acea9b1bc2020f4be08c88` | `fea9069973877d67465589b6e5a0d9336d9b1781e7c275c82492a63ce10b3470` |
| `Langlands.Representation.Twist.AdmissibilityProof` | `706ab8ce915e9902ec30d92c2d471cf7e2e79e2012bf524c9c28868403bf0467` | `25f27ae9ae9c290b60794b1790f6cf0ae47594117c0eee6076dd1cef6b7a0d44` |
| `Langlands.Representation.Twist.AdmissibilityStatement` | `c875a02d8f49506749bc2265041879888de7ad0c76428211a20ffc755f7e7127` | `04559a67afac5b26f332a6122fd9c43424b35f6d9fa9adf917a186108b7702c2` |
| `Langlands.Representation.Twist.AlgebraProof` | `15d469011c703f801ddf6810a9104c0588ab917eb2a179ff6360907425c4fad6` | `9d1893be208c8fcbda33b717d999e2767f76eb9068b70f62932fb3de8d0b17b2` |
| `Langlands.Representation.Twist.AlgebraStatement` | `4c643392e7fc949501dc3e36df71fda5e507598d1a8296be6ea43b3768337895` | `9fd167f7518e27a89b19cfe238a977c8ca2146e0554bb8a92b4dd95171c5b504` |
| `Langlands.Representation.Twist.ContinuousCharacterProof` | `ff9b38a8e4ded2734ccaed8429df42e2abbf92e580034a2576ad111899820f8e` | `ba9c6c6026b6b6a6b576b0d71dba2f8ce39625451f884fc7fe0a309bd7191dc9` |
| `Langlands.Representation.Twist.ContinuousCharacterStatement` | `78a1e542d56cbdfe0f0cf448a0010e6ca2f3331fb3af7437e8d03927de7210c0` | `0791b592e84c04c73f41709e1391c23f874061e8991bf57f5bf750dba5367b3a` |
| `Langlands.Representation.Twist.Definitions` | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` | `94e8c64945411e253a2c91a8e1bf52090d6df15a43362b2032717064c6ac49bc` |
| `Langlands.Representation.Twist.RealPower` | `83e415568697155665a471b9690d6504e353648839503a9a500ef10601f88896` | `509f3af473e1897d2b340724874834fae55db09fe14bfe5007dcea7eca6e1023` |
| `Langlands.Representation.Twist.SmoothProof` | `704914497f29af5abae486c96edead39aa8fa267efeae2d061016c36634cac90` | `b5423ba5dfe57fe3f53686c01a19fb27df085454007505922a788e5666c8a1e4` |
| `Langlands.Representation.Twist.SmoothStatement` | `61616bd03710ca5a5c35ba3bb2b4e5793a9f15801ad99a60d7b20bd95ee3de90` | `6e819947725e6a0877bb7d78dba6c2cbe15a6b7f273c4fe531e4ee3fdc31674e` |
| `Langlands.Representation.Twist.SubquotientDefinitions` | `a9bb92883a9272653ba680cdadc8e025d2f1268bd124ccb7d612f26894227584` | `75aac3b4caadfe14697eeb85f8a4ed729b308d33fd8cac2776c50565de53a7c7` |
| `Langlands.Representation.Twist.SubquotientProof` | `99a2a6e8fe25e885daffea5e59aa2c77f4304afa100d564adabcd869754365a9` | `cf6dad59297e353be1f3cdeca307c3c507d4fc0a5d29ac1c4806b7edc22c4cd0` |
| `Langlands.Representation.Twist.SubquotientStatement` | `1c2bae8d080e8c21743d658d1e3a251e4f5c5c997a4ecd2edd77d6d9315d4b7d` | `407963c3e4e87823630f491fca84066dc7d5a0ca1e7c7404d4d1d577905d7732` |
| `Langlands.Representation.Whittaker.Algebraic` | `890e409cf2b4d586912b928755a4a0dc7b72de9d058ede7510482d816dad3906` | `8127b520fe0395c6600d6b72a7340b87edbf38c4ae1ca664546d63452f8e9072` |
| `Langlands.Representation.Whittaker.GeneralLinear` | `5f5057d690e1bac49a27d650a3c9e678b94660efe8e244ed96e869f33488594c` | `f30d2edde346bc5bbdf3103a54c35f205a6be9643d900be6c4fea23ad38a49cc` |
| `Langlands.Topology.CompactNormCharacter` | `6f70b9473d6386cd111d890c4df0bf411842d28dfdc377e38c2c4fe55e8b0fb7` | `3e50c9561e3e7a068e729aec594ce107f572b2858cd859e6c000fcb8c0aef482` |
| `Langlands.Topology.CompactOpen.ConjugationStabilizer` | `937bc745da117c665bcfd701dbef5758e9ad26f1f4268450c895affa53e91507` | `3dc3ce8f96da8e0525890cadbcbc1d85708c5ff797977e09f7d3af0d613a5c83` |
| `Langlands.Topology.CompactOpen.NeighborhoodBasis` | `5b5322b631663241c1295826da02d7a43cc585566124c5a426020c19c642a6b9` | `0b258f936bb5e0d99be3608077bcdc7da3a2b885aaed75b2c273a633fe2cea7e` |
| `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement` | `80d23d1a0faa606af6610f3a306b130c28739e12d51f533c52862fd45a220131` | `f5a2a0045ab6a79fc96e5681a78be891c9f16fcd9514126b87f4625aeb761532` |
| `Langlands.Topology.Nonarchimedean.Subgroup` | `a45ededd3f67a6645df268d1bf9da0cbcac964137c448ef89966630cd4b4c026` | `01724029b2c592535f55fea2ec4a857a7d15d15156063567d1216e1e4b265675` |

### Complete project declaration closure

`Langlands.Group.GL.Basic` (10 names):

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

`Langlands.Group.GL.Mirabolic` (8 names):

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

`Langlands.Group.GL.MirabolicProjection` (30 names):

```text
Langlands.GeneralLinear.Mirabolic.continuous_lastColumn
Langlands.GeneralLinear.Mirabolic.continuous_plusProjection
Langlands.GeneralLinear.Mirabolic.continuous_projection
Langlands.GeneralLinear.Mirabolic.eq_radicalElement_mul_levi
Langlands.GeneralLinear.Mirabolic.ker_projection
Langlands.GeneralLinear.Mirabolic.lastColumn
Langlands.GeneralLinear.Mirabolic.lastColumn_levi
Langlands.GeneralLinear.Mirabolic.lastColumn_mul
Langlands.GeneralLinear.Mirabolic.lastColumn_mul_last
Langlands.GeneralLinear.Mirabolic.plusProjection
Langlands.GeneralLinear.Mirabolic.plusProjection._proof_1
Langlands.GeneralLinear.Mirabolic.plusProjection._proof_2
Langlands.GeneralLinear.Mirabolic.plusProjection._proof_3
Langlands.GeneralLinear.Mirabolic.plusProjection._proof_4
Langlands.GeneralLinear.Mirabolic.plusSubgroup
Langlands.GeneralLinear.Mirabolic.projection
Langlands.GeneralLinear.Mirabolic.projection._proof_1
Langlands.GeneralLinear.Mirabolic.projection._proof_2
Langlands.GeneralLinear.Mirabolic.projection._proof_3
Langlands.GeneralLinear.Mirabolic.projection._proof_4
Langlands.GeneralLinear.Mirabolic.projection._proof_5
Langlands.GeneralLinear.Mirabolic.projection._proof_6
Langlands.GeneralLinear.Mirabolic.projection._proof_7
Langlands.GeneralLinear.Mirabolic.projection._proof_8
Langlands.GeneralLinear.Mirabolic.projection._proof_9
Langlands.GeneralLinear.Mirabolic.projection_eq_one_iff
Langlands.GeneralLinear.Mirabolic.projection_levi
_private.Langlands.Group.GL.MirabolicProjection.0.Langlands.GeneralLinear.Mirabolic.lastRow
_private.Langlands.Group.GL.MirabolicProjection.0.Langlands.GeneralLinear.Mirabolic.upperLeft_mul
_private.Langlands.Group.GL.MirabolicProjection.0.Langlands.GeneralLinear.Mirabolic.upperLeft_one
```

`Langlands.Group.GL.MirabolicRadical` (38 names):

```text
Langlands.GeneralLinear.Mirabolic.continuous_levi
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
Langlands.GeneralLinear.Mirabolic.mem_radical
Langlands.GeneralLinear.Mirabolic.radical
Langlands.GeneralLinear.Mirabolic.radical._proof_1
Langlands.GeneralLinear.Mirabolic.radical._proof_2
Langlands.GeneralLinear.Mirabolic.radical._proof_3
Langlands.GeneralLinear.Mirabolic.radicalCoordinates
Langlands.GeneralLinear.Mirabolic.radicalElement
Langlands.GeneralLinear.Mirabolic.radicalElement_bottom
Langlands.GeneralLinear.Mirabolic.radicalElement_coordinates
Langlands.GeneralLinear.Mirabolic.radicalElement_first
Langlands.GeneralLinear.Mirabolic.radicalElement_last
Langlands.GeneralLinear.Mirabolic.radicalToUpperUnipotent._proof_1
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_bottom
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_first
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_last
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit._proof_1
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit._proof_2
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.continuous_leviEquiv_symm
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.fixedColumn_mul
_private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.levi_conjugate_mem
```

`Langlands.Group.GL.Nonarchimedean` (10 names):

```text
Langlands.valuativeGeneralLinearNonarchimedean
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.existsSmallMatrix
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.finitePiBasis
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.matrixZeroBasis
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeBallOpen
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid._abel_1
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid._proof_1
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid._proof_2
_private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoidOpen
```

`Langlands.Group.GL.NonarchimedeanStatement` (1 names):

```text
Langlands.ValuativeGeneralLinearNonarchimedean
```

`Langlands.Group.GL.NormalizedCharacter` (13 names):

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

`Langlands.Group.GL.Padic` (4 names):

```text
Langlands.PadicField.TopologicalData.generalLinearDeterminant
Langlands.PadicField.TopologicalData.generalLinearDeterminant._proof_1
Langlands.PadicField.TopologicalData.generalLinearTopologicalGroup
Langlands.PadicField.TopologicalData.generalLinearTopology
```

`Langlands.Group.GL.RankMaps` (23 names):

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

`Langlands.HarmonicAnalysis.Basic` (4 names):

```text
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.continuous_toFun
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.mk
Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar
```

`Langlands.LocalField.Definitions` (10 names):

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

`Langlands.LocalField.Normalization.Definitions` (9 names):

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

`Langlands.LocalField.Normalization.Proof` (12 names):

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

`Langlands.Representation.Category.Basic` (10 names):

```text
Langlands.SmoothRep
Langlands.SmoothRep.hom
Langlands.SmoothRep.instAddCommGroupVObjRepSmoothRepProperty
Langlands.SmoothRep.instModuleVObjRepSmoothRepProperty
Langlands.SmoothRep.isSmooth
Langlands.SmoothRep.of
Langlands.SmoothRep.ofHom
Langlands.SmoothRep.representation
Langlands.SmoothRep.toRep
Langlands.smoothRepProperty
```

`Langlands.Representation.Category.Twist` (5 names):

```text
Langlands.SmoothRep.twist
Langlands.SmoothRep.twist._proof_1
Langlands.SmoothRep.twistFunctor
Langlands.SmoothRep.twistFunctor._proof_1
Langlands.SmoothRep.twistFunctor._proof_2
```

`Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps` (25 names):

```text
Langlands.Derivative.Mirabolic.HighestLayer.mem_range_phiPlusPost
Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost
Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_1
Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_2
Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_3
Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_4
Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost_eval
Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost_injective
Langlands.Derivative.Mirabolic.HighestLayer.psiMinusQuotient_psiPlusBaseEmbedding
Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding
Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding._proof_1
Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding_injective
Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding_quotient
Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding_range
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_1
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_2
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_3
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_4
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_5
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_6
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_7
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseLinear
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseLinear._proof_1
_private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseLinear._proof_2
```

`Langlands.Representation.Derivative.MirabolicMinus` (20 names):

```text
Langlands.Derivative.Mirabolic.continuousPullback
Langlands.Derivative.Mirabolic.continuousPullback._proof_1
Langlands.Derivative.Mirabolic.continuousPullbackFunctor
Langlands.Derivative.Mirabolic.continuousPullbackFunctor._proof_1
Langlands.Derivative.Mirabolic.continuousPullbackFunctor._proof_2
Langlands.Derivative.Mirabolic.continuousPullbackMap
Langlands.Derivative.Mirabolic.continuousPullbackMap._proof_1
Langlands.Derivative.Mirabolic.continuousPullbackMap._proof_2
Langlands.Derivative.Mirabolic.isOpen_ker_psiMinusCharacter
Langlands.Derivative.Mirabolic.psiMinus
Langlands.Derivative.Mirabolic.psiMinusCharacter
Langlands.Derivative.Mirabolic.psiMinusCharacter._proof_1
Langlands.Derivative.Mirabolic.psiMinusQuotient
Langlands.Derivative.Mirabolic.psiMinusQuotient_surjective
Langlands.Derivative.Mirabolic.psiMinusUnnormalized
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_1
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_2
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_3
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_4
Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_5
```

`Langlands.Representation.Derivative.MirabolicPlus` (28 names):

```text
Langlands.Derivative.Mirabolic.continuous_thetaPlus
Langlands.Derivative.Mirabolic.isOpen_ker_thetaPlus
Langlands.Derivative.Mirabolic.phiPlusEval
Langlands.Derivative.Mirabolic.phiPlusEval_covariant
Langlands.Derivative.Mirabolic.phiPlusEval_exists_openSubgroup
Langlands.Derivative.Mirabolic.phiPlusEval_injective
Langlands.Derivative.Mirabolic.phiPlusEval_isCompact_quotientSupport
Langlands.Derivative.Mirabolic.phiPlusMk
Langlands.Derivative.Mirabolic.phiPlusUnnormalized
Langlands.Derivative.Mirabolic.phiPlusUnnormalized._proof_1
Langlands.Derivative.Mirabolic.plusLastCoordinate
Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_1
Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_2
Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_3
Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_4
Langlands.Derivative.Mirabolic.plusTwistFunctor
Langlands.Derivative.Mirabolic.plusTwistFunctor._proof_1
Langlands.Derivative.Mirabolic.plusTwistFunctor._proof_2
Langlands.Derivative.Mirabolic.plusTwistFunctor._proof_3
Langlands.Derivative.Mirabolic.plusTwistRepresentation
Langlands.Derivative.Mirabolic.plusTwistRepresentation._proof_1
Langlands.Derivative.Mirabolic.psiPlusUnnormalized
Langlands.Derivative.Mirabolic.psiPlusUnnormalized._proof_1
Langlands.Derivative.Mirabolic.psiPlusUnnormalized._proof_2
Langlands.Derivative.Mirabolic.thetaPlus
Langlands.Derivative.Mirabolic.thetaPlusContinuous
Langlands.Derivative.Mirabolic.thetaPlusContinuous._proof_1
Langlands.Derivative.Mirabolic.thetaPlus_isOpen_ker
```

`Langlands.Representation.Derivative.MirabolicPlusNormalization` (19 names):

```text
Langlands.Derivative.Mirabolic.isOpen_ker_phiPlusCharacter
Langlands.Derivative.Mirabolic.isOpen_ker_psiPlusCharacter
Langlands.Derivative.Mirabolic.phiPlus
Langlands.Derivative.Mirabolic.phiPlusCharacter
Langlands.Derivative.Mirabolic.phiPlusHaarHalf._proof_1
Langlands.Derivative.Mirabolic.phiPlusHaarHalf._proof_6
Langlands.Derivative.Mirabolic.phiPlusNormalizedEval
Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_covariant
Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_exists_openSubgroup
Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_injective
Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_isCompact_quotientSupport
Langlands.Derivative.Mirabolic.phiPlusNormalizedMk
Langlands.Derivative.Mirabolic.psiMinusCharacter.eq_1
Langlands.Derivative.Mirabolic.psiPlus
Langlands.Derivative.Mirabolic.psiPlusCharacter
Langlands.Derivative.Mirabolic.psiPlusCharacter._proof_1
Langlands.Derivative.Mirabolic.psiPlusCharacter_eq_inv
Langlands.Derivative.Mirabolic.psiPlusCharacter_mul_psiMinusCharacter
Langlands.Derivative.Mirabolic.psiPlusHaarHalf._proof_6
```

`Langlands.Representation.Induction.Definitions` (45 names):

```text
Langlands.Induction.CompactFunctions
Langlands.Induction.EquivariantFunctions
Langlands.Induction.EquivariantFunctions._proof_1
Langlands.Induction.LeftQuotient
Langlands.Induction.SmoothFunctions
Langlands.Induction.SmoothRep
Langlands.Induction.compactFunctionOf
Langlands.Induction.compactFunctions
Langlands.Induction.compactFunctions._proof_1
Langlands.Induction.compactFunctions._proof_2
Langlands.Induction.compactFunctions._proof_3
Langlands.Induction.compactFunctions._proof_4
Langlands.Induction.compactFunctions._proof_5
Langlands.Induction.compactFunctions._proof_6
Langlands.Induction.compactFunctions._simp_1
Langlands.Induction.compactFunctions._simp_2
Langlands.Induction.compactFunctionsAddCommGroup
Langlands.Induction.compactInduced
Langlands.Induction.compactInducedMap
Langlands.Induction.compactInducedMap._proof_1
Langlands.Induction.compactInducedMap._proof_2
Langlands.Induction.compactInduced_smooth
Langlands.Induction.compactInductionFunctor
Langlands.Induction.compactInductionFunctor._proof_1
Langlands.Induction.compactInductionFunctor._proof_2
Langlands.Induction.compactInductionFunctor._proof_3
Langlands.Induction.compactSubrepresentation
Langlands.Induction.compactSubrepresentation._proof_1
Langlands.Induction.equivariantAction
Langlands.Induction.eval
Langlands.Induction.quotientMap
Langlands.Induction.quotientRight
Langlands.Induction.quotientRight._proof_1
Langlands.Induction.quotientSupport
Langlands.Induction.smoothFunctionOf
Langlands.Induction.smoothFunctionOf._proof_1
Langlands.Induction.smoothFunctionsAddCommGroup
Langlands.Induction.smoothInduced
Langlands.Induction.smoothInducedMap
Langlands.Induction.smoothInduced_smooth
_private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.compact_map_mem
_private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.continuous_quotientRight
_private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.eval_locallyConstant
_private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.preimage_quotientSupport
_private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.quotientSupport_closed
```

`Langlands.Representation.Jacquet.Localization` (35 names):

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

`Langlands.Representation.Smooth.Definitions` (3 names):

```text
Langlands.IsSmooth
Langlands.IsSmoothVector
Langlands.fixedVectors
```

`Langlands.Representation.Smooth.SmoothPart.Definitions` (15 names):

```text
Langlands.smoothInclusion
Langlands.smoothInclusion._proof_1
Langlands.smoothInclusion._proof_2
Langlands.smoothLift
Langlands.smoothLift._proof_1
Langlands.smoothLift._proof_2
Langlands.smoothMap
Langlands.smoothMap._proof_1
Langlands.smoothPart
Langlands.smoothSubrepresentation
Langlands.smoothSubrepresentation._proof_1
Langlands.smoothVectors
Langlands.smoothVectors._proof_1
Langlands.smoothVectors._proof_2
Langlands.smoothVectors._proof_3
```

`Langlands.Representation.Smooth.Transfer.PullbackProof` (2 names):

```text
Langlands.isSmoothVector_comp
Langlands.isSmooth_comp
```

`Langlands.Representation.Smooth.Transfer.SubquotientProof` (2 names):

```text
Langlands.isSmoothVector_map
Langlands.isSmooth_of_surjective
```

`Langlands.Representation.Twist.ContinuousCharacterProof` (2 names):

```text
Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
Langlands.isOpen_ker_of_continuous_complex_character
```

`Langlands.Representation.Twist.Definitions` (7 names):

```text
Langlands.twist
Langlands.twist._proof_1
Langlands.twist._proof_2
Langlands.twist._proof_3
Langlands.twistIntertwining
Langlands.twistIntertwining._proof_1
Langlands.twistIntertwining._proof_2
```

`Langlands.Representation.Twist.RealPower` (5 names):

```text
Langlands.isOpen_ker_realPowerCharacter
Langlands.ker_le_realPowerCharacter_ker
Langlands.positiveUnitsToComplex
Langlands.realPowerCharacter
Langlands.realPowerCharacter_neg
```

`Langlands.Representation.Twist.SmoothProof` (2 names):

```text
Langlands.isSmoothVector_twist_iff
Langlands.isSmooth_twist_iff
```

`Langlands.Topology.Nonarchimedean.Subgroup` (1 names):

```text
Langlands.subgroupNonarchimedean
```
