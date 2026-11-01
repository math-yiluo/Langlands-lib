# Exactness of the actual F and left exactness of the actual I

The theorem `Langlands.Algebra.nondegenerateFInductionExactness` proves the
closed published `Langlands.Algebra.NondegenerateFInductionExactnessTheorem`.
It gives the full `SequenceExact` of `NondegenerateTensorFunctor.F` and the
full `SequenceLeftExact` of `RenardHomFunctors.I`, including the appropriate
boundary monomorphism and epimorphism for every tested one-sided exact sequence.
Workers 595 and 695 developed the proof together; Worker 595 supplies the
concrete categorical criteria, F argument and final assembly, and Worker 695
the direct I argument in the companion `NondegenerateILeftExactness`.

Renard I.2.4 states exactness of F and left exactness of I in the complex-algebra
setting. This result is the published internal arbitrary-ring additive
formulation, for precisely the specified original left A-action on B and the
right regular B-action. The supplied commutation and nondegenerate-bimodule
witnesses remain tied to those actions. Ring universes `uA`, `uB` and source
carrier universe `v` are independent. F has the actual tensor carrier
`Tensor B B N`, and I has the actual nondegenerate part of
`NonUnitalModuleHom A B M`, both in carrier universe `max uB v`.
The source and target categories use exactly the named
`NondegenerateModuleCat.abelian` structures from the statement and their
inherited preadditive structures.

The intrinsic companion `NondegenerateModuleExactnessConcrete` expresses
categorical exactness by preimages of elements in the kernel, and the boundary
mono/epi by injectivity/surjectivity of original additive maps. It derives these
criteria from the published exact inclusion, ambient range/kernel criterion,
and integer unitization equivalence. The statement module and its complete
import closure are unchanged.

For F, the published `RegularTensorContraction.contraction` is used only as an
additive map. Its injectivity is the published local-unit result. Its
surjectivity for a nondegenerate N follows by choosing an idempotent e fixing
n: the pure tensor e tensor n contracts to n. Its published naturality
identifies contraction after the actual F tensor map with the original map
after contraction. For an exact triple, contract a kernel element, lift it
through the original first map, choose a tensor preimage of that lift, and use
contraction injectivity to recover the required equality. The same naturality
and bijectivity transfer injectivity and surjectivity, giving both boundary
conditions. This proves exactness for every triple, which supplies both tests
of `SequenceExact`.

For I, the companion constructs lifts directly through an injective original
first map. Evaluating a Hom element in the kernel yields pointwise preimages
by original exactness. Injectivity forces those preimages to preserve zero,
addition and the specified A-action. The same B-idempotent that fixes the
original Hom element fixes the lift, so it lies in the actual nondegenerate
part for action `(b • h)(b') = h(b' * b)`. Evaluation also proves injectivity
of restricted postcomposition. The concrete criteria give both exactness and
the first boundary monomorphism required by `SequenceLeftExact`.

The final theorem combines these two proofs with no additional premise.
This proof does not construct an A-action on the source B-module N and does
not invoke a categorical adjunction or a change of carrier universe. General
tensor/Hom exactness, the independent P/pseudo-F family, preservation of
injectivity, and coefficient or complex-linear comparisons remain separate
results. The additive generalization is justified by the implemented use of
only the original ring actions, additive maps, idempotents and the published
categorical criteria.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are the original conventions, printed pp.5–7 / PDF11–13;
tensor and Hom constructions, printed pp.15–18 / PDF21–24; regular-tensor
comparison (I.2.3.3), printed p.17 / PDF23; the exactness theorem I.2.4, printed
pp.18–19 / PDF24–25; and the one-sided exactness definitions A.VIII.1,
printed p.266 / PDF272. These passages were read directly. The source proves
right exactness by tensor exactness and left exactness of F by contraction;
the implemented proof uses contraction for both sides and a direct Hom lift.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–2 and PDF18–19. Its corrected adjunction orientation agrees
with the 2026 edition. The corrected 2026 source governs this proof; the 2010
errata is supplementary.
