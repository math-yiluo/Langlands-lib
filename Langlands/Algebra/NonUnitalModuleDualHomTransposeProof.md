# Proof of the prescribed natural dual-Hom equivalence

This module proves exactly
`Langlands.Algebra.NonUnitalModuleDualHomTransposeStatements.DualHomTranspose`
with five independent universes. Its entry theorem is
`Langlands.Algebra.NonUnitalModuleDualHomTransposeProof.dualHomTranspose`.
It imports the published statement module and leaves that module and all its
imports unchanged.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The unnumbered lemma and formula (I.4.2.1), printed p.24 / one-based PDF p.30,
assert the natural isomorphism given by `psi(w)(v) = phi(v)(w)`.
The original nonunital conventions are on printed pp.5–7 / PDF pp.11–13;
the recovered complex scalars and pointwise Hom scalars are in I.2.1,
printed p.14 / PDF p.20; the actual nondegenerate duals are in I.4.1,
printed pp.22–23 / PDF pp.28–29. These pages were read for this proof.
The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, was also read for the nearby corrections. Those pages do not
replace this formula; the 2026 edition governs.

Renard proves the lemma using two tensor-Hom identifications. This module
implements a direct proof from the full-functional evaluation formulas of
the already published `NonUnitalModuleDualHomTranspose` construction. Its
helper declarations are derived internal content packaging that formula,
its inverse, scalar linearity and naturality. They add no mathematical
hypotheses to the published statement.

The proof retains exactly the original right and left Hom carriers
`R hA hV hW` and `L hA hV hW`, into the actual nondegenerate dual subtypes.
It selects the inherited `fullAction` and the published double-opposite
`rightDualAction` where required. All linear maps and equivalences use
precisely `rModule` and `lModule`. No complex module on an original carrier
is supplied as an input.

`S_T` proves `S (T phi) = phi` by extensionality of original intertwiners,
then extensionality of the actual dual subtype. At each `v` and `w`, the
two swaps return `(phi v).val w`, so the final evaluation equality is
reflexive. `T_S` uses the same argument for a left intertwiner and explicitly
selects `rightDualAction`. `inverseIdentities` applies linear-map
extensionality to these results, proving both entire linear-map composite
identities of the published `InverseIdentities` proposition.

`equiv` bundles `T` as its forward linear map and `S` as its inverse
function; `S_T` and `T_S` supply the inverse laws. The forward linear map,
inverse linear map and their functions agree definitionally with the
published maps. `prescribedEquivalence` supplies this equivalence and all
six required equalities. Its two additive pins use the published
`T_toAddMonoidHom` and `S_toAddMonoidHom` equalities, retaining precisely
`transposeAdd` and `reverseAdd` as entire additive maps.

For original intertwiners `f : V' → V` and `g : W' → W`, `rLinear` and
`lLinear` bundle exactly the functions and addition laws of the published
`Rfg` and `Lfg`. Complex scalar preservation is proved, rather than assumed.
For `rLinear`, extensionality of intertwiners and dual functionals reduces
the scalar identity to the two pointwise laws `rModule_smul_val` at the
source and target Hom spaces. Both sides evaluate to
`c • (phi (f v')).val (g w')`. The proof of `lLinear` similarly uses
`lModule_smul_val`; both sides evaluate to
`c • (psi (g w')).val (f v')`. The named transported target action is
selected explicitly. `rLinear_toAddMonoidHom` and
`lLinear_toAddMonoidHom` identify the whole additive maps with exactly
`Rfg` and `Lfg` by reflexivity.

`equiv_natural` and `equiv_symm_natural` prove the two entire complex-linear-map
squares. Linear-map extensionality reduces each square to evaluation at an
original intertwiner. The published equalities `T_natural` and `S_natural`
of entire additive maps give precisely those identities. Thus naturality
is established for the prescribed components and the actual composition
maps. `naturality` supplies the constructed linear maps, the same prescribed
equivalence at both carrier pairs, all additive and linear pins, and both
squares as witnesses of the unchanged `Naturality` proposition.

Finally, `dualHomTranspose` introduces every quantified original structure
of the closed published target, combines the inverse and prescribed-equivalence
proofs, and applies `naturality` at every independently sized pair of
additional carriers and every original pair of intertwiners. It has no
hypotheses outside that target. The algebra and four carrier universes are
independent; closed examples additionally check the entire theorem at
(0,1,2,3,4) and (4,3,2,1,0). Arbitrary dimensions and all permitted zero cases
are retained. No unit, nontriviality, faithful action, anti-involution,
admissibility or reflexivity is used.

This result proves formula (I.4.2.1) and the exact derived interfaces of the
published target. It makes no further assertion about the surrounding
forgetful, pseudoforgetful or induction comparisons, tensor-Hom or completion
comparisons, fixed-part duality, bidual injection, exactness or admissibility.
Worker 1187 authored this proof and its documentation.
