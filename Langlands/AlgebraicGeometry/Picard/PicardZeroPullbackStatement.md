# Pullback preservation of the relative geometric Picard-zero condition

`Langlands.AbelianScheme.PicardZeroPullbackStatement` is a proposition
definition. It quantifies over every scheme `S : Scheme.{u}`, abelian scheme
`A/S`, two `S`-schemes `T` and `U`, morphism `h : T ⟶ U` in the slice
category, and actual rigidified line bundle `L : RigidifiedFamily A U`.
It asserts that `IsPicardZeroFamily A L` implies the same condition for the
actual relative rigidified pullback of `L` along `h`.

The source family has total space `U ×_S A`, and the target family has total
space `T ×_S A`. The pullback is along the existing `relativeSpace` map and
uses the canonical rigidification comparison already constructed in
`RigidifiedLineBundle.relativePullback`. In each family, the tested
geometric-fibre condition uses `familyLineBundle` to pull across the inverse
canonical symmetry to the chosen abelian-scheme base change `A ×_S U` or
`A ×_S T`. Thus the target requires preservation for those actual scheme
maps and bundles, with no chosen replacement fibre or assumed equivalence.

There are no smoothness, flatness, surjectivity or finiteness hypotheses on
`h`, and no noetherian or projectivity hypothesis on `S`. Smoothness,
properness and geometric connectedness are the existing properties of `A`.
No rigidified pullback coherence hypothesis is needed just to state this
one-map preservation result.

This is a derived compatibility target. The original source is Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §1, (6.2), printed p.88 (PDF p.92), describes the actual
pullback of relative rigidified line bundles. The point formula on printed
p.95 (PDF p.99) and Corollary (7.22), printed p.106 (PDF p.110), motivate
the geometric-fibre translation-invariance condition selected by the parent
contract.

The cited passages do not state this particular Lean compatibility target.
Its mathematical rationale is that a geometric point `Spec K → T` also
gives a geometric point of `U` by composition with `h.left`. The two resulting
geometric fibres of `A` are canonically isomorphic as group schemes, and the
restricted line bundles correspond under that isomorphism. A proof must
establish these identifications, their compatibility with the actual
translations, and the necessary pullback comparisons. This explanation is
the provenance of the derived target, not a formal proof supplied here.

The module contains no proof or axiom of the proposition. Its separate proof
task must retain the exact target. Once proved, quotient induction gives
preservation of `IsPicardZeroClass`; together with the separate rigidified
pullback coherence proposition, this enables the geometric Picard-zero
subfunctor. Tensor-product closure, identity-component comparison and
representability remain distinct obligations.
