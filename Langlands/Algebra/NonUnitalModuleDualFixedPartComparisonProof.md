# Full-fixed and right-corner duality comparisons

Worker 691 proves the unchanged published proposition
`Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonStatements.FixedPartComparisons`
as the entire type of `fixedPartComparisons` in
`Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonProof`.
The algebra, original source carrier and original target carrier have
independent universes `uA`, `uM` and `uN`. The final unapplied assignments
check the closed theorem generically and at `(0,1,2)` and `(2,1,0)`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition of 9 July 2026, I.4.1, printed pp.22–23 /
one-based PDF pp.28–29, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof implements the identification `(e·M)* ≃ M*·e ≃ M~·e` from the
idempotent splitting. The source defines the full dual and its nondegenerate
part on PDF p.28, and proves the identification on PDF p.29. Original
nonunital conventions (printed pp.5–7 / PDF pp.11–13), recovered complex
scalars (I.2.1, printed p.14 / PDF p.20), and the splitting (I.3.1, printed
p.19 / PDF p.25) were read directly.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF pp.1–2. Its nearby correction invokes the I.4.1
isomorphisms in the admissibility argument; it does not alter this
restriction and extension construction. The 2026 edition governs.
No source-specific erratum file was found under the project or Library
notes. The supplementary errata are not substituted for the original.

The entire-map pins, both scalar interfaces and eight explicit naturality
squares are derived formulations in the imported statement. Renard does
not list them individually. The proof uses the published functional
formulas and the original intertwining law.

## Original carriers, actions and scalars

Write R = `RightFixedPart hA hM e`, F = `FullRightFixedPart hA hM e`,
O = `Module.Dual ℂ (FixedPart e M)`, and
K = `Idempotent.Corner (oppositeIdempotent e)`. These are the original
published carriers, without any replacement by abstract isomorphic spaces.

The proof installs `NonUnitalModuleDual.fullAction hA hM` on the full dual
and `NonUnitalModuleDual.dualAction hA hM` on its actual nondegenerate
subtype. They express right A-actions as left actions of `Aᵐᵒᵖ`.
The original action on M remains the supplied `NonUnitalModule A M`.
The full dual is formed using `NondegenerateScalars.complexModule hA hM`;
no complex module structure on M is an input.

On `FixedPart e M`, R and F, the selected complex structures are exactly
`NonUnitalModuleCorner.complexModule hA hM e`,
`rightFixedModule hA hM e` and `fullRightFixedModule hA hM e`.
The K-actions on R and F are the original fixed-part corner actions.
The K-action on O is exactly `fixedPartDualCornerModule hA hM e`,
precomposition with `cornerUnop e a` acting on the original fixed part.
All corresponding structures are installed for N in the naturality proof.

## Inverses and equivalences

The four equations in `FullFixedInverseIdentities` hold by linear-map
extensionality followed by one or two applications of subtype
extensionality. Both `toFullFixed` and `fromFullFixed` preserve the entire
full-dual functional. Their corner versions have the same functions.
The local equivalences E over ℂ and C over K use
`LinearEquiv.ofLinearMap` with precisely these maps and inverse equations.
Their forward and inverse map pins, and their additive-map agreement,
are definitional equalities. Additive-map extensionality proves the two
inclusion equations into the actual full dual; both sides keep the
original functional.

The published
`NonUnitalModuleDualFixedPart.fixedPartDuality` supplies the basic complex
inverse pair for `restriction` and `extension`. This proof reuses those
equations to build the complex R/O equivalence B. Evaluation of the same
inverse equations gives the corner-linear inverse pair and hence BC,
whose maps are `restrictionCorner` and `extensionCorner`.

The three equivalences in `CornerEquivalences` are BC,
`E.symm.trans B` and `C.symm.trans BC`. Their entire forward and inverse
linear maps are definitionally the prescribed restriction/extension
composites, and the two composite equivalences have identical underlying
additive maps in both directions.

## Naturality and additional scalar linearity

For an independently sized original nondegenerate N and an original
intertwiner f, the proof names exactly the specified maps RC, SC and Dℂ:
the fixed-part restriction of `pullback`, the fixed-part restriction of
`fullPullback`, and the dual of `restrictLinear`, respectively.

It constructs Rℂ and Sℂ using the functions RC and SC and their existing
additivity. Complex homogeneity follows by subtype and functional
extensionality: complex scalars on the included functionals are pointwise,
and pullback is precomposition with f. It constructs DC from Dℂ with the
same additive map. For corner homogeneity, evaluation at a fixed element
reduces the claim to equality of the two fixed-subgroup elements whose
underlying values are

```text
a.val.unop • f(x.val) = f(a.val.unop • x.val).
```

This is the original `f.map_smul` law, reversed. Thus all three additional
scalar-linear representatives are constructed, and their entire
additive-map pins are definitional.

The eight entire-linear-map squares are then proved in the order of the
published target. The four R/F squares, over ℂ and over K in both
directions, follow by subtype extensionality because pullback keeps the
same included functional along either route. The R/O restriction square
over K and the F/O restriction square over ℂ follow by evaluating at a
fixed element: both routes give the original functional evaluated at
`f(x.val)`.

For the R/O extension square over K and the F/O extension square over ℂ,
evaluation at m reduces both claims to

```text
ell(projection e (f m)) = ell(f_e(projection e m)),
```

where `f_e = NonUnitalModuleCorner.restrictLinear hA hM hN e f`.
Subtype extensionality and `f.map_smul (e : A) m` identify the arguments.
This expresses preservation of the idempotent splitting by the original
intertwiner.

## Scope

The original nonunital actions and all named recovered scalar structures are
retained. No original complex module, dimension bound, unit, nontriviality,
faithfulness, anti-involution, admissibility or reflexivity is assumed.
The proof includes zero algebras, zero modules and the zero idempotent.
The basic complex comparison from task
`9e60fa95-77ba-4cbc-9994-ad43fc47fc19` remains a reused separate result.
Exactness, bidual injection, reflexivity, admissibility, I.4.2 functor
comparisons, tensor smoothing and completion are outside this theorem.

Worker 691 authored this comparison proof. The imported basic proof
retains Worker 1149's attribution, and the imported constructions and
statement retain their existing authorship. No imported file is edited.
