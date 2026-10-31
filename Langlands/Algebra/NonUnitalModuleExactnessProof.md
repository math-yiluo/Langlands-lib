# Exactness through the original nonunital stable range and kernel

Worker 633 proves the published closed proposition
`Langlands.Algebra.NonUnitalModuleExactnessStatement.{uA,uM}` in the theorem
`Langlands.Algebra.nonUnitalModuleExactnessStatement`. The proof imports the
unchanged statement by Lean name and uses the existing original-action category,
its pointwise zero maps, and the published stable range and kernel.

## Implemented argument

The established ambient abelian structure supplies homology for every short
complex. Mathlib's
`ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero` therefore identifies
`S.Exact` with vanishing of the selected kernel-to-cokernel composite.
The first helper theorem cancels the isomorphisms `kernelIsoConcrete` and
`cokernelIsoConcrete`, using their published arrow identities. This gives the
equivalent equation

```lean
concreteKernelι S.g ≫ concreteCokernelπ S.f = 0
```

The second helper proves equality of the original stable subgroups by
membership extensionality. Every vector in the range is sent to zero by `S.g`,
because the short complex supplies `S.f ≫ S.g = 0`. Conversely, evaluate the
vanishing concrete composite on a kernel vector. Its coset in the quotient by
the stable range is zero, so `concreteCokernelπ_eq_zero_iff` places the vector
in that range. If range and kernel are equal, every kernel vector has zero
coset, and pointwise extensionality makes the concrete composite zero.
The closed theorem then quantifies over the acting ring, its structure and the
short complex exactly as in the published statement.

## Scope and provenance

The ring universe `uA` and carrier universe `uM` are independent. The file
includes the complete unapplied theorem interface and both unequal
specializations `(0,1)` and `(1,0)`. No original unit-action law, commutativity,
nondegeneracy, idempotentedness, nontriviality, scalar-field or finiteness
hypothesis is introduced. Homology and ambient abelianness are supplied by
published instances, rather than assumed in the closed theorem. The proof
uses the actual original stable subgroups and their inherited actions.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 633 read the module conventions at printed pp.5–7/PDF11–13 and the
exact-sequence paragraph in A.VI.2, printed p.262/PDF268. These conventions
allow nonunital rings and actions without a unit law even over unital rings;
nondegenerate modules are a separately specified subcategory. The exact
correspondence proved here is internal derived content, rather than a
numbered theorem printed in this form. Its proof specializes the pinned
Mathlib categorical criterion to the published concrete kernel and quotient
of the original action.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was
read at PDF18–19. It concerns the 2010 edition and does not replace the
governing 2026 original. No project errata file is present for either source.
The public note `notes/renard/appendix-a-corrections.md` was also read; its
defective full-subcategory criterion is not used by this proof. Mathlib's
criterion was read in `Algebra/Homology/ShortComplex/Exact.lean` at commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The result establishes the accepted exactness proposition. Concrete
image/coimage comparisons, nondegenerate-category constructions and exactness
of other functors retain their separate units.
