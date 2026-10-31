# Simultaneous scalar eigensubsheaves

This internal construction cuts out an actual subsheaf of an actual module
sheaf by simultaneous scalar eigenconditions. Given `M : S.Modules`, a ring
action `ρ : R →+* End M` and a scalar character `χ : R →+* Γ(S, ⊤)`,
its sections on `U` are exactly the sections `x` satisfying
`(ρ a).app U x = restrictScalar U (χ a) • x` for every `a : R`.
The rings and schemes may have nilpotents. No flatness or finiteness is used.

`scalarEigenSections` constructs the actual section submodule.
`scalarEigenPresheafSubmodule` proves its restriction stability by naturality
of the actual action and restriction of the scalar section.
`scalarEigenSubmodule` proves local membership by separation of the ambient
module sheaf. Mathlib's submodule-to-sheaf construction then gives
`scalarEigensheaf`, with its actual monomorphism `scalarEigensheafι`.

`scalarEigensheafMap` restricts an actual equivariant morphism to these
subsheaves. Its formula on sections is the original map on the underlying
section. The inclusion square, identity law and composition law are proved
for those constructed maps. `scalarEigensheafIso` restricts an actual
equivariant isomorphism, deriving equivariance of its inverse and both inverse
laws from the original isomorphism.

This is an internal derivation using actual module sheaves, scalar
multiplication, submodules and sheaf separation. It does not assert a tensor
factor interpretation, a direct-sum splitting, local freeness, fixed rank,
or preservation under arbitrary base change.
