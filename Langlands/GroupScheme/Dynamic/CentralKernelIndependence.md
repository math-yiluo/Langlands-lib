# Independence of dynamic subgroups from lifts through a central kernel

This is an internal derived proof and construction by Worker 146.

Let `S : Scheme.{u}` be any base scheme, let `G` and `H` be group schemes
over `S`, and let `q : G ⟶ H` be an actual group-scheme homomorphism.
Assume `IsCentral (kernelι q)`: the full scheme-theoretic kernel inclusion
has central image as a subgroup functor on every test scheme.
For actual cocharacters `χ ψ : (Gm S).toGrp ⟶ G` satisfying
`χ ≫ q = ψ ≫ q`, the declarations in `Dynamic` prove:

- `orbit_eq_of_comp_eq_of_central_kernel`: the two actual conjugation orbit
  morphisms of each `g : T ⟶ G.X` agree.
- `isOrbitExtension_iff_of_comp_eq_of_central_kernel`: the same morphisms
  `T ×_S A¹_S ⟶ G` extend either orbit.
- `hasLimit_iff_of_comp_eq_of_central_kernel`: the two orbits have exactly
  the same possible limits at zero, in the original `G`.
- `parabolic_eq_of_comp_eq_of_central_kernel`,
  `centralizer_eq_of_comp_eq_of_central_kernel` and
  `unipotent_eq_of_comp_eq_of_central_kernel`: the actual dynamic subgroup
  functors `P_G(χ)`, `Z_G(χ)` and `U_G(χ)` equal their counterparts for `ψ`.

These statements hold on every test scheme over `S`, including nonreduced
and nonaffine tests. No affine, finite-type, smooth, connected, reductive,
flatness or surjectivity hypothesis is used in these results. In particular
`q` need not be an isogeny and its kernel need not be finite or smooth.

Over `Spec R` for an arbitrary commutative ring `R`, suppose additionally
that the underlying scheme of `G` is affine. The theorem
`Dynamic.parabolic_eq_of_positive_powers_comp_eq_of_central_kernel`
proves `P_G(χ) = P_G(ψ)` whenever there are positive integers `m,n` such that

```text
(groupHom (Gm.powerHom (Spec R) m) ≫ χ) ≫ q =
  (groupHom (Gm.powerHom (Spec R) n) ≫ ψ) ≫ q.
```

Here the integers are represented by `ℤ` and each displayed power is an
actual endomorphism of `Gm`. No assertion that the original orbits or their
individual limits agree is made under this weaker hypothesis.

Under the same affine assumptions and the original equality
`χ ≫ q = ψ ≫ q`,
`Dynamic.Affine.parabolicCentralKernelIso` constructs an isomorphism
between the published affine group-scheme representatives of `P_G(χ)`
and `P_G(ψ)`. Its supporting theorem
`parabolicCentralKernelIso_hom_comp` states that the forward isomorphism,
followed by the inclusion of the second representative into the original
`G`, is exactly the first inclusion.

## Implemented proof

The supporting pointwise theorem
`conjugate_eq_of_comp_eq_of_central_kernel` starts with two points `a,b`
over an arbitrary test scheme with the same image under `q`.
The point `a⁻¹*b` is killed by `q`. The published
`isCentral_kernelι_iff` identifies it as a point of the all-test centre.
Consequently it commutes with every point `x`, and cancellation in the
group of points proves

```text
a * x * a⁻¹ = b * x * b⁻¹.
```

Apply this result on the test `T ×_S Gm` to the two values of the supplied
cocharacters and to the pullback of `g`. Equality of the composites
`χ ≫ q` and `ψ ≫ q` supplies precisely the required equality of images
on that test. This proves equality of the actual orbit morphisms.
The extension and limit comparisons follow by rewriting their definitions;
the three subgroup-functor equalities follow by extensionality on every test.

The positive-power corollary combines this lift independence, applied
to the two powered cocharacters, with the published
`Dynamic.parabolic_precomp_power` on each side.
The affine representative isomorphism uses the proved equality of subgroup
functors and the published
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` construction.
Its compatibility with inclusions is the corresponding published property.

## Provenance and retained obligations

All results are derived from the imported kernel and centre interfaces,
the actual dynamic orbit definitions, group identities, positive scaling
and representability. No separate original literature assertion or unproved
classification statement is used.

This unit establishes independence among supplied actual lifts in the
original group. It does not construct a lift, a reductive central quotient,
or a cocharacter for a supplied parabolic. It also does not prove that the
dynamic subgroup in `G` is the full inverse image of the corresponding
subgroup in `H`. That quotient comparison and the geometric classification
remain separate obligations for `SplitParabolicCocharacterStatement`.
