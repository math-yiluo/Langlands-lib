# Reduction of Weil restriction unit coordinates

Let \(A\) be a local ring with residue field \(k\), and let \(B\) be a
finite projective \(A\)-algebra. `WeilGm.residueUnitsEquiv` identifies the
points of the special fibre of \(\operatorname{Res}_{B/A}\mathbf G_m\)
with the units of \(k \otimes_A B\). It composes the point maps of
`WeilGm.algebraBaseChangeIso` and `WeilGm.sectionUnitsEquiv`.
`WeilGm.residueUnitsEquiv_section` computes the reduction of a section
with unit coordinate \(w\) as \(1 \otimes w\). The calculation uses
`WeilGm.algebraBaseChangeIso_hom_points`, naturality of the point
equivalences, and naturality of `Scheme.ΓSpecIso`.

`WeilGm.residueSection_eq_one_iff` checks identity reduction by applying
`IdealTensorRelation.one_tmul_eq_zero_iff` to \(w-1\). In the congruent-unit
model over a local principal ideal domain, `WeilCongruence.sectionUnit`
records the unit in the coefficient algebra of pairs. Its first
coordinate is one because the source group is the kernel of the
augmentation. `WeilCongruence.reduction_eq_one_iff` uses that this kernel
inclusion remains a monomorphism after base change. Reduction to one
is therefore equivalent to the pair differing from one by the extended
maximal ideal.

These coordinate formulas are consequences of the actual Weil restriction
model and the coefficient pair construction in `WeilCongruenceModel`.
They compute the reduction used with the induced-torus models of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition B.3.6, printed pp. 658–659, PDF pp. 689–690.
