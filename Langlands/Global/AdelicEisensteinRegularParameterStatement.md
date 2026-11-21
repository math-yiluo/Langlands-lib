# Nonemptiness of the Eisenstein regular-parameter region

`Langlands.Global.EisensteinRegularParameterStatement` is a proposition definition.
For a connected reductive group `G` over a field `F`, take an actual parabolic
presentation `r` with parabolic `P`, Levi `M`, split component `A`, and the
presentation's maximal split torus `T`. Assume the split-torus witnesses for `A`
and `T`, the two monomorphism instances and the finite relative Weyl group instance
used by `r.IsRegularParameter`. Then, for every real threshold `R`, there exists
`λ ∈ X*(P) ⊗ ℂ` for which `B(Re λ|_A, α) > R` for every root `α` in
`r.unipotentRoots`. The bilinear form `B` and the root set are the same ones as in
`AdelicEisensteinConvergenceStatement`. If the root set is empty, the inequalities
are vacuous.

This is a derived structural input to the analytic comparison arguments, not a
convergence theorem. Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series* (2024), §2.1, p.190 (PDF p.4), writes the real character
space of the parabolic `P` through its Levi `M` and the centre `Z_M` of `M`.
The Library's condition restricts instead to the split component `A`, the
maximal split torus of `Z_M`. This is one step beyond the printed identification:
by Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
I.1.4(2), p.6, the restrictions to that torus of a basis of the rational
characters of `M` are linearly independent and generate a subgroup of finite
index. Hence restriction identifies the real character spaces. §2.2, p.191
(PDF p.5), of Bernstein–Lapid uses the region of sufficiently regular real parts
in the positive chamber for the series (2.1). The proposition makes the
nonemptiness of the Library's particular threshold region explicit. It is
algebraic and linear-algebraic, so it does not require `F` to be a number field.
Openness in any complex linear chart is the separate published lemma
`Langlands.Global.isOpen_setOf_isRegularParameter`, in module
`Langlands.Global.AdelicEisensteinContinuationReduction`. No convergence,
meromorphic continuation or imaginary-axis holomorphy is asserted.
