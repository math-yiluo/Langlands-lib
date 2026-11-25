# Dominant Weyl displacement in the real character space

`Langlands.GroupScheme.DominantWeylDisplacementStatement` states the bound
in the full real character space in Renard (VII.4.1.3). For a connected
reductive group over a field `k`, a maximal split torus `i : T → G`, and a
generic cocharacter `ν`, let `D` be the integral reflection data on the actual
relative roots. If `x : Vstar T` pairs nonnegatively with every simple
coroot of `D`, then `x - w⁻¹ x` belongs to the conic hull of the real simple
roots for every class `w : relativeWeylGroup i`. Here `Vstar T` is
`ℝ ⊗[ℤ] X*(T)` and each simple root is mapped to `1 ⊗ α`. The Weyl action
is the actual action on this entire space, including its central directions.

The source uses the closed coroot chamber and the nonnegative root cone of
V.3.15. Its coordinate inequality on printed p. 242 allows zero coefficients,
including when `w = 1`. The proof uses the closed chamber when lifting a
parameter from the split component of a standard Levi. The bound is algebraic
and holds over arbitrary fields.

The formulation is derived from David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, V.3.15, printed p. 113
(PDF p. 119), and (VII.4.1.3) and the surrounding proof, printed pp. 241–242
(PDF pp. 247–248). Source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
