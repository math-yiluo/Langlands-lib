# Actual rational coefficient bounds on compact translates

`RationalCompactTranslateCoefficientBoundStatement` is an internal derived
adapter toward the general rational strict Jacquet square-integrability criterion.
It uses the actual rational-point family, canonical point topology and
Haar-normalized Jacquet exponents of that criterion.

The assumptions are exactly those of `RationalLatticeCoefficientDecayStatement`:
a nonarchimedean local field, connected reductive group, actual maximal split
torus and generic cocharacter, local compactness and a nonarchimedean rational
point group, the standard-cocharacter statement, closed actual unipotent radicals,
an admissible smooth complex representation with strict normalized Jacquet
exponents, and a supplied simultaneous standard basis at a subgroup `K0`.
The field, representation carrier and finite ray-index universes are independent.
There is no finite-length, irreducibility or central-character assumption here.

For each finite family of cocharacters, the pairings vanish on its specified
faces and are positive on every outside simple root; each ray has an outside
root. The conclusion chooses actual points in the full centers of the
corresponding Levis whose ambient values are the uniformizer powers of those
cocharacters. These points are chosen before all compact translating sets,
finite middle sets, vectors and smooth functionals.

For any compact sets `S₁`, `S₂`, finite set `F₀`, vector `v` and smooth functional
`φ`, the conclusion supplies positive real radii `r` and a positive constant `C`.
Uniformly over all natural ray exponents and all translating elements, the
coefficient at `k₁ * uniformizerPowers(sum n a • x a) * t * k₂` is bounded by
`C * product (r a ^ n a)`. For every coordinate, `r a ^ 2` times the inverse
actual positive Haar modulus of its unipotent radical at the chosen central
Levi point is strictly below one. Thus the same weights can be used in a
separate quotient-volume estimate.

The derivation is a composition of the actual lattice coefficient bound and the
generic `CompactTranslateLatticeBoundStatement`. Extract the common compact-open
normal basis from the supplied simultaneous basis. For every smooth input pair,
choose a member below the intersection of its two open fixing subgroups. Fixed
vectors restrict to this smaller subgroup, so the actual lattice coefficient
bound applies. Compact translation moves vectors and smooth functionals through
finite sets, and attained coordinate maxima preserve the strict weighted gaps.
This explanation specifies the internal provenance; this statement file does
not prove either adapter.

The finite index type and translating sets may be empty. An empty index type
makes the lattice value the identity and the product equal to one. With no
simple roots, the outside-root premise forces the ray index type to be empty.
This result does not assert geometric basis existence, a chamber cover,
quotient-volume bounds or square-integrability; all remain obligations of the
complete criterion.
