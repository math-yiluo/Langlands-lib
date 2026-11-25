# Relative Frobenius on a special frame: exact global inverse target

`Langlands.FormalGroup.LocalDivision.SpecialModule.RelativeFrobeniusQuasiIsogenyStatement`
is a proposition asserting actual global rational invertibility of
the already constructed relative Frobenius map on a supplied height-certified
special formal frame.

The retained hypotheses are a nonarchimedean local field `K`, a
finite-dimensional central division `K`-algebra `D`, a supplied embedded field,
a supplied coefficient field `κ` with its actual `𝒪[K]`-algebra structure, an
actual distinguished integer `π`, and an actual special frame `Φ` with the
existing kernel-rank height-`d²` certificate. For exponential characteristic
`p` of `κ` and a natural iterate `n`, the proposition quantifies over every
actual `𝒪[K]`-algebra endomorphism `θ` proved to be the actual `p^n`-Frobenius.
It asks for an actual full-order `QuasiIsogeny` from `Φ.order` to its actual
coefficient twist, whose forward rational map is exactly the rationalization
of the constructed integral Frobenius formal map.

This is an existence target for BOTH actual inverse tensor maps and their
original two inverse equations in the whole rational Hom. A local inverse of
a sheaf section alone does not meet it. No global rational equality can be
inferred only from chartwise or pointwise equations, and no inverse map or
kernel representation is added as an input.

The implemented `frobeniusQuasiIsogeny_unique` uses uniqueness of an actual
quasi-isogeny inverse to show that the prescribed forward tensor determines
the whole quasi-isogeny. `frobeniusQuasiIsogenyOfStatement` is conditional on a
proof of the full stated existence result; it chooses the resulting actual
map and exposes its exact forward tensor. Neither this conditional definition
nor uniqueness proves existence.

The provenance is internal: this is the specific fixed-frame global inverse
statement needed toward the natural Frobenius quasi-isogeny used in Drinfeld
1976, §2 A, printed p.109. The source's final normalization uses the residue
cardinality, inverse residue-Frobenius twisting and integer iterates; those
comparisons and the kernel-rank height formula are not part of this
statement. The present statement neither asserts a Hasse-invariant
classification nor constructs a frame or a representing object. The
statement is proved in `SpecialFrameFrobenius`, as
`Langlands.FormalGroup.LocalDivision.SpecialModule.relativeFrobeniusQuasiIsogeny`.
General rational Hom sheaf-section inverse results are not assumed here.
