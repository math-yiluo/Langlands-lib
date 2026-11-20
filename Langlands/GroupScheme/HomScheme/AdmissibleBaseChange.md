# Base change of the actual torus-subgroup presheaf

`smallAdmissiblePresheafBaseChangeIso` identifies the small presheaf of actual
closed torus subgroups of an ambient pullback with restriction of the original
presheaf along composition of structure maps. For each test the comparison
isomorphism between the iterated and direct pullbacks transports both the
literal subgroup range and its closed torus representative. It commutes with
restrictions by the actual family-evaluation comparison.

`AdmissibleAdicLimitsBaseChangeStatement.{u}` says that adic-limit
bijectivity of the torus-subgroup presheaf survives arbitrary base change.
The proof applies base change of Murre's adic condition and uses the natural
isomorphism to transport injectivity and the compatible lifts.

This implements the presheaf comparison needed for the base change in the
proof of Raynaud, SGA 3, Exposé XV, Theorem 8.9(a), Gille–Polo recomposition,
PDF pp. 62–63.
