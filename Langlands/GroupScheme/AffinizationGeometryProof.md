# Geometry of a supplied group affinization

`Langlands.GroupScheme.affinizationGeometry.{u}` proves the supporting
`AffinizationGeometryStatement.{u}` for every arbitrary field and universe:
a supplied actual affinization homomorphism from a smooth connected group has
smooth connected affine target and a flat, surjective, quasi-compact
projection. The target's finite type is derived through its smoothness and
affineness. No affine-source or extra finite-type premise is used.

Over an algebraically closed field, the smooth connected source is
quasi-compact and locally Noetherian, hence Noetherian. The finite detector
for its full kernel chooses finitely many augmentation functions generating
the exact closed-kernel ideal sheaf. A single actual finite-dimensional
representation of the affine target contains those functions in its
coordinate pullback. The actual smooth connected affine image of the
represented homomorphism gives a flat, surjective, quasi-compact map `q0`
from the original, possibly nonaffine, source.

The finite detector proves that the full kernel of `q0` is killed by the
original affinization map. The fpqc affinization comparison then supplies an
actual isomorphism from that affine image to the supplied affine target,
compatible with both projections. The target's smoothness and the
projection's flatness, surjectivity and quasi-compactness transfer across this
actual isomorphism. Connectedness follows from the continuous surjection
from the connected original source. The private comparison lemma organizes
these data without altering their maps or weakening the kernel condition.

For an arbitrary field, source quasi-compactness and field-group
separatedness give the qcqs hypotheses needed for the published
`IsAffinization.baseChange`. Base change the actual group homomorphism to the
algebraic closure; the source remains smooth and connected. Apply the
algebraically closed case. The actual base-change square for homomorphisms
and fpqc descent give flatness and surjectivity of the original projection;
smoothness of the target descends along the faithfully flat field-spectrum
map. Quasi-compactness follows from the original algebraic source and the
affine target, and connectedness follows again from surjectivity.

The mathematical source is SGA 3, Exposé VI_B, Corollary 11.18.1 (printed
p.427 / PDF p.97) and Theorem 12.2(i) (printed p.430 / PDF p.100),
Gille–Polo recomposed edition of 13 October 2024. Source identifier:
`sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
The implemented proof uses a finite representation retaining the full kernel
rather than an inverse system of finite-type affine groups and a general
nonaffine normal quotient theorem. The exact ideal-sheaf and fpqc comparison
lemmas make this replacement explicit. The complete official Tome I errata
dated 13 October 2024 do not alter the cited results.
