# Proof of fixed-vector detection through actual Jacquet subquotients

Worker 189. The theorem
`Langlands.jacquetSubquotientFixedVectorDetection` proves
`Langlands.JacquetSubquotientFixedVectorDetectionStatement` with independent
group, carrier and finite-family index universes.

The implementation first proves three helper lemmas for actual smooth
subquotient presentations. Write such a presentation as an injective
intertwiner `i : C → A` and a surjective intertwiner `q : C → D`.

* At a fixed compact open `K`, the restriction of `i` to fixed vectors is
  injective. If `A^K` is finite dimensional, so is `C^K`. Compact-open
  fixed-vector exactness makes `C^K → D^K` surjective, proving finite
  dimension of `D^K`.
* A nonzero vector of `D^K` lifts to `C^K` by that same surjectivity. Its
  image under `i` is fixed and nonzero: if zero, injectivity of `i` makes
  the lift zero, contradicting its nonzero image under `q`.
* Under finite compact containment in `N`, the published coinvariant
  injection theorem applies to `i` restricted to `N`; right exactness of
  coinvariants applies to `q`. The induced maps intertwine the actual
  descended `M`-actions and give a subquotient presentation of `JD` in `JA`.

Transitivity now makes the supplied `E` a subquotient of `JA`. The
published factorization proof transfers generation by `A^K` to generation
of `JA` by its `K ∩ M`-fixed vectors. The finite compact-restriction
detection theorem, applied inside `M` with its normal subgroup `H`,
therefore supplies a nonzero `K ∩ M`-fixed vector in `E`.

The subgroup `K ∩ M` is open in `M` by continuity of the inclusion and
compact because `M` is closed in `G` and `K` is compact. The second helper
lifts nonvanishing from the subquotient `E` to `JD`. The first helper makes
`D^K` finite dimensional, so the actual weak Jacquet lemma for the supplied
Iwahori contraction makes `D^K → JD^(K ∩ M)` surjective. A preimage of
the nonzero vector is the required nonzero `K`-fixed vector of `D`.

The source motivation is Renard VI.6.3, printed pages 178–179 / PDF184–185,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This proof composes the published algebraic and topological lemmas on actual
objects. It retains the statement's explicit structural and finite
compact-restriction inputs. It supplies no reductive rational-point
realizations and does not prove the final Howe target.
