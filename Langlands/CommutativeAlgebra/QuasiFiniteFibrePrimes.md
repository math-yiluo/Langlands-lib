# Primes witnessing the failure of quasi-finiteness

Let `f : A →ₐ[K] B` be a map of commutative algebras over a field `K`, with
`B` of finite type over `K`. If `f.toRingHom` fails to be quasi-finite, then
`B` has a nonmaximal prime ideal `q` whose contraction `q.comap f` is maximal
in `A`. Such a prime yields a positive-dimensional piece of a closed fibre.
The module supplies internal lemmas for
`AffineAnalytificationFibreIsolationConverse`, derived from Mathlib's theory
of quasi-finite algebras.

Throughout, `R` and `S` are commutative rings, `S` is an `R`-algebra, and
`Algebra.QuasiFinite` and `Algebra.QuasiFiniteAt` are Mathlib's notions.

- `quasiFinite_of_forall_quasiFiniteAt`: a finite-type algebra that is
  quasi-finite at every prime is quasi-finite. By Mathlib's
  `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`, every fibre of
  `Spec S → Spec R` is discrete. Each fibre is compact, being homeomorphic
  to the spectrum of the fibre ring
  (`PrimeSpectrum.preimageHomeomorphFiber`). It is therefore finite, and
  `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` concludes.
- `exists_isMaximal_not_quasiFiniteAt`: a finite-type algebra that is not
  quasi-finite fails to be quasi-finite at some maximal ideal. Quasi-finiteness
  at a maximal ideal passes to every smaller prime
  (`Algebra.QuasiFiniteAt.of_le`), so the previous lemma applies.
- `quasiFiniteAt_of_forall_le`: let `M` be a maximal ideal of a finite-type
  algebra. Suppose every prime `q ≤ M` with the same contraction to `R` equals
  `M`. Then the algebra is quasi-finite at `M`. The fibre ring is Noetherian
  and Jacobson, being of finite type over a field. In such a spectrum a point
  is open as soon as it is closed and has no proper generization
  (`PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`).
  Both conditions are checked through the fibre homeomorphism.
- `isMaximal_comap_of_finiteType`: let `f : A →ₐ[K] B` be a map of algebras
  over a field `K`, with `B` of finite type. Then the contraction of a maximal
  ideal of `B` is maximal. The residue field `B ⧸ M` is finite over `K`
  (Zariski's lemma, `finite_of_finite_type_of_isJacobsonRing`). The image of
  `A` in it is a `K`-subalgebra of a finite field extension, hence a field.
- `exists_lt_isMaximal_comap_eq`: a finite-type algebra that is not
  quasi-finite has primes `q < M`, with `M` maximal, having the same
  contraction. Combine the second and third lemmas.
- `exists_isPrime_not_isMaximal_of_not_quasiFinite`: let `f : A →ₐ[K] B` be a
  map of algebras over a field, with `B` of finite type, and suppose
  `f.toRingHom` is not quasi-finite. Then `B` has a prime `q` that is not
  maximal while `q.comap f` is maximal. View `B` as an `A`-algebra through
  `f`; it is of finite type, and the previous lemma provides `q < M`. The prime
  `q` is not maximal because it lies strictly below `M`. Its contraction equals
  that of `M`, which is maximal by the fourth lemma.
