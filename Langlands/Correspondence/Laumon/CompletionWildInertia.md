# Wild inertia of `k((t))` and the roots of the uniformizer

The module `Langlands.Correspondence.Laumon.CompletionWildInertia` proves clause 4 of
`Langlands.Henniart.Laumon.HenselianCompletionRamificationStatement`
(`Langlands.Correspondence.Laumon.Completion`), assuming that `completionRestriction k` is a
homeomorphism. Notation: \(k\) is a finite field of characteristic \(p\) with \(q\) elements,
\(X=\)`LaurentSeries k`, \(\Omega_X=\)`SeparableClosure X`, \(\Omega=\)`endGenericClosure k`,
\(r=\)`completionRestriction k`, \(v=\)`closureValuation X Ω_X`, \(\mathbb A\) its integers, and
\(t\in\Omega\) the uniformizer `endUniformizer k .zero` of the end trait.

The Library's wild inertia `localWildInertia X Ω_X` is the closure of the union of the absolute
upper groups of positive level; by the Library's `absoluteUpperWildInertia`
(`Herbrand/LocalAbsoluteImageProof.lean`) it consists of the \(\sigma\) whose restriction to
every finite Galois level \(L\) lies in the first lower group \(G_1(L)\). The module shows that
this happens exactly when \(\sigma\) lies in the Library's inertia and fixes every
\(\varpi\in\Omega_X\) with \(\varpi^N=t\), \(p\nmid N\): Laumon's description of the wild part
\(P\) as the kernel of the action of inertia on the roots of order prime to \(p\) of a
uniformizer (Laumon 1987, (2.1.1), p. 151).

## Basic facts (section `Basic`)

- `closureConstantHom`, `closure_charP`: the constants \(k\to\Omega_X\); \(\Omega_X\) has
  characteristic \(p\).
- `natCast_isUnit`: an integer prime to \(p\) is a unit of \(\mathbb A\) (its image in \(k^\times\)
  is a root of unity).
- `closureUniformizer k` is \(t\) in \(\Omega_X\); `closureUniformizer_eq`: it is the image of the
  power series \(t\in X\); `closureUniformizer_ne_zero`, `closureUniformizer_lt_one`
  (\(v(t)<1\), from `LaurentSeries.valuation_X_pow` and the extension property of \(v\)),
  `closureUniformizer_mem` (\(t\) lies in every finite level), `closureUniformizer_map`
  (\(\sigma(t)=t\)).
- `mem_endGenericClosure_of_pow_eq_closureUniformizer`: a root of \(\varpi^N=t\) with
  \(N\ne 0\) in \(\Omega_X\) is separable over the end field (it is a root of the separable
  \(X^N-t\)), hence lies in \(\Omega\).

## Inertia (section `Inertia`)

- `residue_eq_residue_iff_sub_mem`: in a local ring, two residues agree exactly when the
  difference lies in the maximal ideal.
- `sub_lt_one_of_mem_absoluteInertia`, `mem_absoluteInertia_of_sub_lt_one`: \(\sigma\) lies in
  the Library's `absoluteInertia X Ω_X` exactly when \(v(\sigma x-x)<1\) for every \(x\) with
  \(v(x)\le 1\) (`mem_inertia_iff`).
- `exists_constant_mem_level`: every integral \(x\) of a finite Galois level \(L\) is congruent
  modulo the maximal ideal to a constant \(a\) (`constantsResidue_surjective`,
  `Langlands.Correspondence.Laumon.CompletionConstants`) lying in \(L\): an automorphism
  \(\tau\) fixing \(L\) maps \(a\) to a constant with the same residue, so \(\tau(a)=a\) by the
  injectivity of reduction, and \(a\in L\) by `InfiniteGalois.fixedField_fixingSubgroup`.

## Wild inertia (section `Wild`)

Let \(\pi\) be an element of a finite level \(L\) of maximal valuation \(<1\)
(`exists_levelUniformizer`).

- `mem_lowerRamificationGroup_one_iff`: the restriction of \(\sigma\) lies in
  \(G_1(L)\) exactly when \(v(\sigma x-x)\le v(\pi)^2\) for every integral \(x\in L\)
  (`mem_lowerRamificationGroup_iff_closureValuation`); `apply_mem_level`: \(\sigma\) maps \(L\)
  to itself.
- `fixes_root_of_forall_lower_one`: if the restrictions of \(\sigma\) lie in every \(G_1(L)\),
  then \(\sigma(\varpi)=\varpi\) whenever \(\varpi^N=t\), \(p\nmid N\). Take for \(L\) the
  Galois closure of \(X(\varpi)\) (`FiniteGaloisIntermediateField.adjoin`). Write
  \(v(\varpi)=v(\pi)^n\) (`exists_closureValuation_eq_pow`); \(\sigma\) moves \(\pi\) and the
  unit \(\varpi/\pi^n\) by at most \(v(\pi)\) times their valuations, hence also
  \(\varpi\) (`map_sub_mul_le`, `map_sub_pow_le`). Thus \(\zeta=\sigma(\varpi)/\varpi\) is an
  \(N\)-th root of unity with \(v(\zeta-1)<1\), so its reduction is \(1\). Since \(N\) is a
  unit of \(\mathbb A\), reduction is injective on \(N\)-th roots of unity.
  The proof applies `Separable.eq_of_pow_eq_one_of_sub_mem` to conclude \(\zeta=1\).
- `mem_absoluteInertia_of_forall_lower_one`: such a \(\sigma\) lies in inertia
  (\(G_1(L)\subset G_0(L)\), with \(L\) the Galois closure of \(X(x)\)).
- `lower_one_of_fixes_roots`: conversely, if \(\sigma\) lies in inertia and fixes these roots,
  its restriction lies in \(G_1(L)\) for every \(L\).
  First \(v(\sigma\pi-\pi)\le v(\pi)^2\): write \(v(t)=v(\pi)^e\), \(e=p^a m\) with \(p\nmid m\),
  and let \(\varpi^m=t\) (`IsSepClosed.exists_pow_nat_eq`), fixed by \(\sigma\). Then
  \(y=\pi^{p^a}/\varpi\) is a unit, \(v(\sigma y-y)<1\), and in characteristic \(p\)
  \((\sigma\pi-\pi)^{p^a}=\sigma(\pi^{p^a})-\pi^{p^a}=\varpi(\sigma y-y)\) (`sub_pow_char_pow`), so
  \(v(\sigma\pi-\pi)<v(\pi)\), hence \(\le v(\pi)^2\) (`le_pow_succ_of_lt_pow`). Then an integral
  \(x\in L\) is \(a+\pi x_1\) with \(a\in L\) a constant (`exists_constant_mem_level`), fixed by
  \(\sigma\) (`mem_absoluteInertia_iff`), and \(x_1\in L\) integral, and
  \(\sigma x-x=\sigma(\pi)(\sigma x_1-x_1)+(\sigma\pi-\pi)x_1\) has valuation at most
  \(v(\pi)^2\). This is Serre's criterion \(s(\pi)/\pi\equiv 1\) for \(s\in G_0\) to lie in
  \(G_1\) (IV §2, Proposition 5, p. 66), with the constants of \(L\) in the role of the maximal
  unramified subextension.
- `mem_localWildInertia_iff`: \(\sigma\in\)`localWildInertia X Ω_X` exactly when \(\sigma\) lies
  in `absoluteInertia X Ω_X` and fixes every \(\varpi\in\Omega_X\) with \(\varpi^N=t\),
  \(p\nmid N\).
- `mem_map_localWildInertia_iff` (**clause 4**): if \(r\) is a homeomorphism, \(\tau\) lies in the
  image of `localWildInertia X Ω_X` exactly when \(\tau\) fixes `endUnramifiedField k` and every
  \(\varpi\in\Omega\) with \(\varpi^N=t\), \(p\nmid N\). It combines the previous theorem with
  `mem_absoluteInertia_iff` and `mem_fixingSubgroup_endUnramifiedField_iff`; the roots in
  \(\Omega_X\) lie in \(\Omega\).

Every declaration of the module depends only on `propext`, `Classical.choice` and
`Quot.sound`.
