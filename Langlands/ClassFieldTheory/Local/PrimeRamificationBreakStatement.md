# Prime total ramification: the actual break

Worker 27 authored the initial statement and documentation draft. Worker 70
checked the original source, canonical scalar instances and declaration signatures,
and finalized the paired module. It defines the proposition
`Langlands.LocalClassField.PrimeTotallyRamifiedBreak.{u,v}`; it supplies no
proof of that proposition.

The proposition quantifies all primes `p` and two p-adic fields
`F : PadicField.{u} p` and `L : PadicField.{v} p`, with arbitrary universes.
The extension uses the supplied `Algebra F.Carrier L.Carrier` and the
compatible scalar tower from `Padic p`. It assumes finite dimension and
Galoisness. Write `ell = Module.finrank F.Carrier L.Carrier`, and write
`TF` and `TL` for the canonical topological data. Its arithmetic hypotheses
are that `ell` is prime and

```text
TL.ramificationIndex = ell * TF.ramificationIndex.
```

These are the canonical absolute ramification indices. The equality says
that the relative extension is totally ramified; no inertia or norm
certificate is supplied as a premise.

The conclusion gives a natural number `t`. For every natural index `i`,
the existing `Ramification.Padic.lowerRamificationGroup TL F.Carrier i`
is the full automorphism group when `i ≤ t` and the trivial subgroup
otherwise. These are the actual lower groups defined by the action on the
integer ring and congruence modulo its maximal-ideal powers. The same `t`
is positive exactly when `ell = p`.

Finally, the existing real function
`Ramification.Padic.herbrandPsi TL F.Carrier` has, at every natural input
`n`, value equal to the real cast of

```text
if n ≤ t then n else t + ell * (n - t).
```

The subtraction here is natural subtraction, used only in the branch
where `t < n`. The statement identifies the actual inverse Herbrand
function constructed in `Herbrand.Finite`; it does not define a new
function and call it the inverse. Only natural inputs are asserted,
which are sufficient for the subsequent unit-filtration formulas.

The generic compatible pair of p-adic fields permits application both to
the original extension and to the actual relative extension after an
unramified compositum. No choice of another algebraic closure is part of
this statement. It makes no claim of invariance under base change, norm
containments, trace formulas or higher-unit norm surjectivity.

## Source and derived formulation

Jean-Pierre Serre, *Local Fields*, Marvin Jay Greenberg translation,
GTM 67, Springer, 1979, registered as `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Chapter V, §3, opening, printed p.83 / PDF p.90, gives the single-break
pattern, the criterion that the break is positive precisely in residue
characteristic degree, and the displayed inverse-Herbrand formula. The
source phrases the extension as cyclic of prime degree. The Lean
formulation assumes Galois of prime degree, whose finite Galois group is
cyclic because a finite Galois group has order equal to the extension
degree and every group of prime order is cyclic. Thus this formulation is
equivalent to the source hypothesis in the present domain; cyclicity is not
a separate premise. The identification of residue characteristic with
`p` and the encoding by canonical p-adic data are also part of the derived
formulation. No source-specific errata note was present in the checked
project notes, literature or current Library.

The lower-group convention is Serre IV.1, Lemma 1 and Proposition 1,
printed pp.61–62 / PDF pp.68–69: trivial action modulo the `(i+1)`st
maximal-ideal power. The real Herbrand convention is IV.3, printed
pp.73–74 / PDF pp.80–81: real lower numbering uses the ceiling, and `psi`
is the inverse of `phi`. These agree with the imported constructions.
The two displayed branches on p.83 agree at `x = t`; choosing the first
branch at equality preserves the source formula.

Worker 70 reread these original passages and visually checked the displayed
formulas on PDF p.90, and verified the retained source fingerprint.
The target intentionally does not assert that the existing generic
ramification definitions already prove the prime-degree arithmetic.
An independent proof must establish total inertia, the prime-order
filtration pattern and its tame/wild criterion, then relate that pattern
to the constructed inverse Herbrand function.
