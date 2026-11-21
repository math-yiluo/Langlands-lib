# Herbrand's finite subgroup formula in either characteristic

This module proves the published statement
`Langlands.Ramification.Local.FiniteHerbrandSubgroupFormula` from
`Herbrand.LocalSubextensionStatement`:

```lean
theorem finiteHerbrandSubgroupFormula : FiniteHerbrandSubgroupFormula
```

It also contains two helper lemmas used by the proof. Everything is in the
namespace `Langlands.Ramification.Local`. There is no characteristic hypothesis,
and neither \(M/K\) nor \(M/E\) is assumed Galois.

## Statement proved

Let \(K_0\) carry the structure required by `LocalField.TopologicalData`, let
\(K\to E\to M\) be a tower with compatible maps from \(K_0\), let \(M\) be finite
over \(K_0\), and let `T : LocalField.TopologicalData K₀ M` be one realization of
\(M\). For every real \(u\) and every \(\sigma\in\operatorname{Aut}_E(M)\),
`σ.restrictScalars K` lies in `upperRamificationGroup T K u` exactly when
\(\sigma\) lies in `upperRamificationGroup T E (herbrandPhi T E (herbrandPsi T K u))`.
With \(G=\operatorname{Aut}_K(M)\) and \(H=\operatorname{Aut}_E(M)\) embedded in
\(G\) by restriction of scalars, this is
\[
  H\cap G^{u}=H^{\varphi_{M/E}(\psi_{M/K}(u))}\qquad(u\in\mathbb R).
\]

## Helper lemmas

- `restrictScalars_mem_lowerRamificationGroupInt_iff K E T i σ`: for every
  integer \(i\) and \(\sigma\in\operatorname{Aut}_E(M)\),
  `σ.restrictScalars K ∈ lowerRamificationGroupInt T K i ↔
  σ ∈ lowerRamificationGroupInt T E i`. This is \(H_i=H\cap G_i\).
- `restrictScalars_mem_lowerRamificationGroupReal_iff K E T t σ`: the same
  statement for `lowerRamificationGroupReal` at every real \(t\).

## Proof

**Lower groups.** By definition, `lowerRamificationGroupInt T K i` is the whole
group when \(i<0\). Otherwise it is the set of automorphisms \(g\) with
\(g\cdot x-x\in\mathfrak m^{i+1}\) for all \(x\) in `T.Integers`, where
\(\mathfrak m\) is the maximal ideal. Here \(g\cdot x\) is
`integerAutomorphism T K g x`, whose underlying element of \(M\) is \(g(x)\). The
group over \(E\) is defined the same way with `integerAutomorphism T E`. The
proof unfolds `lowerRamificationGroupInt` and `lowerGroupInt` and splits on
\(i<0\). In the negative case both sides are `⊤` and `simp` closes the goal. In
the other case, `σ.restrictScalars K` and \(\sigma\) have the same underlying map
of \(M\). So the two integer automorphisms agree definitionally, the two
membership conditions are the same proposition, and `Iff.rfl` closes the goal.
The real-indexed lemma is the integer lemma at \(\lceil t\rceil\), because
`lowerRamificationGroupReal T K t` is defined as
`lowerRamificationGroupInt T K ⌈t⌉`.

**The formula.** After introducing the binders, the proof rewrites the right side
with `upperRamificationGroup_phi` from `Herbrand.GeneralFinite`:
`upperRamificationGroup T E (herbrandPhi T E t) = lowerRamificationGroupReal T E t`.
This holds because `herbrandPsi T E` inverts `herbrandPhi T E`. Here
\(t=\psi_{M/K}(u)\). The left side `upperRamificationGroup T K u` is by
definition `lowerRamificationGroupReal T K (herbrandPsi T K u)`. The real-indexed
helper lemma at \(t\) therefore closes the goal.

The Herbrand functions of \(M/K\) and \(M/E\) are different. The proof only uses
that \(\varphi_{M/E}\) and \(\psi_{M/E}\) are mutually inverse. So it puts both
memberships at the same lower index \(t\), and then at the same integer index
\(\lceil t\rceil\).

## Source correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979). The registered source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- Chapter IV, §1, Proposition 2, printed p. 62 (PDF p. 69): for a subgroup
  \(H\) of \(G\), \(H_i=G_i\cap H\). The first helper lemma is this statement
  for \(H=\operatorname{Aut}_E(M)\) inside \(\operatorname{Aut}_K(M)\) in the
  Library's integer-ring indexing.
- Chapter IV, §3, Remark 3, printed pp. 75–76 (PDF pp. 82–83): with
  \(G(t)=G_{t_L}=G^{t_{L'}}\), one has \(H(t)=H\cap G(t)\). The proof follows
  this route. It fixes the lower index \(t_M=\psi_{M/K}(u)\), whose two upper
  coordinates are \(u\) for \(M/K\) and \(\varphi_{M/E}(t_M)\) for \(M/E\).

Serre works on \([-1,\infty)\) with Galois groups. The Library extends both
Herbrand functions by the identity at nonpositive arguments, and its lower groups
are constant below \(-1\). Its finite groups are subgroups of the full
automorphism groups. The proof uses only these definitions, so the formula holds
at every real \(u\) without a Galois hypothesis.

The p-adic counterpart is
`Langlands.Ramification.HerbrandBridge.restrictScalars_mem_upperRamificationGroup_iff`
in `Herbrand.SubextensionProof`. It has the same proof.
