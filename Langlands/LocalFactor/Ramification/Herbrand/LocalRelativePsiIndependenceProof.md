# Independence of the relative inverse Herbrand function

`Langlands.Ramification.Local.relativeHerbrandPsiIndependence` proves
`RelativeHerbrandPsiIndependence` from
`Langlands.LocalFactor.Ramification.Herbrand.LocalSubextensionStatement`, in
all universes `u₀`, `uK`, `uΩ` and with no hypothesis on the characteristic.
For a finite intermediate field \(E\) of a separable closure \(\Omega/K\) and
every finite Galois intermediate field \(M\) of \(\Omega/K\) containing \(E\),
it gives
\[
  \psi_{E/K}(u)=\varphi_{M/E}\bigl(\psi_{M/K}(u)\bigr)\qquad(u\in\mathbb R),
\]
where the left side is `relativeHerbrandPsi`, computed in the normal closure
of \(E/K\) in \(\Omega\), and the right side is `relativeIndex` for \(M\).

The module imports the tower laws `herbrandPhiTower` and `herbrandPsiTower`
from `Langlands.LocalFactor.Ramification.Herbrand.LocalTowerProof`. Both hold
at every real index and for arbitrary realizations of the two fields over
\(K_0\).

## Enlarging the finite Galois field

`Langlands.Ramification.Local.relativeIndex_eq_of_le` takes finite Galois
intermediate fields \(M_0\le M\) of \(\Omega/K\), both containing \(E\), and
proves `relativeIndex K₀ K hbase M h u = relativeIndex K₀ K hbase M₀ h₀ u` for
every real \(u\). It needs neither that \(\Omega\) is a separable closure nor
that \(E\) is finite over \(K\).

The proof views \(M_0\) and \(M\) over \(E\) through `extendFiniteGalois`, as
in the definition of `relativeIndex`, and makes \(M\) an algebra over \(M_0\)
by the inclusion of intermediate fields. All the scalar towers it needs
(\(K\to M_0\to M\), \(E\to M_0\to M\), \(K_0\to M_0\to M\),
\(K_0\to K\to M_0\) and \(K_0\to K\to M\)) hold because every algebra map is
the restriction of an algebra map into \(\Omega\). Both fields are finite over
\(K\), hence over \(K_0\). The fields \(M_0\) and \(M\) are Galois over \(K\),
and \(M\) is Galois over \(M_0\) by `IsGalois.tower_top_of_isGalois`.

Let \(T\) and \(S\) be the canonical realizations of \(M\) and \(M_0\) over the
norm of \(K_0\) (`LocalField.canonicalTopologicalData`). After unfolding
`relativeIndex`, the goal is
\[
  \varphi^{T}_{M/E}\bigl(\psi^{T}_{M/K}(u)\bigr)
  =\varphi^{S}_{M_0/E}\bigl(\psi^{S}_{M_0/K}(u)\bigr).
\]
Three rewrites prove it:

1. `herbrandPsiTower K M M₀ T S` gives
   \(\psi_{M/K}(u)=\psi_{M/M_0}(\psi_{M_0/K}(u))\);
2. `herbrandPhiTower E M M₀ T S` gives
   \(\varphi_{M/E}(w)=\varphi_{M_0/E}(\varphi_{M/M_0}(w))\);
3. `herbrandPhi_herbrandPsi` (from `Herbrand.GeneralFinite`) cancels
   \(\varphi_{M/M_0}\circ\psi_{M/M_0}\).

## The theorem

`relativeHerbrandPsi K₀ K Ω hbase E` is by definition
`relativeIndex K₀ K hbase (galoisClosure E) (algebraMap_mem_galoisClosure E)`.
The hypothesis `h` says that \(E\le M\) as intermediate fields of \(\Omega/K\).
Since \(M/K\) is normal, `IntermediateField.normalClosure_le_iff_of_normal`
gives that the normal closure of \(E\) is contained in \(M\);
`FiniteGaloisIntermediateField.le_iff` turns this into
`galoisClosure E ≤ M`. The lemma `relativeIndex_eq_of_le` for this inclusion
proves the statement.

## Source

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979), Chapter IV, §3, Proposition 15 (printed p. 74, PDF p. 81;
proof on p. 75) and Remark 2 (printed p. 75, PDF p. 82). The registered source
is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Remark 2 defines \(\varphi_{E/K}=\varphi_{L/K}\circ\psi_{L/E}\) for a
subextension \(E\) of a finite Galois \(L/K\) and deduces from Proposition 15
that this does not depend on \(L\). The theorem here is the same independence
for the inverse function \(\psi_{E/K}=\varphi_{L/E}\circ\psi_{L/K}\), proved by
comparing any \(L\) with the normal closure of \(E/K\), which it contains.
