# Proof of adic cofinality of separated descending local ideals

`Langlands.Algebra.completeLocalIdealCofinality.{u}` proves the Library
proposition `Langlands.Algebra.CompleteLocalIdealCofinalityStatement.{u}`,
imported from `Langlands.Algebra.CompleteLocalIdealCofinalityStatement`. Its
type is exactly that closed proposition, for every universe `u`. The statement
pair and its imports are unchanged. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Statement proved

Let \(R\) be a commutative Noetherian local ring with maximal ideal \(m\)
(`IsLocalRing.maximalIdeal R`), complete for the \(m\)-adic topology
(`IsAdicComplete (maximalIdeal R) R`). Let \(J : \mathbb N \to\) `Ideal R` be
antitone with \(\bigcap_n J_n = 0\). Then for every \(a\in\mathbb N\) there is
\(n\) with \(J_n\subseteq m^a\). No hypothesis is added: the residue field is
arbitrary and no coefficient field, generators or index bound are used.

This is a form of a classical lemma usually attributed to Chevalley. The Lean
proof does not rely on a literature source; it follows the route suggested in
the task context, described below.

## Helper lemmas

All three are in the namespace `Langlands.Algebra.CompleteLocalIdealCofinality`
and are stated for an arbitrary commutative Noetherian local ring `R`
(no completeness).

1. `isArtinianRing_quotient_maximalIdeal_pow (hk : 0 < k) :
   IsArtinianRing (R ⧸ maximalIdeal R ^ k)`. The maximal ideal is a minimal
   prime over \(m^k\): it contains \(m^k\) (`Ideal.pow_le_self`), and any prime
   \(q\) with \(m^k\subseteq q\) contains \(m\) (`Ideal.IsPrime.le_of_pow_le`).
   Mathlib's `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`
   then gives that \(R/m^k\) is Artinian.

2. `exists_sup_pow_stable (J) (hJ : Antitone J) (k) :
   ∃ N, ∀ n, N ≤ n → J n ⊔ maximalIdeal R ^ k = J N ⊔ maximalIdeal R ^ k`.
   For \(k=0\), both sides are \(\top\) (take \(N=0\)). For \(k>0\), the images
   of \(J_n\) in the Artinian ring \(R/m^k\) (`Ideal.map` along
   `Ideal.Quotient.mk`) form a descending chain, which stabilizes by
   `IsArtinian.monotone_stabilizes` (applied in the order dual). Pulling the
   equality of images back along the quotient map gives
   \(J_n + m^k = J_N + m^k\), because the preimage of the image of an ideal
   \(I\) is \(I + m^k\) (`Ideal.comap_map_of_surjective'`, `Ideal.mk_ker`).

3. `mem_of_forall_mem_sup_pow (I : Ideal R) (h : ∀ k, y ∈ I ⊔ maximalIdeal R ^ k) :
   y ∈ I`. Every ideal is closed in the \(m\)-adic topology. The image
   \(\bar y\) of \(y\) in the finite \(R\)-module \(R/I\) lies in
   \(m^k\cdot(R/I)\) for every \(k\): writing \(y=a+b\) with \(a\in I\),
   \(b\in m^k\), one has \(\bar y=b\cdot\bar 1\) (`Submodule.smul_mem_smul`).
   Mathlib's instance `IsHausdorff (maximalIdeal R) M` for finite modules over
   a Noetherian local ring (Krull's intersection theorem) gives \(\bar y=0\),
   that is \(y\in I\).

## Main proof

Fix \(a\). By helper 2 choose, for every \(k\), an index \(N(k)\) such that
\(J_n+m^k=J_{N(k)}+m^k\) for all \(n\ge N(k)\), and put
\(L_k = J_{N(k)}+m^k\), the stable value.

1. **Compatibility.** For \(k\le k'\), \(L_k = L_{k'}+m^k\). Indeed, with
   \(n=\max(N(k),N(k'))\), both \(L_k\) and \(L_{k'}\) are computed at \(n\),
   and \(m^{k'}\subseteq m^k\) (`Ideal.pow_le_pow_right`).

2. **Lifting.** Taking \(k'=k+1\), every \(x\in L_k\) can be written as
   \(x = x'+e\) with \(x'\in L_{k+1}\) and \(e\in m^k\) (`Submodule.mem_sup`).
   `choose!` turns this into a function `lift k x` with `lift k x ∈ L (k+1)`
   and `x - lift k x ∈ m ^ k` whenever `x ∈ L k`.

3. **The claim \(J_{N(a)}\subseteq m^a\).** Let \(x\in J_{N(a)}\); then
   \(x\in L_a\). Define \(g_0=x\) and \(g_{j+1}=\mathrm{lift}(a+j, g_j)\)
   by `Nat.rec`. By induction \(g_j\in L_{a+j}\) and
   \(g_j-g_{j+1}\in m^{a+j}\); summing (`Nat.le_induction`),
   \(g_i-g_j\in m^{a+i}\) whenever \(i\le j\).

4. **The limit.** Since \(m^{a+i}\subseteq m^i\), the sequence \(g\) is
   \(m\)-adically Cauchy in the sense of `IsPrecomplete` (the submodule
   \(m^i\cdot\top\) of \(R\) is \(m^i\), by `smul_eq_mul` and `Ideal.mul_top`).
   Completeness (`IsPrecomplete.prec'`) gives \(y\in R\) with
   \(g_k - y\in m^k\) for every \(k\).

5. **\(y\) lies in every \(L_k\).** By step 1, \(g_k\in L_{a+k}\subseteq L_k\),
   and \(g_k-y\in m^k\subseteq L_k\), so \(y\in L_k\).

6. **\(y\) lies in every \(J_n\).** For each \(k\), using the stabilization at
   the index \(\max(n,N(k))\ge N(k)\) and antitonicity,
   \(L_k = J_{\max(n,N(k))}+m^k\subseteq J_n+m^k\). Hence \(y\in J_n+m^k\) for
   all \(k\), and helper 3 gives \(y\in J_n\).

7. **Conclusion.** So \(y\in\bigcap_n J_n=0\) (`Submodule.mem_iInf`, the
   hypothesis, `Submodule.mem_bot`), and
   \(x = (g_0-g_a) + (g_a - y)\) with \(g_0-g_a\in m^{a}\) (step 3 with
   \(i=0\)) and \(g_a-y\in m^a\) (step 4). Therefore \(x\in m^a\), proving
   \(J_{N(a)}\subseteq m^a\).

Completeness is used only through `IsPrecomplete.prec'`; the Hausdorff part
of `IsAdicComplete` is not used. Closedness of the ideals comes from helper 3,
which holds without completeness.
