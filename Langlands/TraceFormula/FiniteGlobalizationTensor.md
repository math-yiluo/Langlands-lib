# Finite adelic tensor tests with prescribed local factors

Let \(K\) be a number field, \(n \ge 0\), and \(s\) a finite set of finite places of \(K\).
The module works with the actual finite adelic matrix group `FiniteAdelicGL K n` and its
splitting `FiniteAdelicGL.splitAtPlaces` at the places of \(s\). This splitting is a
topological group isomorphism with the product of the local groups
\(GL_n(K_v)\), \(v \in s\), and the restricted product at the remaining places.

## Definitions

- `finiteAway K n s` is the away component outside \(s\) of a finite adelic matrix, as a
  continuous homomorphism. Its value at a place \(w \notin s\) is the local projection.
- `finiteSchwartzTest K n s f` is a Schwartz–Bruhat function on the finite adelic group. It is built
  from local Schwartz–Bruhat functions \(f_v\) on \(GL_n(K_v)\), \(v \in s\):
  \[
    g \mapsto \Bigl(\prod_{v \in s} f_v(g_v)\Bigr)\cdot
      \mathbf 1_{J}(g^{s}),
  \]
  where \(\mathbf 1_J\) is `awayCharacteristic K n s`, the characteristic function of the
  subgroup of away families integral at every place outside \(s\). The function is
  locally constant and compactly supported, because it is the pullback along the splitting
  of a product of such functions.
- `finiteComplement K n s f v` is the same expression with the factor at \(v \in s\)
  omitted.
- `finiteLevel K n s U` is the open subgroup of finite adelic matrices \(g\) with
  \(g_v \in U_v\) for \(v \in s\) and away component integral outside \(s\), for given
  open subgroups \(U_v\) of \(GL_n(K_v)\).

## Statement

`FiniteTensorFactorizationStatement` assumes that each \(U_v\) is compact and that each
\(f_v\) is right invariant under \(U_v\). It concludes three things:

1. `finiteLevel K n s U` is compact;
2. `finiteSchwartzTest K n s f` is right invariant under `finiteLevel K n s U`;
3. at every \(v \in s\), `finiteSchwartzTest K n s f` is `finiteComplement K n s f v` times
   \(f_v(g_v)\). The complement is unchanged when a local matrix at \(v\)
   (`FiniteAdelicGL.localInclusion K n v`) is inserted between two factors.

## Proof

`finiteTensorFactorization` combines the lemmas of the module.

- The level subgroup is the preimage under the splitting of the product of the compact
  local subgroups and the compact away integral subgroup
  (`RankinSelbergGlobal.UnipotentClass.isCompact_awayIntegral`). The preimage of a compact
  set under a homeomorphism is compact.
- Right invariance holds factor by factor. Local projections and the away component are
  homomorphisms, each \(f_v\) is right \(U_v\)-invariant, and the characteristic function of
  the away integral subgroup is right invariant under that subgroup.
- The factorization at \(v\) splits off one factor of the finite product.
- A local matrix at \(v\) has trivial components at every other finite place
  (`FiniteAdelicGL.localProjection_localInclusion_of_ne`), so its away component is
  trivial and the remaining local factors are unchanged.

These are the finite-adelic versions of the properties of `GlobalizationTensor.test` and
`GlobalizationTensor.complement`. The implemented construction is a tensor of compactly
supported, locally constant functions on \(GL_n(\mathbb A_{K,f})\): local tests at the
prescribed finite places and the integral indicator at every other finite place. It has
no archimedean factor and no central transformation law.

The restricted tensor product pattern \(f = \otimes_v f_v\), with factors at finitely many
places and the integral indicator elsewhere, follows Arthur–Clozel, *Simple algebras, base
change, and the advanced theory of the trace formula* (1989), Chapter 1, §4, printed
pp. 43–45. Their global test functions also include archimedean factors, transform by a
central character, and have compact support modulo the central subgroup introduced on
printed p. 42. The finite tensors here are therefore not the source's test functions.
Printed p. 45 of the same section fixes a compact open subgroup of the finite adelic group;
the level subgroup here plays that role. The module is internal infrastructure for
fixed-level smoothing with tests factored at a place.

Source ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
