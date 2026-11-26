# Transport of simple type data and conjugacy of principal orders

`SimpleTypeTransportStatement` is stated over every nonarchimedean local
field \(F\), every finite-dimensional \(F\)-space \(V\) of dimension \(N\ge 1\),
and every `IsBKAdditiveCharacter` \(\psi_F\). The field, vector space and
representation carrier have independent universes.

For \(g\in\mathrm{Aut}_F(V)\), the first clause transports the data
exhibiting a simple type under `conjRepresentation g`. In kind (a), the
transported stratum is \([g\mathfrak A g^{-1},n,0,g\beta g^{-1}]\)
on the conjugated lattice chain. The new character is transported with
its domain and satisfies \(\theta'(ghg^{-1})=\theta(h)\). The equality of
centralizer order periods comes from using the same \(e\) in both
`IsSimpleTypeDataOver` predicates. In kind (b), the transported data use
the conjugated lattice chain and the same period of the principal order.

The second clause says that each principal order period divides \(N\)
and that two principal orders of equal period are conjugate. The Lean
conclusion identifies their orders using `LatticeChain.linearEquivMap`.

The transport and the period classification are unnumbered facts in this
form. BK94 uses the transport of simple type data implicitly on printed
p. 126 and states the period classification on that page. The transport
comes from the conjugation of the constituents in BK93 (5.5.10).
The lattice-chain bases and block forms on BK93 printed pp. 22–23 give the
period classification. The common block size of a principal order is \(N/e\)
when there are \(e\) blocks.

## Sources

- Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*
  (1994), §3, the paragraph before (3.8) and its use in (3.8), printed p. 126
  (volume PDF p. 139).
  Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
  SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
- Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
  (1993), §1.1, lattice-chain bases and block form, printed pp. 22–23
  (PDF pp. 34–35), and (5.5.10), printed pp. 184–185 (PDF pp. 196–197).
  Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
  SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
