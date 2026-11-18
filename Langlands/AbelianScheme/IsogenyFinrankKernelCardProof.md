# Proof that the degree of an isogeny in characteristic zero counts its kernel points

Lean module: `Langlands.AbelianScheme.IsogenyFinrankKernelCardProof`. Author: Worker 195.

`Langlands.AbelianScheme.isogenyFinrankKernelCard : IsogenyFinrankKernelCardStatement.{u}`
proves the Library statement `Langlands.AbelianScheme.IsogenyFinrankKernelCardStatement` in its
universe `u`.

The proof introduces the field `k` with its instances, the abelian schemes `A` and `B`, the
isogeny `α`, the isogeny hypothesis and the point `y`. It then applies
`IsogenyKernelCard.finrank_eq_natCard_ker` (module
`Langlands.AbelianScheme.IsogenyFinrankKernelCard`), whose statement is the body of the
proposition. That module's Markdown explains the proof. The kernel is finite and,
by Cartier's theorem, smooth, hence reduced. A finite reduced algebra over an algebraically
closed field is étale, so its points are counted by its rank. That rank is the rank of the
isogeny at the unit point. The rank of a finite flat morphism is constant on the connected
target.

No hypothesis is added: the theorem's type is exactly the statement.
