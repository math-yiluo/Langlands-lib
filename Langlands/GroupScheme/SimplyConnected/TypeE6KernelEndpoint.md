# The first E6 kernel weight in another A5 numbering

In the branch-marked E6 diagram with zero-based vertex 1 distinguished, the
induced A5 numbering of the actual kernel starts at ambient vertex 0.
`KernelComparison.e6BranchFirstWeight` is its first integral fundamental
weight for a simply connected kernel.
`KernelComparison.e6BranchFirstVertex_eq_endpoint` identifies this kernel
vertex with vertex 0 or vertex 4 in any exact A5 numbering of that kernel.

In A5 exactly the two endpoint rows have one entry equal to −1.
The proof checks this property on the five rows and transfers the property of
the initial row between the two numberings using their actual Cartan entry
equalities. `KernelComparison.e6BranchFirstWeight_eq_endpoint` then
identifies the corresponding fundamental character. The equality
`KernelComparison.e6BranchFirstWeight_eq_firstWeight` compares the simple
coroot pairings and identifies this character with the first integral
weight in the E6 kernel restriction formula.

This internal comparison uses the induced Cartan numbering of the actual
kernel and the integral fundamental-weight basis. It is independent of the
ground field characteristic.
