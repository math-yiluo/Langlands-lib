# Equivariant embeddings of factors into a finite tensor

`Langlands.FiniteTensor.slotEmbedding` inserts a vector into a specified slot
while keeping the tensor of the other slots fixed. The construction uses
the linear equivalence that splits off the specified slot. After this
split, insertion sends `x` to `y ⊗ x` for a fixed complementary tensor `y`.
A nonzero `y` gives an injective map because a tensor of two nonzero vectors
over the field is nonzero.

The split takes the one-slot action of an endomorphism to the action on the
right tensor factor. Evaluating it on `y ⊗ x` proves that insertion intertwines
any endomorphism of the given slot. If every complementary factor is
nontrivial, the complementary tensor is nontrivial, including when the
complement is empty. Choosing a nonzero tensor gives a single embedding
for all operators of the given slot.

This is an internal algebraic step for extracting each of the prescribed
local factors from one global tensor constituent. It applies to the
finite adelic factor and to both the compact and Lie actions at each
archimedean place in the proof of Getz–Hahn (2024), Theorem 10.7.5,
printed p. 288 (PDF p. 300).
