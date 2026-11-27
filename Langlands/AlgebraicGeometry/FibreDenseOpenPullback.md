# Pullback and intersection of fibre-dense opens

`FibreGenerizationDense.preimage_of_isPullback` preserves same-fibre generization
density under arbitrary base change. At a point of the pullback, the morphism from
its fibre to the corresponding original fibre is the base change of an extension
of residue fields. This morphism is flat, so `Flat.generalizingMap` lifts a
generization into the given subset. The fibre embeddings yield the required
specialization and structural-image equality in the total schemes.

`FibreGenerizationDense.inter` takes two successive generizations over the same
base point. Openness of the first subset keeps the second generization in that
subset. `dense` follows because each point lies in the closure of its chosen
generization. `preimage_of_generalizing` is the corresponding lifting argument
along a generalizing morphism with the same base.

These lemmas implement the base-change and intersection properties of fibre-dense
opens in Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §2.5, printed p. 55
(PDF p. 62). The literature ID is `bosch-lutkebohmert-raynaud-1990-neron-models`,
and the retained file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
