# Ground-field radicals under quotients with unipotent kernel

This internal development uses the published actual kernel, ground-field radical,
scheme-image and unipotent-extension interfaces. It introduces
`HasSmoothConnectedUnipotentKernel q`, which means that the actual kernel of
`q` is smooth, connected and unipotent over the original field. The predicate
asserts no quotient existence and chooses no radical.

`of_representative` transports these three properties from any supplied closed
representative of the exact kernel range under the existing fppf quotient
predicate. In particular it applies to a represented split ground-field radical
without using its maximality or splitness.

For an fppf homomorphism between affine groups over any field, `smooth` uses
the published smooth-kernel descent theorem to prove that the original
projection is smooth. `geometricallyConnected` applies geometric connectedness
of a smooth connected affine group to the actual kernel.

The radical comparison additionally assumes that the target is locally of
finite type over the field. Both radicals are supplied representatives using the
unchanged `IsUnipotentRadical` predicate. `radical_le_comap` factors the map
from the source radical to the target through its actual scheme image.
That image is smooth and connected, its unipotence descends along the image's
flat surjective projection, and its normality descends through the commuting
fpqc square. Greatestness of the target radical gives one containment. This
containment does not require the kernel predicate.

For the opposite containment, `comap_radical_le` takes the actual group-scheme
preimage of the target radical. The original fppf projection is smooth with
geometrically connected kernel, so this preimage is smooth and connected.
Its projection has the same unipotent kernel and a unipotent quotient; published
unipotent extension closure proves that the preimage is unipotent. It is closed
and normal in the source, so greatestness of the source radical applies.

`radical_comap_eq` combines the containments as an equality of subgroup functors
on every relative scheme, including nonaffine and nonreduced tests.
`radical_isFppfImage` applies the published cartesian restriction theorem to
that equality. Thus the image assertion includes an actual fppf homomorphism
between radical representatives and does not assert surjectivity on the points
of the original test scheme.

These are derived lemmas from the imported published results. No external
structural theorem is assumed or added as an axiom.
