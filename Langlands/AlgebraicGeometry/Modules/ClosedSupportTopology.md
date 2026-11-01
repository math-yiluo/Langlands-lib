# Heights and dimensions of closed subspaces

This internal helper module compares irreducible closed sets under an
embedding. An irreducible closed subset of the target contained in the
embedding's range lifts by inverse image: the restricted homeomorphism
transfers irreducibility, and continuity transfers closedness. Its image
closure is the original closed set.

For a closed embedding, every irreducible closed subset below an image is
contained in the range, because the image of the original closed set is
closed. Thus the strictly monotone map on irreducible closed sets has the
lifting property in `Order.height_eq_of_strictMono`. Heights agree.

For a closed subset `Z` and a natural number `e`, this identifies the
heights of its irreducible closed subsets with their ambient heights.
The bound on topological Krull dimension in one direction bounds every
height. In the other direction, the length of each irreducible-closed
chain is at most the height of its last member, giving dimension less
than `e`. The argument includes `e = 0` and the empty closed set.

These are derived topological comparisons. There is no new geometric
assumption, support definition, or claim of Euler positivity here.
