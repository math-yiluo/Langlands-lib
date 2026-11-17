# Topology of chart systems over an affinoid atlas

`AffinoidChartSystem.AtlasProjection.topology` proves the exact proposition
`AffinoidChartSystem.AtlasProjection.TopologyStatement`, with independent
universes for both fields, the original space and both chart index types.
The proof uses the actual quotient topology on `C.Space`. It requires only
the local Hausdorffness already present in the original indexed atlas.

First, finite neighborhood witnesses of quasinets and their relative overlap
refinements pull back along any continuous map. Empty inverse images are
retained. The chart-range identity therefore gives the quotient chart net.

For the separation arguments, compact subsets of two original chart ranges
that lie in a common Hausdorff subspace have compact intersection in the
ambient space. The original net covers this intersection by finitely many
common original chart domains. Passing to corresponding new charts gives a
finite compact description of the gluing relation after compact cutoffs in
both chart coordinates. This description proves closedness of the cut-off
relation.

It follows that a compact subset of a new chart whose base projection lies
in an open Hausdorff subspace `U` has closed image in the inverse image of
`U`. To check this in any other quotient chart, choose a compact original
spectrum neighborhood whose image lies in `U` and apply the cut-off lemma.
The quotient topology then detects the desired open complement.

For a chart embedding, take a closed subset `F` of its spectrum and a point
outside `F`. Choose an open Hausdorff base neighborhood `U` and a compact
neighborhood `D` of the original spectrum coordinate inside `U`. The image
of `F` restricted above `D` is closed over `U`. Because the original chart
is an embedding, `D` contains the pullback of an ambient base neighborhood.
This supplies a relative neighborhood in the new chart range disjoint from
the image of `F`. The chart factorization into its range is thus a continuous
injective closed map, proving the embedding.

Finally, take a finite original quasinet witness at the image of a quotient
point. In each of its charts choose a compact original coordinate
neighborhood lying in a fixed open Hausdorff base neighborhood. Original
chart embeddings give ambient neighborhoods whose chart pullbacks lie in
these compact sets. Intersect these neighborhoods with the original finite
chart union. Above the resulting base neighborhood, finitely many compact
pieces of new charts form a closed Hausdorff cover. The finite closed-cover
separation lemma proves this neighborhood is Hausdorff.

The underlying construction is motivated by Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §1.4, printed page 30 (PDF page 27),
and the atlas and net conventions of §1.2, printed pages 16–18. The precise
generic statement and the compact-cutoff proof are internal derived content.
No domain-preservation or completed-tensor theorem is used in this proof.
