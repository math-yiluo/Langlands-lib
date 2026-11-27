# Compatible Bruhat indices for standard parabolics

`isDoubleCosetRepresentatives_of_minimal` uses one rational normalizing point per relative Weyl element. Restricting that family to the appropriate minimum-length representatives gives the actual adelic images representing `Q(F) \ G(F) / P(F)`. The proof uses the rational Bruhat equivalence and the uniqueness of the Coxeter double-coset minimum.

For a fixed left-minimal Weyl element, the permissible right indices range over subsets of its positive simple roots. The smaller source Levi index is the intersection of the right index with the simple roots conjugated from the fixed left index. The smaller target Levi index is the simple image of that intersection inside the fixed left index. The last two lemmas express exactly this dependence. These are the indexing facts of Bernstein–Lapid (2024), Lemma 6.7, specialized to the range of standard parabolics in Arthur's constant-term sum.
