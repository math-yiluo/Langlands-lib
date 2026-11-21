# Compact open rank-one norm neighborhoods

Hilbert's theorem 90 expresses every norm-one unit of a cyclic field extension as a quotient of a unit and its image under the cyclic generator. A character invariant under the generator therefore takes the value one on the norm kernel.

For the supplied p-adic local field data, the norm image is closed and has finite index, so it is open. The `exists_compactOpen_normPreimage` theorem shrinks an open neighborhood of one downstairs so that its full norm preimage lies in any open set containing the norm kernel. It first restricts to integral units. The image of the compact complement of the given open set among integral units is then closed and misses one. A principal-unit neighborhood inside its complement has the required compact open preimage.

These lemmas are for rank-one concordance. See Henniart and Lemaire, *Changement de base et induction automorphe pour GL(n) en caractéristique non nulle* (2011), II.2.9, Remarque (3), printed p. 70, and II.2.10, printed p. 71, for the norm pullback and the role of Hilbert 90.
