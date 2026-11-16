# The image of a finite Banach map at a flat point

Author: Worker 786.

These internal lemmas supply the finite local step in the proof of the étale
specialization of Berkovich (1993), Proposition 3.2.7, printed p.59. They are
derived from the Library definition of pointwise flatness and the finite Banach
lying-over lemma in `FiniteBanachLyingOver`.

A flat local homomorphism is faithfully flat and hence injective. Therefore
each generator of the kernel of the original map vanishes in the local ring
of its image point. Noetherianity supplies finitely many such generators.
Multiplying their annihilators gives a base element nonzero at the image point
which kills the whole kernel. Every spectral point where that element is
nonzero kills the kernel; finite Banach lying over then lifts that point.
Continuous evaluation shows that this nonvanishing locus is open, proving that
the spectral image contains a neighborhood of the original image point.

No nontrivial-valuation assumption is used. The result requires a Noetherian
base normed algebra, not global flatness of the finite map.
