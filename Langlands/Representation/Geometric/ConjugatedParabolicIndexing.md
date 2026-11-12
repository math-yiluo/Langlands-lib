# Distinguishing conjugated parabolic images

These internal lemmas are part of the actual-parabolic counting route for
Renard V.4.8 and VI.5.4. The first transports equality of two conjugated subgroup
images back to a rational conjugacy of the original subgroup functors.

The second proves that if two conjugates of the same actual rational parabolic
have the same image, their conjugating points have equal double cosets for any
left subgroup. Postcomposition by the inverse of the first conjugation shows
that `x⁻¹y` normalizes the parabolic. The published `parabolicSelfNormalizer`
places this point in the parabolic point image, and `DoubleCoset.eq` gives the
conclusion. No Bruhat coordinates or representation-theoretic result is used.
