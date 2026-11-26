# Cuspidal rapid decay on the norm-one Siegel cover

`Langlands.Global.AdelicGroupPoints.adelicNormOneCuspidalRapidDecay`
proves `AdelicNormOneCuspidalRapidDecayStatement`. For a connected reductive
group over a number field, there is a subset of the norm-one adeles meeting
every rational left orbit. On this subset a rationally invariant smooth
cuspidal function decays faster than every inverse power of the given adelic
matrix height, provided its real archimedean derivative words have a common
polynomial growth exponent. The constants can depend on the function and the
power, and the same subset works for all the functions in the statement.

The proof takes the finite-right-translate Siegel cover and intersects it
with the norm-one group. It forms the standard parabolic family from the
cover's maximal split torus. The full standard index has trivial radical,
and a proper subindex represents a proper parabolic, so the hypotheses for
relative cuspidal decay at the full index hold. The positive component of the
Siegel cover maps from the derived split torus to the maximal split torus.
Its simple-root inequalities persist under this map, and all restrictions of
ambient rational characters have norm one there. The simple roots and these
restricted characters together span the rational character space. The finite
components lie in the product of the finite images of the compact prefix
and the compact right factor. The relative rapid decay estimate then gives
the bound on the cover.

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.3.4, p. 46, applies rapid decay to the smoothed cuspidal function in the
vanishing argument. This is the adelic height estimate derived from the
Library's relative decay and finite-translate reduction theorems.
