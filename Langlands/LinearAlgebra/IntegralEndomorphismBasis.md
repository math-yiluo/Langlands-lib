# An integral matrix for an endomorphism with integral characteristic coefficients

Let `O` be a principal ideal domain with fraction field `F`, and let `T` act on a finite-dimensional `F`-vector space `V`. `IntegralEndomorphismBasisStatement` asserts that if the characteristic coefficients of `T` belong to `O`, there is an `F`-basis of `V` in which all matrix entries of `T` belong to `O`.

Lift the characteristic polynomial to a monic polynomial over `O`. By Cayley–Hamilton it annihilates `T`, so the algebra `O[T]` is finite over `O`. Applying `O[T]` to a finite `F`-basis and taking the sum gives a finite `O`-module `L` that spans `V` and is stable under `T`. Since `O` is a principal ideal domain, this lattice is free and its basis extends to an `F`-basis of `V`. In that basis the entries of `T` are the images of the integral coordinates of `T` on `L`.

This is a derived lattice calculation for describing small exponential domains by characteristic coefficients. [Clozel, *Characters of non-connected, reductive p-adic groups*, §3.4, p. 155](https://doi.org/10.4153/CJM-1987-008-3)
