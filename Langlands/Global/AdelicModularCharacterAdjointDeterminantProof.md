# The adelic modular character is the normalized idele norm of `det Ad`

`Langlands.Global.AdelicGroupPoints.adelicModularCharacterAdjointDeterminant`
proves `AdelicModularCharacterAdjointDeterminantStatement.{u}` for arbitrary
`u`. For a smooth connected affine group scheme locally of finite type
over a number field, it identifies Mathlib's modular character of each
actual adelic point with the normalized idele norm of its value under the
algebraic adjoint-determinant character. The modular character gives the
pushforward scaling of left Haar measure by right translation.
[Published statement](AdelicModularCharacterAdjointDeterminantStatement.md)

The proof applies `adelicModularCharacterAdjointDeterminantStatement_of_local`
to `PlaceGroupPoints.localModularCharacterAdjointDeterminant.{u}`. The local
theorem gives the modular character on the actual completion-valued
point group at each place, with the squared absolute value at complex places.
[Local proof](LocalModularCharacterAdjointDeterminantProof.md)

The assembly theorem restricts the adelic modular character to each
closed normal single-place image. On that image the normalized adelic
character norm also reduces to the local norm, since all other
coordinates are the identity. The two continuous homomorphisms therefore
agree on all single-place insertions. Finite truncations converge in the
actual adelic topology, which extends the equality to every adelic point.
[Local-to-adelic comparison](AdelicLocalModularComparison.md)

The formula is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §3.6, equations (3.12)–(3.13), printed
pp. 89–90. Their local formula is Proposition 3.6.1, printed p. 88.
The Lean proof combines the Library's local formula and its
continuity argument on adelic points.
[Getz–Hahn, Chapter 3](https://doi.org/10.1007/978-3-031-41153-3_3)
