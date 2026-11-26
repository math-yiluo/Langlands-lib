# Compatible rank-one realizations of algebraic Hecke characters: proof

`algebraicHeckeLambdaAdicRealization` proves
`AlgebraicHeckeLambdaAdicRealizationStatement` with its two independent
universe parameters, for the base field and for the coefficient field. Let `K`
be a totally complex number field and `χ` a Hecke character of `K` whose
archimedean component is the character of an integral infinity type `t`. Then
there are a coefficient number field `L`, an embedding `ι : L → ℂ` and
continuous characters of the absolute Galois group of `K` into `L_λ^×`, one for
every finite place `λ` of `L`. Together they form an
`IsCompatibleLambdaAdicRealization` of `χ`.

The proof goes through `exists_isUniformHeckeAvatar`, which gives the stronger
`IsUniformHeckeAvatar` family for these characters. Its exceptional set is
exactly the set of places where `χ` is ramified. The values at the good places
lie in `Lˣ`.

1. `algebraicHeckeFinitePart` (the proof of `AlgebraicHeckeFinitePartStatement`)
   gives `L` in the coefficient universe, `ι`, lifts `emb σ : K → L` with
   `ι ∘ emb σ = σ`, a lift `φ` of the finite part of `χ` to `Lˣ` with open
   kernel, and the finite set `S` of ramified places of `χ`.
2. `ClassFieldTheory.Global.Artin.exists_uniformizer` chooses a uniformizer
   `π v` of `K_v` at every finite place `v`.
3. `exists_isUniformHeckeAvatar_of_finitePart` (module
   `HeckeAvatarConstruction`) is applied to the Library theorems
   `heckeAvatarIdeleCorrection`, `finiteGeometricArtinLifting` and
   `heckeAvatarInverseLimit`. At each `λ` it corrects `φ` by the infinity-type
   monomial in the coordinates over `λ`. The finite reductions of the
   resulting integral idele-class character are lifted to the Galois group,
   with geometric normalization, outside `S` and the places over the residue
   characteristic of `λ`. The family is the limit of these lifts. For `v ∉ S`
   of residue characteristic different from that of `λ`, the character at `λ`
   is unramified at `v`. It sends every geometric Frobenius lift to the image
   in `L_λ` of `a v = φ(π v)`, where `φ(π v)` means `φ` at the one-place idele
   of `π v`. The complex value `χ_v(π v)` equals `ι (a v)`.
4. `IsUniformHeckeAvatar.isCompatibleLambdaAdicRealization` turns this uniform
   family into the compatible realization of the target, with the same set
   `S` and the same values `a v`.

The construction is Serre's, *Abelian l-Adic Representations and Elliptic
Curves*, 1989 reprint (`serre-abelian-l-adic-1989`), Chapter II §§2.3–2.7. The
Frobenius formula is §2.5, pp. II-18–II-19, and the identification with type
`A₀` characters is §2.7, p. II-24. Serre's arithmetic Frobenius corresponds
here to the geometric normalization of `FiniteGeometricArtinLifting`.
