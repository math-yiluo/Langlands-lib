# The actual intrinsic kernel character

Fix an actual homomorphism `f : A ⟶ B` of abelian schemes over `S`, a
scheme `T` over `S`, a module `M` on `T ×_S B`, and an actual isomorphism
`α : f_T^* M ≅ O_(T ×_S A)`. In particular `M` can be the underlying module
of an actual line bundle. Keep `h : UniversalGlobalFunctions A` explicit;
it is the proposition about the actual projection map on global functions
after every base change, and `universalGlobalFunctions A` proves it.

`kernelCommGroupScheme f` is the actual scheme-theoretic kernel of `f`,
with the commutativity inherited from the abelian schemes. The construction
`intrinsicKernelCharacterHom f α h` is an actual homomorphism
`ker(f)_T → Gm_T`. Its corresponding element of the existing presheaf is
`intrinsicKernelCharacter f α h : (Cartier.characters
(kernelCommGroupScheme f)).obj (op T)`.

Here is the construction and its evaluation on every test scheme. A scheme
`U` over `T` is viewed over `S` by composing its structure map with `T → S`.
`kernelCharacterParameter U` is the resulting arrow `a : U → T`. Use the
actual equivalence `baseChangePointsEquiv` to view a point `k` of
`ker(f)_T` on `U` as a point `k₀ : U → ker(f)` over `S`. Then
`intrinsicKernelCharacterHom_points` says

`Gm.pointsEquiv (k ; intrinsicKernelCharacterHom f α h) =
 kernelTranslationUnit f α h a k₀`.

The right hand side is the unique unit whose pullback to `U ×_S A` is the
scalar of the canonical transported kernel action. Its defining composite
is inverse ordinary trivialization, canonical ordinary-to-translated
pullback comparison, and translated trivialization, with the canonical
structure-module comparisons at the ends. Thus evaluation retains the
transported-action divided by trivial-action orientation of
`KernelTranslationScalar`, motivated by EGM VII §§7.1–7.4, printed
pp.98–100 / PDF pp.102–104 of the preliminary build 2012-02-08. The
constructor accepts no character, pairing or linearization as input.

`kernelTranslationUnitsHom` uses the already proved identity and
multiplication laws of `kernelTranslationUnit`. Composing it with the
actual kernel base-change equivalence and inverse of `Gm.pointsEquiv`
gives `intrinsicKernelCharacterPoints`, a homomorphism on groups of points.
Its naturality follows from the scalar unit's parameter precomposition law
and naturality of the two equivalences. `homOfPoints` constructs the actual
group-scheme morphism; `comp_homOfPoints` proves the displayed evaluation
formula. Finally `Cartier.characterHomEquiv` gives the presheaf element.
These are internal derivations from the imported scalar, kernel
base-change, Gm and Cartier interfaces.

This is a complete progressive packaging unit. Independence of the
trivialization, bundle isomorphism and tensor compatibility, and comparison
with replacing the bundle by its test-scheme pullback belong to subsequent
units. No descent equivalence, representability, perfectness or duality is
asserted here.
