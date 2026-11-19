# A torus as the kernel of a quotient of an induced torus

Over a characteristic-zero field, every torus embeds as a closed subgroup of an induced torus. The latter admits an fppf quotient onto a torus whose scheme kernel has the same subgroup functor as the given closed subgroup on every test scheme.

The Lean proof uses the Library's induced embedding and the closed-immersion criterion for monomorphisms of groups of multiplicative type. It forms the actual quotient in the category of relative groups of multiplicative type. Over a field that diagonalizes the quotient, the surjection from the base-changed induced torus gives connectedness. The characteristic-zero criterion for a finitely generated character group then makes that group free, so the diagonalization is a split torus.

This construction supplies the exact sequence used in Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §7.3, Corollary 2, pp. 418–419. The proof here derives it from the Library's structural results.
