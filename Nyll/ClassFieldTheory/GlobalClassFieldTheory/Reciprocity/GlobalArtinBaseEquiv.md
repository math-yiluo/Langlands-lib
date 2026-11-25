# Idele-class Artin maps under field isomorphisms

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinBaseEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For finite abelian extensions of number fields, the file passes the norm–restriction square of the global Artin map to idele classes and deduces that the idele-class Artin map is transported along field isomorphisms.

- `globalIdeleClassArtinMonoidHom_norm_restriction`: for number fields K ⊆ M and L ⊆ N in scalar towers, with L/K and N/M abelian, restriction Gal(N/M) → Gal(L/K) composed with the idele-class Artin map of N/M equals the idele-class Artin map of L/K composed with `ideleClassNorm K M`.
- `globalIdeleClassArtinMonoidHom_semilinear`: for ℚ-algebra isomorphisms e : K ≃ M and E : L ≃ N with E compatible with e on K, conjugation by (e, E) (`ClassFieldTheory.semilinearGaloisEquiv`) sends the Artin symbol of an idele class c of K to the Artin symbol of `ideleClassCongr e c`.

The first statement descends the idele version `globalArtinMonoidHom_norm_restriction` to idele classes. The second applies it to the tower K → M given by e, with a private lemma that the norm from K to itself does not change the Artin symbol; no description of the kernel is used.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalArtinBaseEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `a68016ea4d0bfbcdc677959da01e0c042c589a5902187597b9641fdc3d2882c0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
