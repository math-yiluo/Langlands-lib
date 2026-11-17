# Global formal maps as rational sections on arbitrary opens

This internal construction uses the same commutative O, O-algebra R,
O-algebra field F and finite-coordinate hypotheses as RationalHomSheaf.
R and F share a universe; O may have a different universe.

`Hom.algebraMapLinear_mapStructural` identifies coherent restriction of a
map extended from R with its direct structural extension to the target
algebra. Its proof computes the actual coordinate power series and uses
commutation with the structural R-map. Tensor induction proves the analogous
compatibility for rational Hom.

`RationalSection.ofGlobalOn U` extends a global rational tensor along the
actual map from R to the structure ring on U and applies the genuine
sheafification unit. It is F-linear and agrees with the existing ofGlobal
on the whole space. The structural comparison proves compatibility with
every open restriction. Tensor base change and the section-composition
agreement law prove that it preserves composition and identities.

`RationalSection.ofHom f U` sends the actual integral structural extension
of f into the rational sheaf. It agrees with ofGlobalOn applied to the
rational tensor of f. The preceding restriction and composition identities
therefore give restriction, composition and identity compatibility for
these integral images. `comp_ofIntegral` also identifies composition of
two integral maps already defined over the actual section algebra.

An actual global isogeny supplies the local scalar-isogeny condition on
any open: its structural extension remains an isogeny by the existing
base-change theorem and gives a witness with exponent zero. In particular
each actual identity section satisfies that condition. These results are
internal consequences of the existing definitions and their implemented
calculus. They assert neither general composition closure of isogenies
nor the existence of inverses for arbitrary local quasi-isogenies.
