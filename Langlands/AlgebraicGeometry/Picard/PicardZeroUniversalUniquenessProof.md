# Uniqueness of universal geometric Picard-zero families

`Langlands.AbelianScheme.picardZeroUniversalUniqueness` proves exactly the
published proposition `PicardZeroUniversalUniquenessStatement.{u}`, imported
from `Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalStatements`.
It retains the arbitrary universe, base scheme, abelian scheme, parameter
schemes and actual rigidified families, and its explicit rigidified pullback
coherence premise. It requires no `PicardZeroPullbackStatement` premise.

For universal families `L` over `P` and `M` over `Q`, the first conjunct of
each universal-property hypothesis places its own class in
`PicardZeroClasses`. Classification of the class of `L` by `M` supplies
`a : P ⟶ Q`; classification of the class of `M` by `L` supplies
`b : Q ⟶ P`. These choices give actual ambient rigidified pullback class
equalities.

The composition law `RigidifiedLineBundle.classifyingMap_comp` identifies
the class of `L` pulled back along `a ≫ b` with its own class, using the
two chosen class equalities. The identity law `classifyingMap_id` gives
the same class for `𝟙 P`. Uniqueness of classification of this particular
Picard-zero class gives `a ≫ b = 𝟙 P`. Interchanging `L` and `M` gives
`b ≫ a = 𝟙 Q`. Both laws use precisely the given coherence premise.
The proof packages these equations as an isomorphism `P ≅ Q` in `Over S`.

`classifyingMap_eq_iff` turns the class equality for `a` into existence of
an actual rigidified isomorphism from the relative pullback of `M` to `L`.
Any other compatible parameter isomorphism has a forward map classifying
that same class. The uniqueness clause used to select `a` identifies the
forward maps, and `Iso.ext` identifies the parameter isomorphisms. The proof
claims uniqueness of the parameter isomorphism, not of the bundle-isomorphism
witness. It proves no existence theorem for a universal family.

This is a derived universal-property proof, using the published restricted
classification interface. The analogous unrestricted categorical argument
appears in `RigidifiedUniversalUniquenessProof`; here uniqueness is applied
only to the two specified Picard-zero classes, so no global preservation
premise is needed. The original mathematical provenance is Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft, registered
as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §1, paragraph (6.2), printed p.88 (PDF p.92), states the unique
parameter-map property of the Poincaré bundle. The point formula on printed
p.95 (PDF p.99) and Corollary (7.22), printed p.106 (PDF p.110), motivate
the geometric Picard-zero predicate inherited from the statement. This
conditional uniqueness result over arbitrary bases is a formal consequence
of the stated universal properties, not a claim that those passages prove
representability over arbitrary bases.
