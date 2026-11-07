# Actual coefficient actions on stable root-valuation apartments

Let `k` and `K` be fields in an arbitrary common universe, with a supplied
`k`-algebra structure on `K`. Supply a commutative group scheme `T`, a group
scheme `G` over `k` with affine structure morphism, and a group-scheme map
`i : T.toGrp ⟶ G`. Write `T_K`, `G_K` and `i_K` for their actual base changes.
Assume the underlying scheme map of `i_K` is a monomorphism. The affine
structure-morphism instance for `G_K` is obtained by pullback.

Supply a function `omega : Kˣ → ℝ` and actual `KPApartmentData i_K omega`,
called `D`. In particular, `D` already supplies a full equipollence class of
root-datum valuations compatible with `omega` on the torus and stable under the
normalizer. Its apartment and its affine structure over the existing reduced
`TranslationSpace i_K` are the existing ones. This module does not establish the
existence of such data or of a coefficient-stable valuation class. No splitness,
reductivity, finiteness or Galois-extension hypothesis is added to the algebraic
construction.

`D.GaloisStable` is the proposition that the actual family action from
`RootFunctionGaloisAction` preserves every member of `D.carrier` under every
`K ≃ₐ[k] K`. For any one supplied point `x` of the same apartment,
`galoisStable_iff_equipollent` proves that stability is equivalent to
equipollence of `x.val` with each of its coefficient conjugates. In the forward
direction both families lie in the given class. Conversely, apply preservation
of equipollence by the actual family action to the relation between `x.val`
and any member of the class, then compose with equipollence of `x.val` and its
conjugate. The characterization of the full class by equipollence proves
membership. This equivalence reduces the stability obligation to a single
member; it does not discharge it for a canonical class.

Given `hD : D.GaloisStable`, `galoisAction` restricts the existing family action
to permutations of `D.Apartment`. The value of each permutation is the actual
transported family, with membership supplied by `hD`. Its inverse uses the
inverse coefficient automorphism. Apartment extensionality reduces its inverse,
identity and multiplication laws to those of the actual family action. In
particular, no abstractly selected permutation of an unrelated carrier is used.

`galoisAction_vadd` proves covariance under translation by every member of the
existing reduced translation space. Quotient induction reduces to a real
cocharacter representative; family translation covariance proves the result.
`galoisAffineAction` consequently packages these same permutations as a group
homomorphism to affine equivalences of the same apartment. Its linear part is
exactly the already constructed `galoisTranslationAction`, as the displayed
linear-part theorem states. Its identity and multiplication laws are inherited
from the restricted permutation action.

`rationalConjugate_mem_filtration_iff` identifies membership in the original
apartment filtration with membership of the actual coefficient conjugate in the
filtration at the transported point and character, at every real depth. This
is the all-depth root-filtration equivalence from `RootFunctionGaloisAction`,
specialized to the actual family underlying an apartment point. The filtration
subgroups, rational points and coefficient map are the existing ones.

The construction is derived internally from the imported actual coefficient
actions and the published full-class and affine structures of `KPApartmentData`.
It uses no new external literature assertion. Preservation of a canonical class,
coefficient compatibility with the normalizer action, a quotient-building action
from these data, a metric, a special point, the original supplied-model fixer
comparison and descent remain separate obligations. The unconditional
`BuildingComparisonStatement` remains open.
