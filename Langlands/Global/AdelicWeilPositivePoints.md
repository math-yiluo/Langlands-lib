# Positive real points under the adelic Weil comparison

`AdelicWeilRestriction.map_imageSubgroup_le` carries the positive points of a central split torus in an affine Weil restriction into the positive subgroup of any upper-field split component.

The splitting presents the lower torus by the functor of unit-valued characters of a free abelian group. `AffineWeil.counitTrans` gives a central homomorphism from the corresponding upper split torus. Its image factors through the upper split component by `IsSplitComponent.exists_comp_eq_of_isCentral`. The two positive points with the same real coordinates correspond under the canonical adele tensor map by `AdeleGalois.adeleInclusion_positiveReal` and naturality of the lattice functor. A homomorphism of tori preserves the intrinsic positive subgroup, which gives the claimed inclusion.

The proof uses the Weil point comparison of Springer, *Reduction theory over global fields*, §1.4, pp. 208–209, `springer-1994-reduction-global-fields`, SHA-256 `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
