# Special-fibre kernels of restricted bilinear homomorphisms

Let `A` and `B` be commutative rings, with `B` a finite projective `A`-algebra,
and let `k` be a field with a specified `A`-algebra structure. All types lie in
an arbitrary common universe `u`. Consider bilinear coordinate groups over `B`
with finite vector index types `I` and `J`, cocycles `c` and `d`, and a
compatible linear homomorphism with vector matrix `M : I → J → B` and
central multiplier `t : B`. Compatibility is the original cocycle equation
`BilinearCoordinate.IsCompatible c d M t`; it is an algebraic condition,
not an assumption about kernel geometry.

The actual affine Weil restriction of this homomorphism is a homomorphism
over `A`. The theorem `AffineWeilBilinear.linearKernelFibre_properties` proves
that the scheme-theoretic kernel of its base change along `A → k` is smooth,
connected and unipotent over `k`. Connectedness means `ConnectedSpace` of the
underlying kernel scheme, and unipotence is the existing representation
theoretic `IsUnipotent` predicate. In particular, taking a residue field gives
the kernel of the actual special-fibre map.

The proof constructs and checks the following comparisons.

1. `AffineWeil.mapIso` restricts an actual group-scheme isomorphism, using the
   existing identity and composition laws for `AffineWeil.map`.
2. `fibreCoefficientMap` is the coefficient homomorphism
   `B → k ⊗[A] B`. The isomorphism `restrictionFibreIso` first commutes actual
   affine Weil restriction with base change using `AffineWeil.BaseChange.iso`,
   then restricts `BilinearCoordinate.baseChangeIso`. Its target is the actual
   restriction over `k` of the bilinear coordinate group over `k ⊗[A] B`
   with coefficient images of `c`.
3. `restrictionFibreIso_linearHom` proves the commuting square for the
   original homomorphism. It combines the original bilinear homomorphism's
   coefficient base-change identity with the naturality square for actual
   affine Weil base change. The resulting map has coefficients equal to
   the images of `M` and `t`; its compatibility follows by mapping the
   original compatibility equation.
4. `linearKernelFibreIso` applies `kernelSquareIso` to this square. Thus it
   compares actual pullback kernels, rather than merely their rational points.
5. The algebra `k ⊗[A] B` is finite over the field, so `Module.finBasis`
   supplies a finite basis. The theorem
   `AffineWeilBilinear.linearKernel_properties` then proves the geometric
   triple for the target kernel. Finally
   `smooth_connected_unipotent_of_groupIso` transports it through the
   constructed kernel isomorphism.

No reducedness, separability, perfectness or characteristic restriction is
imposed on the fibre algebra or on `k`. The fibre algebra can contain
nilpotents. The original `B` need not be free over `A`: a basis is used only
after base change to the field. Empty vector index types are allowed, and no
nonvanishing hypothesis is imposed on the coefficients of the homomorphism.

This is a derived supporting calculation for Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Proposition C.5.1, printed
pp.703–704 / PDF pp.734–735, and Lemma C.5.3, printed p.705 / PDF p.736.
C.5.1 assembles the root models by restriction of scalars, and C.5.3 states
the smooth, connected, unipotent kernel conclusion for their special-fibre
depth maps. The general comparison above follows from the existing actual
base-change and restricted bilinear kernel calculations; it is not a separate
assertion quoted from the book. Applying it to every supplied root-depth
model still requires identifying the root models and their integral
transition with the bilinear restriction presentation. This module does not
make that identification or prove the full root-depth statement.
