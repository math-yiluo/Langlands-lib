# Actual face models after arbitrary affine restriction

This internal construction puts chart terms from different affine neighborhoods
inside the same actual direct pullback of the original ambient group.

`AffineParabolicFaceModel` retains a maximal coordinate torus, full fibrewise
root datum, actual parametrized roots, fixed integral presenting weight,
representation of the prescribed parabolic homomorphism, and a canonical
unscaled face chart. It requires neither a chosen base point nor an etale
projection, so it is also usable on arbitrary affine parameter schemes and
empty coefficient spectra.

The stored term functors are required to equal the chart's full-root
presentation. A proved identity also identifies them with the ranges of the
original model inclusion maps. Storing these functors avoids repeated large
dependent conversions when the model is constructed.

An original affine etale face chart restricts along any actual affine base map
to such a model. The construction base changes the actual torus and roots,
transports them through the canonical comparison with the direct pullback of
the original ambient group, and chooses a proved face chart on those data.
The given parabolic homomorphism retains its actual dynamic representation.
Every original term agrees, on every scheme test, with the constructed term
after the specified base change and original ambient comparison. The arbitrary
affine map is treated through its induced coefficient-algebra structure,
transporting the entire dependent assertion to retain its actual pullback.
The recovery proof compares generated root subgroups directly on each test:
base change preserves the original root ranges, their images under the actual
ambient isomorphism are the constructed roots, and the common full datum and
presenting weight give exactly the original unscaled face functional.

Over a nontrivial coefficient ring, two such models presenting the same supplied
relative radical have equal original ambient term ranges. This uses the proved
arbitrary maximal-torus comparison; equality of the parabolic and contracting
functors is derived from their actual prescribed representatives and supplied
radical. No term matching or descent effectivity is supplied as a premise.

Local coordinate and root enumerations have explicit module-specific instance names, so the restriction and finite-cover geometry modules can be combined. Their types, proofs and local scopes are unchanged.

The coefficient base map, ambient comparison, transported torus and roots, and
assembled coefficient model are reducible aliases. This exposes their stored
fields during dependent quotient comparison without changing their values or
mathematical assumptions. The separately chosen coefficient chart remains a
proved construction.
