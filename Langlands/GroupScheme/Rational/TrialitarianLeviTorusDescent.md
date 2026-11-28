# Descent of a maximal torus inside the common Levi

`exists_a2_maximalTorus_descent` works for a connected reductive group
over an infinite field with a split maximal torus over a cyclic cubic
extension. It assumes the split-torus Galois comparison and that the
absolute datum has two coroots with `A₂` pairings whose six-coroot
list contains all coroots. It gives a maximal torus over the ground
field whose base change is rationally conjugate to the given torus.

The three integral `A₂` line cocharacters sum to zero, have a unique
negative value for each root, and have regular first difference. Each
lies in the same Weyl orbit. The cube of a lifted generator fixes the
cubic field, so its star action has cube one. Such a based action
fixes the coroot span in type `A₂`, even when the group has a central
torus. Together with the comparison theorem this gives rational
conjugacy for the two transported parabolics. Cyclic triple descent
produces a group whose base change is the centralizer of the regular
difference up to conjugacy, hence a torus. The maximal torus of that
group over the base becomes the whole centralizer over the extension.
Maximal-torus reflection gives the asserted maximality.

This step obtains the torus in the common Levi by a second
three-parabolic intersection. It provides the prescribed splitting
property in the cyclic maximal-torus construction of Platonov and
Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8,
printed p. 372.
