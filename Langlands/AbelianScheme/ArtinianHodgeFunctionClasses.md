# Cohomology classes of the function cochains

The function cochain comparison takes cocycles and coboundaries to those
in the ordered affine Čech resolution. `functionCocycleClass` composes
this comparison with the canonical class of that resolution. Its zero
classes are precisely the function coboundaries, and in degree one the
map agrees with the function-end equivalence on quotient classes.

For a compatible assignment of charts, `unitCochainMap_eq_pull` identifies
the pullback of the structure module with the actual pullback of section
rings on intersections. The naturality of the canonical comparison
therefore identifies these classes with pullback in actual cohomology.
