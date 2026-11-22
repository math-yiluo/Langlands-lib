# Open nonempty regions of regular Eisenstein parameters

The regularity condition in `AdelicEisensteinConvergenceStatement` cuts out
an open nonempty region in each complex linear chart, for every real
threshold. The root list is finite. In a chart each inequality is the
strict lower bound of a real linear functional on a finite-dimensional
normed space, so their intersection is open.

For nonemptiness, use the defining cocharacter in the given split
component. Every root in the regularity condition has positive integral
pairing with that cocharacter. The Weyl-induced form is nondegenerate,
so it identifies real split-component characters with their duals.
Choose the character corresponding to evaluation on the cocharacter
scaled by `max R 0 + 1`. This gives every required pairing larger than
the threshold.

Restriction of rational characters from the parabolic to its Levi is
bijective. Restriction to the split component is surjective after
rationalization, so the real scalar extension of the composite is
surjective. The real part of the complex parameter is likewise
surjective by the real-to-complex inclusion on the scalar factor. This
lifts the chosen real character to a complex parameter of the
parabolic. An inverse chart gives a point in the coordinate region.

These facts verify the regular parameter regions used for analytic
uniqueness in the number field setting of Bernstein–Lapid §2.2.
