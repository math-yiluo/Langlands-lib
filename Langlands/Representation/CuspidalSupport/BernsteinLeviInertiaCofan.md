# Actual induced Levi inertia cofans for Bernstein decomposition

This derived internal construction implements the inertia-component step in
Renard VI.7.2, printed pp.181–184 / PDF pp.187–190 of the registered 2026
edition. It retains the whole cuspidal inertia product decomposition and
arbitrary-inertia Jacquet exclusion as explicit inputs. It proves no
unconditional Bernstein decomposition.

`bernsteinLeviTorus` is the actual induced torus map into an actual standard
Levi scheme. `bernsteinLeviStandardFamily` uses published connected
reductivity, maximal split torus, intrinsic root and standard-family
comparison theorems to equip it with its intrinsic standard family.

`BernsteinLabelledCofanPresentation` records actual smooth summands and
actual legs at a fixed saturated-carrier vertex, their coproduct universal
property, actual Bernstein inertial labels, and the original saturated
block property for each summand. Its index universe is allowed to exceed
the carrier universe; this is a supplied cofan, without a global coproduct
existence assertion at that index size.

`bernsteinInducedCuspidalCofan` pulls a literal cuspidal Levi object back
to the actual Levi scheme's rational points. The intrinsic cuspidal
inertia decomposition gives its component cofan. Cuspidality passes to
all subquotients, so its noncuspidal component is zero: that component
embeds into the cuspidal object by its monic coproduct leg. Deleting this
zero component retains the universal property.

The actual pullback and normalized induction functors preserve that supplied
cofan using carrier-sized coproduct preservation and the published size
reduction for its nonzero summands. Each cuspidal inertia class has an
actual irreducible cuspidal representative. Intrinsic/literal cuspidality
transport packages it into an original Bernstein cuspidal datum. Its
component belongs to that representative's original same-Levi inertia
block by equality of the actual inertia quotient. The supplied geometric
exclusion and the unconditional simultaneous Jacquet/induction support
presentation put its actual induced component in the corresponding
Bernstein block. The canonical cancellation isomorphism returns the cofan
to the original literal induced object.
