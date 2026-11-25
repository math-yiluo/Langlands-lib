# Descent of closed loci along fpqc covers

Let \(E\) be a sieve on a scheme \(Y\) that is closed for the fpqc
topology. Suppose that on each arrow of some fpqc covering sieve, the
pullback of \(E\) is represented by a closed immersion. Then a closed
immersion into \(Y\) represents \(E\), with a factorization equivalence
on every scheme over \(Y\).

Over an affine base an fpqc covering sieve has a finite flat affine
refinement. The Library's affine fpqc closed-locus descent constructs
the defining ideal on that base and proves the factorization equivalence.
The general case uses this construction on the affine opens of \(Y\).
The sieve condition is local on their inverse images by its fpqc closure,
so the Library's closed-locus gluing theorem gives the global closed
immersion.

This is the closed-sieve formulation of the effective descent and
reflection of closed immersions from the Stacks Project, *Descent*,
Lemmas 35.37.2 and 35.23.21 (Tags 03I0 and 02L6). The source is the
registered chapter PDF `stacks-descent-ed88ff78-2026`, pages 89 and 58.
A closed sieve gives compatibility of the local closed representatives
on overlaps by their common factorization conditions. The implemented
proof descends these conditions directly by ideals and affine gluing.
