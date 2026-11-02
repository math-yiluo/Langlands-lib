# Hausdorffness and local compactness of actual affine scheme points

Author: Worker 105.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1, second paragraph and proof, printed
page 2. Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module supplies proposition-valued statements, not proofs.

R is an arbitrary commutative coefficient ring and S is a commutative
R-algebra with a specified topology. Both rings and the schemes have a
common arbitrary universe. The points are the actual relative morphisms
from Spec S to X over Spec R, with the published global-section evaluation
topology.

`AffineSchemeHausdorffProperty` states that if S is Hausdorff, then the
S-valued point space of every affine scheme over Spec R is Hausdorff.
This extends the source's finite-type assertion: the actual point
homeomorphism identifies these points with algebra maps into S, and
evaluation embeds the latter into the Hausdorff product indexed by the
coordinate ring. Finite generation and continuity of ring operations are
unnecessary for this conclusion.

`AffineSchemeLocalCompactnessProperty` separately assumes that S is a
Hausdorff locally compact topological ring. It states local compactness
of actual S-valued points for affine X locally of finite type over Spec R.
In this affine setting local finite type is finite type, as proved by the
published global-section finite-type comparison and quasi-compactness
of affine structure morphisms. The finite-type coordinate algebra has
a presentation by finitely many generators; its point space is a
closed subspace of a finite power of S, giving the asserted conclusion.

`AffineSchemeTopologicalProperties` combines these conclusions without
moving the stronger hypotheses to the Hausdorff branch. The relative
formulation is derived: setting S = R with the canonical self-algebra
recovers Conrad's statements, while fixed coefficients in S allow an
arbitrary coefficient ring without a topology or a continuity hypothesis
on its structure map. The closed-immersion mapping statements are separate.
No locality, finite presentation or additional scheme separation
hypothesis is imposed. Nonaffine gluing and later sections remain
obligations of the parent task.
