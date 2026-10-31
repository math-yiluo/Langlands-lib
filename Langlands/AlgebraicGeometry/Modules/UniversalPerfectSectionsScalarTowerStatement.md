# Universal perfect representatives under a scalar tower

Author: Worker 137.

`UniversalPerfectSectionsScalarTowerStatement.{u}` asserts that, for every
actual module `M` on a scheme `X` over `Spec R`, every fixed complex `K`
satisfying `IsUniversalPerfectSectionsRepresentative f M K`, and every ring
map `φ : R ⟶ S`, the specific complex obtained by ordinary scalar extension
of `K` along `φ` is a universal perfect representative of the usual
pullback of `M` over `Spec S`.

Unfolding the conclusion requires strict perfection of that extended
complex, its actual derived-sections comparison over `S`, and the
comparisons after every further map `ψ : S ⟶ T`. These latter comparisons
use two successive ordinary scalar extensions of the given `K` and the
actual iterated scheme and module pullbacks. All ring, scheme and module
carrier universes remain arbitrary `u`.

This is an internal transport statement. Its provenance is preservation
of strict perfection by ordinary scalar extension, the composition
isomorphism for that extension, the canonical isomorphism between
iterated and direct scheme pullbacks, module pullback composition, and
invariance of actual derived sections under a scheme isomorphism. These
give the comparison for `ψ` from the assumed comparison for `φ ≫ ψ`.
The original-base comparison over `S` is the assumed scalar comparison
for `φ`.

The proposition assumes a universal representative and asserts no
existence of one for a smooth proper family. It imposes no smoothness,
properness, flatness or quasi-coherence premise beyond the stated
representative predicate. The comparisons are objectwise; no
compatibility or naturality of the assumed witnesses is asserted.
