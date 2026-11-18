# Smoothness and connectedness of anti-affine algebraic field groups

`Langlands.GroupScheme.antiAffineSmoothConnected` proves `AntiAffineSmoothConnectedStatement` with its exact universe parameter and hypotheses. This supporting theorem is included in the full anti-affine quotient existence proof development.

Connectedness is the previously constructed `IsAntiAffine.connectedSpace`, which uses no finiteness or smoothness assumption: the actual global-function ring is a field, and the sheaf product for a nontrivial clopen decomposition would split it as a product of two nonzero rings. The group identity supplies nonemptiness.

Over a perfect field, `ReducedCosetAffine.model` gives an actual affine scheme representing the full reduced-subgroup coset sheaf and an actual smooth surjective projection onto it. `IsAntiAffine.smooth_of_affine_smooth_surjection` uses constancy of every affine-valued scheme map from the anti-affine group. The projection is constant at the identity value. Epimorphy makes the affine target isomorphic to the base field spectrum, so smoothness of the projection proves smoothness over the field.

For an arbitrary field, first base change the actual group to its algebraic closure. Quasi-compactness and the published field separatedness theorem give the qcqs hypotheses for `IsAntiAffine.baseChange`, which preserves anti-affineness. Local finite type is preserved by this base change. Apply the perfect-field result to obtain smoothness over the algebraic closure, and descend it through the actual faithfully flat quasi-compact map of field spectra using Mathlib's `Smooth` fpqc descent instance. The exact statement is the pair of this result and unconditional connectedness.

The proof is internally derived from the imported constructions and published base-change and descent theorems. It uses no extra affine, perfect-field, or algebraically closed field premise in its arbitrary-field conclusion, and it proves no commutativity assertion.
