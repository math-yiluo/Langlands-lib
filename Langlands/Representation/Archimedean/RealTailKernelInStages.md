# Tail-kernel compatibility in surrounding real blocks

This internal construction transports the published three-coordinate tail-kernel argument to actual ambient standard modules. It is supporting work for exchanging two real induction blocks. Its provenance is the Library's compact slices, Frobenius coefficient identity and uniqueness, and the proved character-induced kernel step. No external literature assertion is formalized here.

`frob_slice` states that an ambient Frobenius map commutes with a compact slice when its local and ambient data have the same multiplier, parity and sign. The middle source and target lists have rank `r`; the slice starts at `a=realRank pre` with `a+r≤n`. The ambient operator acts at position `a+p`, and the local operator acts at `p`. Both are the actual maps on compact-finite standard-module functions. The proof compares local block Fourier coefficients on the compact group, uses the slice coefficient formula, and uses uniqueness in the local target standard module.

`eq_zero_of_slices` detects the zero ambient vector from all compact slices. Evaluation at the local identity recovers the original vector at every ambient compact point, and principal-series compact restriction determines the function. This uses no ambient total-rank hypothesis beyond the room required for the slice.

For a character `c` and complex character datum `d` with `L=|d.weight|>0`, choose the internal parity `sb`. In the notation of `RealCharacterInducedPushforward`, write `b=chiB d sb`, `a=chiA d sb` and `d'=dP d sb`. The local lists are

- `Z=[b,a,c]`, `Y=[b,c,a]`, `X=[c,b,a]`;
- `W=[induced d',c]`, `V=[c,induced d']`.

All local lists have rank three. Prepend any list `pre` and append any list `post`, with total ambient rank `n`. Let `Q2:Z→Y` and `Q1:Y→X` be ambient Frobenius swaps, with the prescribed parity and symmetry and recurrence parameters `a.exponent-c.exponent+1` and `b.exponent-c.exponent+1`. Let `T:Z→W` and `D:X→V` be the actual tail Frobenius maps on the ascending pair, with tail multiplier at weight `L`.

`kernel_step` proves that `T z=0` implies `D(Q1(Q2 z))=0`, preserving all surrounding block constraints. The proof slices the four actual ambient maps, uses `frob_slice` to identify them with the published local maps, applies `RealCharacterInducedPushforward.kernel_step`, and detects zero from all compact slices. Its local landing premise is discharged by `RealSwapLandingIntegral.inducedFirst` and the proved mirror theorem.

There is no genericity, exponent-order, or nonvanishing hypothesis. The multiplier data and their two recurrences remain explicit inputs. The result gives tail-kernel compatibility; it does not assert surjectivity of the swaps, identify heavier images, or prove the two-induced-block filtration.

`Langlands.Archimedean.RealTailKernelInStagesStatement` packages this kernel-step conclusion for all ambient ranks, surrounding lists, character and induction data, internal parities, and four valid Frobenius map data with the specified two recurrences. The theorem `realTailKernelInStages` proves that proposition by `kernel_step`. Both the positive absolute-weight premise and the ambient total-rank equality are retained.
