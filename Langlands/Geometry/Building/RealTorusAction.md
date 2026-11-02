# Actual normalizer and relative Weyl action on real cocharacters

Author: Worker 185.

For an arbitrary field `k : Type u` and an actual commutative group scheme `T` over `Spec k`, this module defines automorphisms of the existing tensor spaces in `RealTorusSpace`. No torus, splitness, finite-rank or characteristic assumption is needed for these constructions.

The shared [integral automorphism module](../../GroupScheme/Torus/CocharacterAction.md)
supplies `cocharacterAut σ`, the integer-linear equivalence `ν ↦ ν ≫ σ.hom`, with inverse given by composition with `σ.inv`. `characterRealAut σ` extends the Library's `characterAut σ`, which is `χ ↦ σ.inv ≫ χ`. `cocharacterRealAut σ` extends `cocharacterAut σ`. Both use Mathlib's `LinearEquiv.baseChange`. Their pure-tensor computation rules are `r ⊗ χ ↦ r ⊗ (σ.inv ≫ χ)` and `r ⊗ ν ↦ r ⊗ (ν ≫ σ.hom)`.

The shared `latticePairing_aut` proves invariance of the integer pairing by associating composition and cancelling `σ.hom ≫ σ.inv`. Tensor induction in both variables, using real bilinearity, proves

`pair T (characterRealAut σ x) (cocharacterRealAut σ v) = pair T x v`.

The identity `eval_aut` specializes this result to `1 ⊗ χ`.

For actual `i : T.toGrp ⟶ G`, the hypothesis `Mono i.hom.hom.left` ensures that the normalizing automorphism is unique. `normalizerAction i` sends `n : normalizerPoints i` to `cocharacterRealAut (normalizingAut i n)` and is a group homomorphism into real linear equivalences. Uniqueness identifies the automorphism at the identity with the identity, and the automorphism at `n * m` with `normalizingAut i m ≪≫ normalizingAut i n`; postcomposition gives the required left action. `normalizerAction_tmul` computes this action on pure tensors.

A point of `centralizerPoints i` has the identity normalizing automorphism, so `normalizerAction_eq_one_of_mem_centralizerPoints` proves that it acts trivially. `relativeWeylRealAction i` is the quotient homomorphism obtained with `QuotientGroup.lift`, on the existing `relativeWeylGroup i = normalizerPoints i ⧸ (centralizerPoints i).subgroupOf (normalizerPoints i)`. Its defining identity `relativeWeylRealAction_mk` recovers `normalizerAction i` on the quotient map. Both homomorphisms supply distributive group action instances on `V T`; `normalizer_smul_def`, `relativeWeyl_smul_def` and `relativeWeyl_mk_smul` identify their scalar-action notation.

The identity

`eval T χ (n • v) = eval T (weylAction i n⁻¹ χ) v`

follows by applying simultaneous evaluation invariance to `weylAction i n⁻¹ χ` and cancelling the two published character automorphisms through the group-homomorphism law. When `G` is affine, `rootEval_normalizer_smul` gives the same identity for every actual `α : relativeRoots i`; the root on the right is the image of `α` under the published action of `n⁻¹`, with its membership supplied by `weylAction_mapsTo_relativeRoots`.

This is an internal scalar-extension construction implementing Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Chapter 6 introduction and §6.1.6–8, PDF pages 226–234 (printed 195–203). The original is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The authors' corrections of 1 November 2024 are registered as `kaletha-prasad-2024-corrections`, SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`; PDF page 32 corrects negative signs to positive signs in the proof of Lemma 6.1.12(1). No version of that lemma about valuations or affine translations is asserted here.

These prospective translation spaces and actions require no valued field or Henselian hypothesis. No affine origin, apartment, equipollence class, root-group valuation, affine Weyl group, Iwahori–Weyl group or building is constructed. The separate derived/adjoint and central directions in the reduced and enlarged building remain outside this unit, which closes no bundle or release gate.
