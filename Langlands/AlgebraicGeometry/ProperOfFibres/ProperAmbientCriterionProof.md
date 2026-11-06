# Proof of the generic proper-ambient criterion

Module `Langlands.AlgebraicGeometry.ProperOfFibres.ProperAmbientCriterionProof`, namespace
`Langlands.GroupScheme.RelativeParabolicQuotient`.

## Statement proved

`properAmbientCriterion_holds : ProperAmbientCriterion.{u}`, where
`Langlands.GroupScheme.RelativeParabolicQuotient.ProperAmbientCriterion` is the published
proposition of module `Langlands.GroupScheme.RelativeParabolicQuotientAssembly`, imported
unchanged. It says: for every base scheme `S : Scheme.{u}`, objects `X Y : Over S` and a
morphism `j : X ⟶ Y`, if `X.hom` is smooth, separated and quasi-compact, `Y.hom` is proper
and locally of finite presentation, `j.left` is a monomorphism, and for every field
`k : Type u` and every morphism `f : Spec k ⟶ S` the pullback `((Over.pullback f).obj X).hom`
is proper and its total space `((Over.pullback f).obj X).left` is connected, then `X.hom` is
proper. No hypothesis is placed on `S`: it may be non-noetherian and nonreduced.

## Proof as implemented

The theorem is the term
`Langlands.AlgebraicGeometry.ProperOfFibres.properAmbientCriterion` of module
`Langlands.AlgebraicGeometry.ProperOfFibres.Criterion`, whose type is literally the body of
`ProperAmbientCriterion`; Lean accepts it after unfolding the definition. That theorem is
the end of the following chain of internal helper modules, each with its own Markdown
companion describing its proof.

1. `LocalZariski` (`isProper_of_isOpenImmersion`): over a noetherian integrally closed local
   domain `B`, a flat open subscheme of a proper `B`-scheme, with only constant global
   functions on the generic fibre and a proper nonempty closed fibre, is proper (Zariski
   connectedness argument).
2. `MonoNormalization` (`isFinite_fromNormalization`): a quasi-compact monomorphism of finite
   type out of an integral scheme, into a scheme whose affine rings are of finite type over
   `ℤ`, has finite relative normalization. With Mathlib's Zariski main theorem this makes
   the monomorphism an open immersion followed by a finite morphism.
3. `NoetherianCore` (`isProper_pullback_snd_of_mono`): over the localization `B` of a normal
   domain `N` of finite type over `ℤ` at a prime, a smooth quasi-compact `N`-scheme that is
   a monomorphic subscheme of a proper `N`-scheme becomes proper over `B` when its generic
   fibre over `B` is proper and geometrically connected and its closed fibre is proper and
   nonempty. By step 2 the relative normalization of the ambient scheme in `X` is finite over
   it, hence proper over `N`, and contains `X` as an open subscheme; step 1, applied after
   base change to `B`, gives the conclusion.
4. `Approximation` (`exists_normal_model`): for an integrally closed domain `V`, a
   factorization `j ≫ g = f` over `Spec V` with `f` smooth and quasi-compact, `g` proper and
   locally of finite presentation and `j` a monomorphism descends to such a factorization
   over a normal subring `N ⊆ V` of finite type over `ℤ`.
5. `ValuationCore` (`isProper_of_isLocalRing`): over an integrally closed local domain `V`,
   the conclusion of step 3 holds without noetherian hypotheses. The model of step 4 is
   localized at the prime under the maximal ideal of `V`; properness of the two fibres
   descends along the field extensions of generic and residue fields, and geometric
   connectedness of the generic fibre descends likewise; step 3 then applies, and
   properness is base-changed back to `V`.
6. `Criterion` (`isProper_of_fibres`, `isProper_hom_of_fibres`, `properAmbientCriterion`):
   universal closedness of `X ⟶ S` is checked by the existence part of the valuative
   criterion. Given a valuation ring `R` and `Spec R ⟶ S`, the base change of the
   situation to `Spec R` satisfies the hypotheses of step 5, using the fibre hypothesis at
   the two field points `Spec K ⟶ S` and `Spec κ(R) ⟶ S`; the resulting properness over
   `Spec R` supplies the lift. Properness follows from separatedness, universal closedness
   and local finite type.

The noetherian hypothesis is used only internally, for the descended model over `N` and its
localization; the proved statement keeps an arbitrary base.

## Provenance

The target proposition is the generic properness input of the conditional relative parabolic
quotient assembly. For geometric context compare Conrad, *Reductive group schemes* (2014),
proof of Theorem 2.3.6(2) (pp. 73–75): there properness of `G/H` is deduced from proper,
geometrically connected fibres by a general fact (a special case of EGA IV₃ 15.7.10, as
Conrad notes), proved by reduction to a noetherian, then complete local, base and idempotent
lifting by the theorem on formal functions for a scheme open in a proper scheme. The
implemented route shares the reduction to a noetherian local base and the use of fibre
connectedness, but differs: it uses the valuative criterion over arbitrary valuation rings,
noetherian approximation over normal finitely generated `ℤ`-subalgebras, the relative
normalization (Zariski's main theorem) to make `X` open in a proper scheme, and a Zariski
connectedness argument instead of formal functions. The Lean proof is described above as
implemented. This theorem does not by itself prove existence of
relative parabolic quotients; the other structural inputs of the assembly are separate.
