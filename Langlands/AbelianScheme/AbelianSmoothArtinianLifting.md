# Smooth proper pointed lifts of abelian schemes across elementary Artinian extensions

Module `Langlands.AbelianScheme.AbelianSmoothArtinianLifting`.

`abelianSmoothArtinianLifting` proves `AbelianSmoothArtinianLiftingStatement`. Let
`φ : R' →+* R` be a surjection of local Artinian rings with `R'` a `ℚ`-algebra and
`maximalIdeal R' * ker φ = 0`. Write `t := Spec.map (CommRingCat.ofHom φ)`.
For an abelian scheme `B` over `Spec R`, the theorem produces a smooth proper
`p : X ⟶ Spec R'`, a section `s` of `p`, and an isomorphism
`e₀ : B.X.left ≅ pullback p t` over `Spec R`. The section lifts the identity of
`B`, with

```text
η[B.X].left ≫ e₀.hom ≫ pullback.fst p t = t ≫ s
```

## Proof

1. `Setting.exists` chooses a coefficient-field section of the residue map of `R'`
   and factors that residue map through `R`. The section exists by formal
   smoothness of the characteristic-zero residue field `k` over `ℤ` and nilpotence of the
   maximal ideal of `R'`. It defines the constant abelian scheme
   `C = A₀ ×_k Spec R'` from the special fibre `A₀` of `B`.
2. `Setting.Charts.exists` identifies a finite affine cover of `B` with reductions
   of affine opens in `C`.
3. `Charts.nonempty_liftedTransitions_of_elementary` lifts the overlap maps to
   `C`. Comparing a single Čech obstruction on the fibre square along the product
   cover and its transport by `(x, y) ↦ (x + y, y)` gives primitivity in each
   coordinate. The primitive-class criterion gives a coboundary on the original
   residue cover. Correcting the lifts gives the cocycle and diagonal identities
   with the prescribed reductions over `Spec R`.
4. `LiftedTransitions.exists_smoothLift` glues the thicker charts. The thinner
   charts identify `B` with the actual pullback `pullback p t`, with
   `e₀.hom ≫ pullback.snd p t = B.X.hom`. The glued scheme is smooth by its charts
   and proper by reflection from `B` along the surjective closed immersion `t`.
   Smoothness lifts the unit section across the nilpotent kernel and gives the
   displayed section equation.

## Provenance

The obstruction calculation follows Kai-Wen Lan, *Arithmetic compactifications
of PEL-type Shimura varieties*, Harvard thesis revised 14 March 2021,
Proposition 2.2.4.1 (printed pp. 152–154, PDF pp. 180–182), registered as
`lan-2008-pel-thesis-revision-2021`. The correction and gluing follow SGA 1,
Exposé III, §6 (recomposed edition, printed pp. 64–66, PDF pp. 80–82), registered
as `sga1-arxiv-math-0206203v2`.
