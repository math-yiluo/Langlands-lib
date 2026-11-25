# Twisting by a one-dimensional module and the coprime case

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Twist.lean`, namespace `Langlands.ProfiniteCohomology`.

Let `P` be an open normal subgroup of `G` acting trivially on a one-dimensional `k`-module `T` and
on a finite `k`-module `M` (`k` a field), with `[G:P]` invertible in `k`. Then
`Hⁿ(G, M) ≅ (Hⁿ(P, T) ⊗ Hom(T, M))^{G/P}` (`coprimeTwistEquiv`). With `T = μ_l` this expresses the
cohomology of `G` through the Kummer cohomology of `P` and the Galois action of `G/P` on it, and the
dimension count of the regular representation gives the coprime case of the Euler characteristic.
The file also transports cohomology along additive isomorphisms of modules over different
coefficient rings and identifies `l`-torsion `ℤ`-modules with `ℤ/l`-modules.

- `finrank_invariants_tprod_comp_mulEquiv`: pulling back the first factor of a tensor product along an
  isomorphism `Γ₁ ≃* Γ₂` and pushing the second forward does not change the dimension of the
  invariants.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.finrank_invariants_tprod_comp_mulEquiv.{u_1, u_2, u_3, u_4, u_5} {k : Type u_1}
  {Γ₁ : Type u_2} {Γ₂ : Type u_3} {X : Type u_4} {N : Type u_5} [Field k] [Group Γ₁] [Group Γ₂] [AddCommGroup X]
  [_root_.Module k X] [AddCommGroup N] [_root_.Module k N] (ρ : Representation k Γ₂ X) (σ : Representation k Γ₁ N)
  (e : Γ₁ ≃* Γ₂) :
  Module.finrank k ↥(Representation.tprod (MonoidHom.comp ρ e.toMonoidHom) σ).invariants =
    Module.finrank k ↥(ρ.tprod (MonoidHom.comp σ e.symm.toMonoidHom)).invariants
```

## Declarations

- `cochainsAddEquiv`, `cochainsAbIso`, `homologyAbIsoOfAbIso`,
  `cohomologyAddEquivOfEquiv e hρ n : Hⁿ(A) ≃+ Hⁿ(A')` for an additive equivariant `e : A ≃+ A'`,
  with compatibilities (`…_mapAlong`, `…_cohomologyRes`, `…_cohomologyMap`, `…_cohomologyConj`).
- `zmodRepOfTorsion l A hA` (an `l`-torsion module as a `ℤ/l`-module),
  `zmodRepOfTorsionEquiv`, `isSmoothRep_zmodRepOfTorsion`, `cohomologyZModEquiv`.
- `cochainsMap_smul`, `cohomologyMap_smul`; `tensorRightMor`, `tensorFormMor`, `twistMap`,
  `twistResMap`, `twistInv`, `twistEquiv`, `twistResEquiv` and their compatibility with
  conjugation (`cohomologyConj_twistResEquiv`, `twistResEquiv_cohomologyConjRep`).
- `quotientRep`, `twistInvariantsEquiv`; the regular representation: `regularTensorEquiv`,
  `invariantsLeftRegularTensorEquiv`, `finrank_invariants_leftRegular_tprod`.
- `homRep T M`, `evalMor`, `evalInv`, `isSmoothRep_homRep`, `bijective_nsmul_of_ne_zero`.
- `coprimeTwistEquiv P T M hT hM hTr hP n`, `finrank_cohomology_eq_finrank_invariants`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Scalars.lean`, `TwistDefs.lean`,
`CohomologyMapTensorRightMorCompCohomologyConj.lean`, `CoprimeRegular.lean` and `CoprimeTwist.lean`.
Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

`finrank_invariants_tprod_comp_mulEquiv` is ported from
`src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/GaloisCohomologyRatios/FiniteCohomologyRootsZMod.lean`
(source name `finrank_tprod_comp_eq`).

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
